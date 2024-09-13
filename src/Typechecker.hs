{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
module Typechecker where

import Parser

import Control.Lens
import Data.Bool (bool)
import Data.Function (on)
import Control.Monad.Trans
import Control.Monad.State
import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as H

maybeToEither :: a -> Maybe b -> Either a b
maybeToEither _ (Just b) = Right b
maybeToEither a Nothing  = Left a

update :: MonadState a m => (a -> a) -> m a
update f = modify f >> get
data MonoType =
    Variable { constraints :: S.HashSet String , identifier :: String   }
  | Constant { constraints :: S.HashSet String , constType  :: String   }
  | Function { takesType   :: MonoType         , retsType   :: MonoType }
  | Bottom -- for convenience
  deriving (Eq)

data PolyType = Scheme { bounds :: H.HashMap String (S.HashSet String) , monoBounded :: MonoType }

data DeBrujin a = BIndex { bindex :: Int, tyAnot :: a } | BFunc { bfunc :: String, tfAnot :: a }

data TheContext = TheContext { _context  :: H.HashMap String PolyType , _typeGen :: MonoType, _varIndex :: H.HashMap String Int, _indexGen :: Int }
makeLenses ''TheContext

newtype Subs = Subs    { _typeMap :: H.HashMap String MonoType }

empty :: Subs
empty = Subs H.empty

genFrom :: MonoType -> MonoType
genFrom (Variable c (t:ns)) = Variable c $ (t :) $ show $ (read :: String -> Int) ns + 1
genFrom _                 = undefined

singleMap :: MonoType -> MonoType -> Subs
singleMap (Variable c n) (Variable c' n') = Subs . H.singleton n $ Variable (c `S.union` c') n'
singleMap (Variable _ n) t                = Subs . H.singleton n $ t
singleMap _              _                = undefined

typeMap :: Subs -> MonoType -> MonoType
typeMap s t@(Variable _ v) = H.findWithDefault t v (_typeMap s)
typeMap s (Function tT rT) = let m = typeMap s tT
                                 m' = typeMap s rT
                             in Function m m'
typeMap _ t                = t

polyMap :: Subs -> PolyType -> PolyType
polyMap (Subs m) (Scheme bounds' monoBounded') = Scheme bounds' $ typeMap (Subs $ m `H.difference` bounds') monoBounded'

compose :: Subs -> Subs -> Subs
compose (Subs m1) (Subs m2) = Subs $ H.foldMapWithKey (\t t' m -> H.alter (\case {
      Nothing  -> Just t';
      Just t''@(Variable _ v'') -> Just $ H.findWithDefault t'' v'' m;
      Just t'' -> Just t''
    }) t m) m1 m2

newtype TypeError = TypeError { msg :: String }

instance Show TypeError where
  show (TypeError e) = e
throwTypeErr :: MonadTrans t => String -> t (Either TypeError) a
throwTypeErr msg' = lift $ Left $ TypeError msg'


freeInType :: PolyType -> H.HashMap String (S.HashSet String)
freeInType (Scheme bounds' monoBounded') = freeInType' monoBounded' `H.difference` bounds'
  where
    freeInType' :: MonoType -> H.HashMap String (S.HashSet String)
    freeInType' Bottom = undefined
    freeInType' (Constant {}) = H.empty
    freeInType' (Variable c n) = H.singleton n c
    freeInType' (Function m1 m2) = freeInType' m1 `H.union` freeInType' m2

freeInCtx :: TheContext -> H.HashMap String (S.HashSet String)
freeInCtx (TheContext ctx _ _ _) = foldl (\s p -> s `H.union` freeInType p) H.empty ctx

unify :: MonoType -> MonoType -> Either TypeError Subs
--
unify v@(Variable c s)    v'@(Variable c' s')
  | s == s'             = Right $ Subs H.empty
  | c `S.isSubsetOf` c' = Right $ singleMap v v'
  | otherwise           = Right $ singleMap v' v
unify v@(Variable c _) t'@(Constant c' _)
  | c `S.isSubsetOf` c' = Right $ singleMap v t'
  | otherwise           = Left $ TypeError "Could not instantiate variable"
unify v@(Variable _ _)    t'
  | v `isIn` t' = Left $ TypeError "Infinite type"
  | otherwise   = Right $ singleMap v t'
  where isIn v' (Function rT tT) = v' `isIn` rT || v' `isIn` tT
        isIn v' v''@(Variable _ _) = v' == v''
        isIn _  _                = False
unify t                 v'@(Variable _ _)  = unify v' t
unify (Constant _ i)    (Constant _ i')    = bool (Left $ TypeError "Type mismatch") (Right empty) (i == i')
unify (Function tT rT)  (Function tT' rT') = unify tT tT' >>= \u -> compose u <$> (unify `on` typeMap u) rT rT'
unify _                 _                  = Left $ TypeError "Type mismatch"

algoW :: LambdaExpressionIndexedBy SIdent NoType -> StateT TheContext (Either TypeError) (Subs, (LambdaExpressionIndexedBy DeBrujin MonoType, MonoType))

algoW (Cnst c  t) = return (empty, (Cnst c t, case t of { Nat -> Constant (S.singleton "Num") "Nat" }))

algoW (Var  (IdenNT n)) = do
  ctx <- get
  (Scheme bounds' mono) <- lift . maybeToEither (TypeError "Could not find variable") . H.lookup n $ _context ctx
  instMap <- H.foldlWithKey instanceMap (return $ typeMap empty) bounds'
  let insdMono = instMap mono
  return (empty, (Var $ indexingLam insdMono ctx n, insdMono))
  where
    instanceMap :: StateT TheContext (Either TypeError) (MonoType -> MonoType) -> String -> S.HashSet String -> StateT TheContext (Either TypeError) (MonoType -> MonoType)
    -- for some reason Haskell cannot infer this very easy to read, and easy to understand type
    instanceMap mmap k c = do
      map' <- mmap
      nBeta <- identifier . _typeGen <$> update (typeGen `over` genFrom)
      return $ (. map') $ typeMap $ singleMap (Variable c k) $ Variable c nBeta
    indexingLam t ctx a
      = case H.lookup a (_varIndex ctx) of
        Just i  -> BIndex i t
        Nothing -> BFunc a t
      

algoW (Application e1 e2) = do
  (s1, (e1', t1)) <- algoW e1
  modify $ context `over` H.map (polyMap s1)
  (s2, (e2', t2)) <- algoW e2
  beta <- _typeGen <$> update (typeGen `over` genFrom)
  s3 <- lift $ unify (typeMap s2 t1) (Function t2 beta)
  return (s3 `compose` s2 `compose` s1, (Application e1' e2', typeMap s3 beta))

algoW (Abstraction (IdenNT x) e) = do
  beta <- _typeGen <$> update (typeGen `over` genFrom)
  ind <- _indexGen <$> update (indexGen `over` (+1))
  modify $ context `over` H.insert x (Scheme H.empty beta)
  modify $ varIndex `over` H.insert x ind
  (s1, (e', t1)) <- algoW e
  let tBeta = typeMap s1 beta
  return (s1, (Abstraction (BIndex ind tBeta) e', Function tBeta t1))

algoW (LocalBind (IdenNT n) e1 e2) = do
  (s1, (e1', t1)) <- algoW e1
  ctx <- update (context `over` H.map (polyMap s1))
  ind <- _indexGen <$> update (indexGen `over` (+1))
  modify $ context `over` H.insert n (Scheme (freeInCtx ctx) t1)
  modify $ varIndex `over` H.insert n ind
  (s2, (e2', t2)) <- algoW e2
  return (s2 `compose` s1, (LocalBind (BIndex ind t1) e1' e2', t2))

algoW (Bind (IdenNT n) e) = do
  (s1, (e', t1)) <- algoW e
  ctx <- update (context `over` H.map (polyMap s1))
  ind <- _indexGen <$> update (indexGen `over` (+1))
  modify $ context `over` H.insert n (Scheme (freeInCtx ctx) t1)
  return (s1, (Bind (BIndex ind t1) e', Bottom))

typecheck :: LambdaExpressionIndexedBy SIdent NoType -> Either TypeError (LambdaExpressionIndexedBy DeBrujin MonoType)
typecheck = fmap (fst . snd) . flip evalStateT prelude . algoW
  where
    s = Variable (S.singleton "Num") "s"
    forAll vs = H.fromList $ map (\(Variable c n) -> (n, c)) vs
    prelude = TheContext {
        _context  = H.fromList [
          ("plus", Scheme (forAll [s]) $ Function s (Function s s))
        ],
        _typeGen  = Variable S.empty "t0",
        _varIndex = H.empty,
        _indexGen = -1
    }
