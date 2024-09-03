{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Main where

import System.IO
import Text.Parsec
import Data.Bool (bool)
import Data.Function (on)
import Control.Lens
import Control.Monad.State
import qualified Data.HashMap.Strict as H
import qualified Data.HashSet as S

maybeToEither :: a -> Maybe b -> Either a b
maybeToEither _ (Just b) = Right b
maybeToEither a Nothing  = Left a

update :: MonadState a m => (a -> a) -> m a
update f = modify f >> get

data CnstType = Nat

data LambdaExpression =
    Cnst        { cnst   :: String           , cnstT :: CnstType         }
  | Var         { name   :: String           }
  | Application { func   :: LambdaExpression , arg   :: LambdaExpression }
  | Abstraction { var    :: String           , ret   :: LambdaExpression }
  | LocalBind   { lName  :: String           , lExpr :: LambdaExpression , inExpr :: LambdaExpression}
  | Bind        { bName  :: String           , bExpr :: LambdaExpression }

data MonoType =
    Variable { constraints :: S.HashSet String , identifier :: String   }
  | Constant { constraints :: S.HashSet String , constType  :: String   }
  | Function { takesType   :: MonoType         , retsType   :: MonoType }
  | Bottom -- for convenience
  deriving (Eq)

data PolyType = Scheme { bounds :: H.HashMap String (S.HashSet String) , monoBounded :: MonoType }

data TheContext = TheContext { _context  :: H.HashMap String PolyType , _typeGen :: MonoType }
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

throwTypeErr :: MonadTrans t => String -> t (Either TypeError) a
throwTypeErr msg' = lift $ Left $ TypeError msg'

instance Show LambdaExpression where
  show (Cnst c _) = c
  show (Var n)    = n
  show (Application f a) = show f ++ ' ' : show a
  show (Abstraction v r) = 'λ' : v ++ ". " ++ show r
  show (LocalBind b v e) = "let " ++ b ++ " = " ++ show v ++ " in " ++ show e
  show (Bind b e) = "let " ++ b ++ " := " ++ show e

instance Show MonoType where
  show Bottom = ""
  show (Constant _ c)   = c
  show (Variable c n)   = '(' : n ++ " in " ++ show c ++ ")"
  show (Function t1 t2) = '(' : show t1 ++ " -> " ++ show t2 ++ ")"

instance Show TypeError where
  show (TypeError e) = e

instance Show Subs where
  show (Subs m) = '{' : H.foldlWithKey (\s k t -> s ++ " " ++ k ++ " |-> "++ show t) "" m ++ " }"

nat :: Parsec String () LambdaExpression
nat = (`Cnst` Nat) <$> many1 digit

constant :: Parsec String () LambdaExpression
constant = nat

variable :: Parsec String () LambdaExpression
variable = fmap Var $ many1 $ lower <|> oneOf "αβγδεζηθικμνξοπρσςτυφχψω"

application :: Parsec String () LambdaExpression
application = between (char '(') (char ')') $ Application <$> expression <*> (spaces >> expression)

abstraction :: Parsec String () LambdaExpression
abstraction = do
  _ <- oneOf "\\λ"
  spaces
  vararg <- name <$> variable
  spaces
  _ <- char '.'
  spaces
  Abstraction vararg <$> expression

binds :: Parsec String () LambdaExpression
binds = do
  _ <- string "let"
  spaces
  ctarg <- name <$> variable
  spaces
  do {
    _ <- string ":=";
      spaces;
      Bind ctarg <$> expression
  } <|> do {
    _ <- string "=";
    spaces;
    val <- expression;
    spaces;
    _ <- string "in";
    spaces;
    LocalBind ctarg val <$> expression
  }

expression :: Parsec String () LambdaExpression
expression = application <|> abstraction <|> binds <|> variable <|> constant

freeInType :: PolyType -> H.HashMap String (S.HashSet String)
freeInType (Scheme bounds' monoBounded') = freeInType' monoBounded' `H.difference` bounds'
  where
    freeInType' :: MonoType -> H.HashMap String (S.HashSet String)
    freeInType' Bottom = undefined
    freeInType' (Constant {}) = H.empty
    freeInType' (Variable c n) = H.singleton n c
    freeInType' (Function m1 m2) = freeInType' m1 `H.union` freeInType' m2

freeInCtx :: TheContext -> H.HashMap String (S.HashSet String)
freeInCtx (TheContext ctx _) = foldl (\s p -> s `H.union` freeInType p) H.empty ctx

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

algoW :: LambdaExpression -> StateT TheContext (Either TypeError) (Subs, MonoType)

algoW (Cnst _  t) = return (empty, case t of { Nat -> Constant (S.singleton "Num") "Nat" })

algoW (Var  n   ) = do
  ctx <- get
  (Scheme bounds' mono) <- lift . maybeToEither (TypeError "Could not find variable") . H.lookup n $ _context ctx
  instMap <- H.foldlWithKey instanceMap (return $ typeMap empty) bounds'
  --update (typeGen `over` genFrom) <&> ((m .) . typeMap . singleMap (Variable t) . _typeGen)
  return (empty, instMap mono)
  where
    instanceMap :: StateT TheContext (Either TypeError) (MonoType -> MonoType) -> String -> S.HashSet String -> StateT TheContext (Either TypeError) (MonoType -> MonoType)
    -- for some reason Haskell cannot infer this very easy to read, and easy to understand type
    instanceMap mmap k c = do
      map' <- mmap
      nBeta <- identifier . _typeGen <$> update (typeGen `over` genFrom)
      return $ (. map') $ typeMap $ singleMap (Variable c k) $ Variable c nBeta

algoW (Application e1 e2) = do
  (s1, t1) <- algoW e1
  modify $ context `over` H.map (polyMap s1)
  (s2, t2) <- algoW e2
  beta <- _typeGen <$> update (typeGen `over` genFrom)
  s3 <- lift $ unify (typeMap s2 t1) (Function t2 beta)
  return (s3 `compose` s2 `compose` s1, typeMap s3 beta)

algoW (Abstraction x e) = do
  beta <- _typeGen <$> update (typeGen `over` genFrom)
  modify $ context `over` H.insert x (Scheme H.empty beta)
  (s1, t1) <- algoW e
  return (s1, Function (typeMap s1 beta) t1)

algoW (LocalBind n e1 e2) = do
  (s1, t1) <- algoW e1
  ctx <- update (context `over` H.map (polyMap s1))
  modify $ context `over` H.insert n (Scheme (freeInCtx ctx) t1)
  (s2, t2) <- algoW e2
  return (s2 `compose` s1, t2)

algoW (Bind n e) = do
  (s1, t1) <- algoW e
  ctx <- update (context `over` H.map (polyMap s1))
  modify $ context `over` H.insert n (Scheme (freeInCtx ctx) t1)
  return (s1, Bottom)

main :: IO ()
main = do
  putStr "λ< "
  hFlush stdout
  input <- getLine
  case parse expression "CmdLn" input of
    (Right p) -> case fmap snd . evalStateT (algoW p) . TheContext builtIn $ Variable S.empty "τ0" of
      (Right t) -> putStr "σ> " >> print t
      (Left e)  -> putStr "σ!> " >> print e
    (Left e)  -> putStr "λ!> " >> print e
  main
  where
    a = Variable S.empty "a"
    s = Variable (S.singleton "Num") "s"
    forAll vs = H.fromList $ map (\(Variable c n) -> (n, c)) vs
    builtIn = H.fromList [
        ("eq", Scheme (forAll [a]) (Function a (Function a a))),
        ("inc", Scheme (forAll [s]) (Function s s))
      ]
