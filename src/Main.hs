{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
module Main where

import System.IO
import Text.Parsec
import Data.Bool (bool)
import Data.Functor
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
    Variable { identifier :: String   }
  | Constant { constType  :: String   }
  | Function { takesType  :: MonoType , retsType :: MonoType }
  | Bottom -- for convenience
  deriving (Eq)

data PolyType = Scheme { bounds :: S.HashSet String , monoBounded :: MonoType }

data TheContext = TheContext { _context  :: H.HashMap String PolyType , _typeGen :: MonoType }
makeLenses ''TheContext

newtype Subs = Subs    { _typeMap :: H.HashMap String MonoType }

empty :: Subs
empty = Subs H.empty

genFrom :: MonoType -> MonoType
genFrom (Variable (t:ns)) = Variable $ (t :) $ show $ (read :: String -> Int) ns + 1
genFrom _                 = undefined

singleMap :: MonoType -> MonoType -> Subs
singleMap (Variable n) = Subs . H.singleton n
singleMap _            = undefined

typeMap :: Subs -> MonoType -> MonoType
typeMap s t@(Variable v)   = H.findWithDefault t v (_typeMap s)
typeMap s (Function tT rT) = let m = typeMap s tT
                                 m' = typeMap s rT
                             in Function m m'
typeMap _ t                = t

polyMap :: Subs -> PolyType -> PolyType
polyMap (Subs m) (Scheme bounds' monoBounded') = Scheme bounds' $ typeMap (Subs $ m `H.difference` S.toMap bounds') monoBounded'

compose :: Subs -> Subs -> Subs
compose (Subs m1) (Subs m2)
  = Subs $ H.foldMapWithKey (\t t' m -> H.alter (\case {
      Nothing  -> Just t';
      Just t''@(Variable v'') -> Just $ H.findWithDefault t'' v'' m;
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
  show (Constant c) = c
  show (Variable n) = n
  show (Function t1 t2) = '(' : show t1 ++ " -> " ++ show t2 ++ ")"

instance Show TypeError where
  show (TypeError e) = e

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

freeInType :: PolyType -> S.HashSet String
freeInType (Scheme bounds' monoBounded') = freeInType' monoBounded' `S.difference` bounds'
  where
    freeInType' Bottom = undefined
    freeInType' (Constant {}) = S.empty
    freeInType' (Variable n) = S.singleton n
    freeInType' (Function m1 m2) = freeInType' m1 `S.union` freeInType' m2

freeInCtx :: TheContext -> S.HashSet String
freeInCtx (TheContext ctx _) = foldl (\s p -> s `S.union` freeInType p) S.empty ctx

unify :: MonoType -> MonoType -> Either TypeError Subs
unify v@(Variable _)    v'@(Variable _)
  | v == v'   = Right $ Subs H.empty
  | otherwise = Right $ singleMap v v'
unify v@(Variable _)    t'
  | v `isIn` t' = Left $ TypeError "Infinite type"
  | otherwise   = Right $ singleMap v t'
  where isIn v' (Function rT tT) = v' `isIn` rT || v' `isIn` tT
        isIn v' v''@(Variable _) = v' == v''
        isIn _  _                = False
unify t                 v'@(Variable _)    = unify v' t
unify (Constant i)      (Constant i')      = bool (Left $ TypeError "Type mismatch") (Right empty) (i == i')
unify (Function tT rT)  (Function tT' rT') = unify tT tT' >>= \u -> compose u <$> (unify `on` typeMap u) rT rT'
unify _                 _                  = Left $ TypeError "Type mismatch"

algoW :: LambdaExpression -> StateT TheContext (Either TypeError) (Subs, MonoType)

algoW (Cnst _  t) = return (empty, case t of { Nat -> Constant "Nat" })

algoW (Var  n   ) = do
  ctx <- get
  (Scheme bounds' mono) <- lift . maybeToEither (TypeError "Could not find variable") . H.lookup n $ _context ctx
  instMap <- foldM (\m t -> update (typeGen `over` genFrom) <&> ((m .) . typeMap . singleMap (Variable t) . _typeGen)) (typeMap empty) bounds'
  return (empty, instMap mono)

algoW (Application e1 e2) = do
  (s1, t1) <- algoW e1
  modify $ context `over` H.map (polyMap s1)
  (s2, t2) <- algoW e2
  beta <- _typeGen <$> update (typeGen `over` genFrom)
  s3 <- lift $ unify (typeMap s2 t1) (Function t2 beta)
  return (s3 `compose` s2 `compose` s1, typeMap s3 beta)

algoW (Abstraction x e) = do
  beta <- _typeGen <$> update (typeGen `over` genFrom)
  modify $ context `over` H.insert x (Scheme S.empty beta)
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
    (Right p) -> case fmap snd . evalStateT (algoW p) . TheContext (H.fromList [ ("eq", Scheme (S.fromList ["a"]) (Function (Variable "a") (Function (Variable "a") (Constant "Bool")))) ]) $ Variable "τ0" of
      (Right t) -> putStr "σ> " >> print t
      (Left e)  -> putStr "σ!> " >> print e
    (Left e)  -> putStr "λ!> " >> print e
  main
