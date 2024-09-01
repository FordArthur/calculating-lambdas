module Main where

import System.IO
import Text.Parsec

data CnstType = Nat

data LambdaExpression = 
    Cnst        { cnst   :: String           , cnstT :: CnstType         }
  | Var         { name   :: String           }
  | Application { func   :: LambdaExpression , arg   :: LambdaExpression }
  | Abstraction { var    :: String           , ret   :: LambdaExpression }
  | LocalBind   { lName  :: String           , lExpr :: LambdaExpression , inExpr :: LambdaExpression}
  | Bind        { bName  :: String           , bExpr :: LambdaExpression }

newtype VarIdentifier = VarIdentifier Int
newtype ConstIdentifier = ConstIdentifier Int

data MonoType =
    Variable { identifier :: VarIdentifier   }
  | Constant { constType  :: ConstIdentifier , typeArgs :: [MonoType] }

data PolyType =
    Mono       { mono  :: MonoType }
  | Quantified { bound :: MonoType , bounded :: MonoType }

instance Show LambdaExpression where
  show (Cnst c _) = c
  show (Var n) = n
  show (Application f a) = show f ++ ' ' : show a
  show (Abstraction v r) = 'λ' : v ++ ". " ++ show r
  show (LocalBind b v e) = "let " ++ b ++ " = " ++ show v ++ " in " ++ show e 
  show (Bind b e)        = "let " ++ b ++ " := " ++ show e

nat :: Parsec String () LambdaExpression
nat = (`Cnst` Nat) <$> many1 digit

constant :: Parsec String () LambdaExpression
constant = nat

variable :: Parsec String () LambdaExpression
variable = fmap Var $ many1 $ lower <|> oneOf "αβγδεζηθικμνξοπρσςΤτΥυΦφΧχΨψΩω"

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

main :: IO ()
main = do
  putStr "λ< "
  hFlush stdout
  input <- getLine
  case parse expression "CmdLn" input of
    (Right p) -> putStr "λ> " >> print p
    (Left e)  -> putStr "!> " >> print e
  main
