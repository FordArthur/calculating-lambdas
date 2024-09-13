module Parser where

import Text.Parsec

data CnstType = Nat

newtype SIdent a = IdenNT { name :: String }

data LambdaExpressionIndexedBy i a =
    Cnst        { cnst   :: String                        , cnstT :: CnstType                      }
  | Var         { atom   :: i a                           }
  | Application { func   :: LambdaExpressionIndexedBy i a , arg   :: LambdaExpressionIndexedBy i a }
  | Abstraction { var    :: i a                           , ret   :: LambdaExpressionIndexedBy i a }
  | LocalBind   { lName  :: i a                           , lExpr :: LambdaExpressionIndexedBy i a , inExpr :: LambdaExpressionIndexedBy i a}
  | Bind        { bName  :: i a                           , bExpr :: LambdaExpressionIndexedBy i a }

instance Show (i a) => Show (LambdaExpressionIndexedBy i a) where
  show (Cnst c _)        = c
  show (Var v)           = show v
  show (Application f a) = show f ++ ' ' : show a
  show (Abstraction v r) = 'λ' : show v ++ ". " ++ show r
  show (LocalBind b v e) = "let " ++ show b ++ " = " ++ show v ++ " in " ++ show e
  show (Bind b e) = "let " ++ show b ++ " := " ++ show e

data NoType = NoType

nat :: Parsec String () (LambdaExpressionIndexedBy SIdent NoType)
nat = (`Cnst` Nat) <$> many1 digit

constant :: Parsec String () (LambdaExpressionIndexedBy SIdent NoType)
constant = nat

variable :: Parsec String () (LambdaExpressionIndexedBy SIdent NoType)
variable = fmap (Var . IdenNT) $ many1 $ lower <|> oneOf "αβγδεζηθικμνξοπρσςτυφχψω"

application :: Parsec String () (LambdaExpressionIndexedBy SIdent NoType)
application = between (char '(') (char ')') $ Application <$> expression <*> (spaces >> expression)

abstraction :: Parsec String () (LambdaExpressionIndexedBy SIdent NoType)
abstraction = do
  _ <- oneOf "\\λ"
  spaces
  vararg <- atom <$> variable
  spaces
  _ <- char '.'
  spaces
  Abstraction vararg <$> expression

binds :: Parsec String () (LambdaExpressionIndexedBy SIdent NoType)
binds = do
  _ <- string "let"
  spaces
  ctarg <- atom <$> variable
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

expression :: Parsec String () (LambdaExpressionIndexedBy SIdent NoType)
expression = application <|> abstraction <|> binds <|> variable <|> constant

parseExpression :: String -> Either ParseError (LambdaExpressionIndexedBy SIdent NoType)
parseExpression = parse expression "Commandline"
