module Logic.Predicate.Parse
  ( parseTerm
  ) where

import Logic.Predicate

import Data.Maybe
import Text.ParserCombinators.Parsec
import qualified Data.Map.Strict as Map

-- | Utilities.

spacebars = skipMany (char ' ')

p_lparen = do char '('
              return ()

p_rparen = do char ')'
              return ()

-- p_lbracket = do char '['
--                 return ()

-- p_rbracket = do char ']'
--                 return ()

--------------------------------------------------------------------------------
-- | Parse a term.

parseTerm :: String -> Either ParseError Term
parseTerm input = parse p_term "Bad term" input

p_term = try p_const
         <|> try p_app
         <|> try p_var

p_const =
  do char '_'
     c <- many1 alphaNum
     return $ Const c
     <?> "constant"

p_var =
  do first <- lower
     v' <- many alphaNum
     return $ Var (first:v')
     <?> "variable"

p_varS =
  do first <- lower
     v' <- many alphaNum
     return (first:v')

p_app =
  do first <- lower
     f' <- many alphaNum
     spacebars
     ts <- p_argList
     return $ App (first:f') ts
     <?> "function application"

p_argList =
  do p_lparen
     ts <- sepBy1 (spacebars >> p_term <* spacebars) (char ',')
     p_rparen
     return ts

--------------------------------------------------------------------------------
-- | Parse a formula.

parseFormula :: String -> Either ParseError Formula
parseFormula input = parse p_formula "Bad formula" input

p_formula = try (p_binaryFormula "&" And)
            <|> try (p_binaryFormula "|" Or)
            <|> try (p_binaryFormula "=>" Implies)
            <|> try (p_binaryFormula "<=>" (<~>))
            <|> try (p_quantifier "forall" Forall)
            <|> try (p_quantifier "exists" Exists)
            <|> try p_bottom
            <|> try p_equals
            <|> try p_pred
            <|> try p_neg

p_pred =
  do first <- upper
     rest <- many alphaNum
     let p = first:rest
     ts <- optionMaybe p_argList
     case ts of
       Nothing -> return $ Pred p []
       Just ts -> return $ Pred p ts
     <?> "predicate"

p_equals =
  do p_lparen
     spacebars
     t1 <- p_term
     spacebars
     char '='
     spacebars
     t2 <- p_term
     spacebars
     p_rparen
     return $ Equals t1 t2

p_bottom =
  do string "_|_"
     return Bottom
     <?> "_|_"

p_neg =
  do string "~"
     spacebars
     x <- p_formula
     return $ Implies x Bottom

p_binaryFormula opString opFn =
  do p_lparen
     spacebars
     f <- p_formula
     spacebars
     string opString
     spacebars
     g <- p_formula
     spacebars
     p_rparen
     return $ opFn f g
     <?> "binary formula"

p_quantifier qString qFn =
  do string qString
     spacebars
     x <- p_varS
     spacebars
     char '.'
     spacebars
     f <- p_formula
     return $ qFn x f
