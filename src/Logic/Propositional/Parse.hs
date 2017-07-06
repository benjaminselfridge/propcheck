module Logic.Propositional.Parse
  ( parseFormula
  , parseProof
  ) where

import Logic.Propositional
import Logic.Propositional.Natural
import Logic.Propositional.Natural.ProofLine

import Data.Maybe
import Text.ParserCombinators.Parsec
import qualified Data.Map.Strict as Map

spacebars = skipMany (char ' ')

-- | Parse a formula.

parseFormula :: String -> Either ParseError Formula
parseFormula input = parse (spacebars >>
                            p_outerFormula
                            <* skipMany (char ' ')
                            <* eof)
                     "Bad formula" input

p_outerFormula = try (p_outerBinaryFormula "&" And)
                 <|> try (p_outerBinaryFormula "|" Or)
                 <|> try (p_outerBinaryFormula "=>" Implies)
                 <|> try (p_outerBinaryFormula "<=>" iff)
                 <|> p_formula

p_formula = try (p_binaryFormula "&" And)
            <|> try (p_binaryFormula "|" Or)
            <|> try (p_binaryFormula "=>" Implies)
            <|> try (p_binaryFormula "<=>" iff)
            <|> p_neg
            <|> p_bottom
            <|> p_var
            <?> "formula"

p_var =
  do x <- many1 alphaNum
     return $ Var x
     <?> "variable"

p_outerBinaryFormula opString opFn =
  do f <- p_formula
     spacebars
     string opString
     spacebars
     g <- p_formula
     return $ opFn f g
     <?> "formula"

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

p_bottom =
  do string "_|_"
     return Bottom
     <?> "_|_"

p_neg =
  do string "~"
     spacebars
     x <- p_formula
     return $ Implies x Bottom

p_lparen = do char '('
              return ()

p_rparen = do char ')'
              return ()

p_lbracket = do char '['
                return ()

p_rbracket = do char ']'
                return ()

-- | Parse a proof reference.

parseProofRef :: String -> Either ParseError ProofRef
parseProofRef input = parse (spacebars >>
                            p_ref
                            <* spacebars
                            <* eof)
                      "Bad proof reference" input

p_ref = try (p_ref0 "Assumption" AssumptionRef)
        <|> try (p_ref0 "ExcludedMiddle" ExcludedMiddleRef)
        <|> try (p_ref1 "AndElimL" AndElimLRef)
        <|> try (p_ref1 "AndElimR" AndElimRRef)
        <|> try (p_ref1 "ImpliesIntro" ImpliesIntroRef)
        <|> try (p_ref1 "OrIntroL" OrIntroLRef)
        <|> try (p_ref1 "OrIntroR" OrIntroRRef)
        <|> try (p_ref1 "BottomElim" BottomElimRef)
        <|> try (p_ref2 "AndIntro" AndIntroRef)
        <|> try (p_ref2 "ImpliesElim" ImpliesElimRef)
        <|> try (p_ref3 "OrElim" OrElimRef)

p_ref0 refString refFn =
  do p_lbracket
     spacebars
     string refString
     spacebars
     p_rbracket
     return refFn

p_ref1 refString refFn =
  do p_lbracket
     spacebars
     string refString
     spacebars
     i <- many1 digit
     spacebars
     p_rbracket
     return $ refFn (read i)

p_ref2 refString refFn =
  do p_lbracket
     spacebars
     string refString
     spacebars
     i <- many1 digit
     spacebars
     j <- many1 digit
     spacebars
     p_rbracket
     return $ refFn (read i) (read j)

p_ref3 refString refFn =
  do p_lbracket
     spacebars
     string refString
     spacebars
     i <- many1 digit
     spacebars
     j <- many1 digit
     spacebars
     k <- many1 digit
     spacebars
     p_rbracket
     return $ refFn (read i) (read j) (read k)

-- | Parsing a proof body.
parseProofBody :: String -> Either ParseError [Maybe ProofLine]
parseProofBody input = parse (spaces >>
                              p_lines
                              <* spacebars
                              <* eof)
                       "Bad proof body" input

p_line =
  do spacebars
     i <- many1 digit
     spacebars
     char '.'
     spacebars
     f <- p_outerFormula
     spacebars
     r <- p_ref
     spacebars
     optional p_comment
     return $ Just (read i, (f, r))

p_comment =
  do string "--"
     many (noneOf ['\n'])
     return ()

p_blankLine =
  do spacebars
     optional p_comment
     return Nothing

p_blankLines = many (p_blankLine <* newline)

p_lines = endBy (try p_line <|> p_blankLine) (newline)

-- | Parsing a proof.
parseProofLines :: String -> Either ParseError [Maybe ProofLine]
parseProofLines input = parse (spaces >>
                               p_proof)
                        "Error parsing proof" input

p_proof =
  do p_blankLines
     string "Proof."
     spacebars
     newline
     p_blankLines
     body <- p_lines
     p_blankLines
     string "QED"
     return body

parseProof :: String -> Either String Proof
parseProof input =
  case parseProofLines input of
    Left parseError -> Left $ show parseError
    Right proofLines ->
      case genProof (catMaybes proofLines) of
        Left e -> Left e
        Right proof -> Right proof
