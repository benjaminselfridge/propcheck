-- | Logic.Propositional.TruthTable

module Logic.Propositional.TruthTable
  ( truthTable
  , truthTableAndMessage
  ) where

import Logic.Propositional

import qualified Data.Set as S
import Data.Maybe

variables :: Formula -> S.Set String
variables (Var x)       = S.singleton x
variables (And f g)     = variables f `S.union` variables g
variables (Or f g)      = variables f `S.union` variables g
variables (Implies f g) = variables f `S.union` variables g
variables (Bottom)      = S.empty

varList :: Formula -> [String]
varList = S.toList . variables

assignments :: [String] -> [Assignment]
assignments [] = [[]]
assignments (x:xs) = [(x,a):as | a <- [True, False] , as <- assignments xs]

evalFormula :: Formula -> Assignment -> Either String Bool
evalFormula (Var x)       as = case lookup x as of
  Nothing -> Left x
  Just v -> return v
evalFormula (And f g)     as = do
  f' <- evalFormula f as
  g' <- evalFormula g as
  return $ f' && g'
evalFormula (Or f g)      as = do
  f' <- evalFormula f as
  g' <- evalFormula g as
  return $ f' || g'
evalFormula (Implies f g) as = do
  f' <- evalFormula f as
  g' <- evalFormula g as
  return $ if f' then g' else True
evalFormula (Bottom)      as = return False

ttHeader :: Formula -> String
ttHeader f = concat (map columnHeader (varList f)) ++
             "| " ++ show f ++ " \n"
  where columnHeader x = " " ++ x ++ " |"

ttSeparator :: Formula -> String
ttSeparator f = replicate (length columnHeaders - 1) '-' ++
                "||" ++ (replicate (length (show f) + 2) '-') ++ "\n"
  where columnHeader x = " " ++ x ++ " |"
        columnHeaders = concat (map columnHeader (varList f))

stringWidth :: String -> Int
stringWidth = maximum . map length . lines

padLine :: Int -> Int -> String -> String
padLine i j s = replicate i ' ' ++ s ++ replicate j ' '

pad :: Int -> Int -> String -> String
pad i j = unlines . map (padLine i j) . lines

ttRow :: Formula -> Assignment -> String
ttRow f as = concat (map rowEntry (varList f)) ++
             "| " ++ pad lpad rpad (boolTF f')
  where rowEntry x = padLine (varLpad x) (varRpad x) ((boolTF . fromJust .lookup x) as) ++ "|"
        varLpad x = (stringWidth (show x)) `div` 2
        varRpad x = (stringWidth (show x)) - (varLpad x) - 1
        boolTF True  = "T"
        boolTF False = "F"
        (Right f') = evalFormula f as
        formulaWidth = stringWidth (show f)
        lpad = formulaWidth `div` 2
        rpad = formulaWidth - lpad

truthTable :: Formula -> String
truthTable f = header ++ separator ++
               concat [ttRow f as | as <- assignments (varList f)]
  where header = ttHeader f
        separator = ttSeparator f

truthTableAndMessage :: Formula -> String
truthTableAndMessage f = (if all testFormula (assignments (varList f)) then
                            show f ++ " is a theorem.\n\nTruth table:\n"
                          else
                            show f ++ " is not a theorem.\n\nTruth Table:\n") ++
                         pad 2 0 (truthTable f)
  where testFormula a | Right v <- evalFormula f a = v
