module Logic.Propositional
  ( Formula(..)
  , a, b, c
  , (~&), (~|), (~>), bot, neg, iff
  , Assignment
  , showAssignment
  ) where

-- This module defines the syntax of propositional calculus. We
-- introduce the Formula datatype.

import Data.List
import qualified Data.Set as S

data Formula = Var String
             | And Formula Formula
             | Or Formula Formula
             | Implies Formula Formula
             | Bottom
  deriving (Eq, Ord)

showFormula :: Formula -> String
showFormula (Var s) = s
showFormula (And (Implies a b) (Implies c d))
  | a == d && b == c = "(" ++ showFormula a ++ " <=> " ++ showFormula b ++ ")"
showFormula (And a b) = "(" ++ showFormula a ++ " & " ++ showFormula b ++ ")"
showFormula (Or a b) = "(" ++ showFormula a ++ " | " ++ showFormula b ++ ")"
showFormula (Implies a Bottom) = "~" ++ showFormula a
showFormula (Implies a b) = "(" ++ showFormula a ++ " => " ++ showFormula b ++ ")"
showFormula Bottom = "_|_"

showFormulaTop :: Formula -> String
showFormulaTop (Var s) = s
showFormulaTop (And (Implies a b) (Implies c d))
  | a == d && b == c = showFormula a ++ " <=> " ++ showFormula b
showFormulaTop (And a b) = showFormula a ++ " & " ++ showFormula b
showFormulaTop (Or a b) = showFormula a ++ " | " ++ showFormula b
showFormulaTop (Implies a Bottom) = "~" ++ showFormula a
showFormulaTop (Implies a b) = showFormula a ++ " => " ++ showFormula b
showFormulaTop Bottom = "_|_"

instance Show Formula where
  show = showFormulaTop

-- | Convenience definitions for variables
a = Var "a"
b = Var "b"
c = Var "c"

-- Infix operators for formula construction
(~&) = And
(~|) = Or
(~>) = Implies
bot = Bottom

-- Derived operators for formula construction
neg f = Implies f bot
iff f g = And (Implies f g) (Implies g f)

-- | Assignments

type Assignment = [(String, Bool)]

showAssignment :: Assignment -> String
showAssignment = intercalate "\n" . map showPair
  where showPair (var, val) = var ++ " = " ++ show val
