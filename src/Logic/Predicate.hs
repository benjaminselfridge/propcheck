module Logic.Predicate
  ( Term(..)
  , Formula(..)
  , a, b, c
  , x, y, z
  , f, g, h
  , p, q, r
  , (~&), (~|), (~>), (<~>), (~=)
  , bot, forall, exists, neg
  , occurs
  , subTerm
  , right
  ) where

-- This module defines the syntax of propositional calculus. We
-- introduce the Formula datatype.

import Data.List
import qualified Data.Set as S

-- | Utility functions.

right :: (a -> Either b c) -> a -> c
right f x | Right x' <- f x = x'
          | otherwise = error "right: bad input"

-- | Term datatype.
data Term = Const String
          | Var String
          | App String [Term]
  deriving (Eq, Ord)

instance Show Term where
  show (Const s)  = "_" ++ s
  show (Var s)    = s
  show (App f ts) = f ++ "(" ++ intercalate "," (map show ts) ++ ")"

-- | Formula datatype.
data Formula = Bottom
             | Pred String [Term]
             | Equals Term Term
             | Implies Formula Formula
             | And Formula Formula
             | Or Formula Formula
             | Forall String Formula
             | Exists String Formula
  deriving (Eq, Ord)

showFormula :: Formula -> String
showFormula (Pred pred []) = pred
showFormula (Pred pred terms) =
  pred ++ "(" ++ intercalate "," (map show terms) ++ ")"
showFormula (Equals s t) = "(" ++ show s ++ " = " ++ show t ++ ")"
showFormula Bottom = "_|_"
showFormula (Implies f Bottom) = "~" ++ showFormula f
showFormula (Implies f g) = "(" ++ showFormula f ++ " => " ++ showFormula g ++ ")"
showFormula (And (Implies f g) (Implies g' f'))
  | f == f' && g == g' = "(" ++ showFormula f ++ " <=> " ++ showFormula g ++ ")"
showFormula (And     f g) = "(" ++ showFormula f ++ " & " ++ showFormula g ++ ")"
showFormula (Or      f g) = "(" ++ showFormula f ++ " | " ++ showFormula g ++ ")"
showFormula (Forall  x f) = "forall " ++ x ++ " . " ++ showFormula f
showFormula (Exists  x f) = "exists " ++ x ++ " . " ++ showFormula f

showFormulaTop :: Formula -> String
showFormulaTop (Equals s t) = show s ++ " = " ++ show t
showFormulaTop f@(Implies _ Bottom) = showFormula f
showFormulaTop (Implies f g) = showFormula f ++ " => " ++ showFormula g
showFormulaTop (And (Implies f g) (Implies g' f'))
  | f == f' && g == g' = showFormula f ++ " <=> " ++ showFormula g
showFormulaTop (And f g) = showFormula f ++ " & " ++ showFormula g
showFormulaTop (Or  f g) = showFormula f ++ " | " ++ showFormula g
showFormulaTop f = showFormula f

instance Show Formula where
  show = showFormulaTop

-- | Easy to use constructors.

a = Const "a"
b = Const "b"
c = Const "c"

x = Var "x"
y = Var "y"
z = Var "z"

f = App "f"
g = App "g"
h = App "h"

p = Pred "P"
q = Pred "Q"
r = Pred "R"

-- Infix operators for formula construction
(~&) = And
(~|) = Or
(~>) = Implies
(~=) = Equals

-- quick bottom, forall, exists
bot = Bottom
forall = \(Var x) -> Forall x
exists = \(Var x) -> Exists x

-- Derived operators for formula construction
neg f = Implies f bot
(<~>) f g = And (Implies f g) (Implies g f)

-- | Substitution

-- variable occurs in a term
occursTerm :: String -> Term -> Bool
occursTerm v (Var q) | v == q = True
occursTerm v (App f ts) = any (occursTerm v) ts
occursTerm _ _ = False

-- variable occurs free in a formula
occurs :: String -> Formula -> Bool
occurs x Bottom = False
occurs x (Pred _ ts) = any (occursTerm x) ts
occurs x (Equals s t) = occursTerm x s || occursTerm x t
occurs x (Implies f g) = occurs x f || occurs x g
occurs x (And f g) = occurs x f || occurs x g
occurs x (Or f g) = occurs x f || occurs x g
occurs x (Forall y f) | x == y = False
                      | otherwise = occurs x f
occurs x (Exists y f) | x == y = False
                      | otherwise = occurs x f

-- substitute a term for a variable in another term
substTerm :: String -> Term -> Term -> Term
substTerm x t (Const c) = Const c
substTerm x t (Var y) | x == y = t
                      | otherwise = Var y
substTerm x t (App f ts) = App f $ map (substTerm x t) ts


