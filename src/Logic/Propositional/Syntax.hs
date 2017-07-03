-- | Logic.Propositional.Syntax

-- This module defines the syntax of constructive propositional
-- calculus. We introduce two major datatypes, Formula and Proof.

module Logic.Propositional.Syntax
  ( Formula(..)
  , Proof(..)
  , conclusion
  , a, b, c
  , (~&), (~|), (~>), bot, neg, iff
  ) where

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
showFormula (Implies a Bottom) = "!" ++ showFormula a
showFormula (Implies a b) = "(" ++ showFormula a ++ " => " ++ showFormula b ++ ")"
showFormula Bottom = "_|_"

showFormulaTop :: Formula -> String
showFormulaTop (Var s) = s
showFormulaTop (And (Implies a b) (Implies c d))
  | a == d && b == c = showFormula a ++ " <=> " ++ showFormula b
showFormulaTop (And a b) = showFormula a ++ " & " ++ showFormula b
showFormulaTop (Or a b) = showFormula a ++ " | " ++ showFormula b
showFormulaTop (Implies a Bottom) = "!" ++ showFormula a
showFormulaTop (Implies a b) = showFormula a ++ " => " ++ showFormula b
showFormulaTop Bottom = "_|_"

instance Show Formula where
  show = showFormulaTop

data Proof = Assumption Formula
           | AndIntro Formula Proof Proof
           | AndElimL Formula Proof
           | AndElimR Formula Proof
           | ImpliesIntro Formula Proof
           | ImpliesElim Formula Proof Proof
           | OrIntroL Formula Proof
           | OrIntroR Formula Proof
           | OrElim Formula Proof Proof Proof
           | BottomElim Formula Proof
           | ExcludedMiddle Formula
           deriving (Eq, Ord)

conclusion :: Proof -> Formula
conclusion (Assumption f) = f
conclusion (AndIntro f _ _) = f
conclusion (AndElimL f _) = f
conclusion (AndElimR f _) = f
conclusion (ImpliesIntro f _) = f
conclusion (ImpliesElim f _ _) = f
conclusion (OrIntroL f _) = f
conclusion (OrIntroR f _) = f
conclusion (OrElim f _ _ _) = f
conclusion (BottomElim f _) = f
conclusion (ExcludedMiddle f) = f

showProof_ :: S.Set Formula -> String -> Proof -> String
showProof_ pool pad (Assumption formula) =
  pad ++ show formula ++ " [Assumption]" ++
  if (formula `S.member` pool) then "*" else ""
showProof_ pool pad (AndIntro formula p1 p2) =
  pad ++ show formula ++ " [AndIntro]\n" ++
  showProof_ pool (pad++"  ") p1 ++ "\n" ++
  showProof_ pool (pad++"  ") p2
showProof_ pool pad (AndElimL formula p) =
  pad ++ show formula ++ " [AndElimL]\n" ++
  showProof_ pool (pad++"  ") p
showProof_ pool pad (AndElimR formula p) =
  pad ++ show formula ++ " [AndElimR]\n" ++
  showProof_ pool (pad++"  ") p
showProof_ pool pad (ImpliesIntro formula@(Implies f _) p) =
  pad ++ show formula ++ " [ImpliesIntro]\n" ++
  showProof_ (S.insert f pool) (pad++"  ") p
showProof_ pool pad (ImpliesElim formula p1 p2) =
  pad ++ show formula ++ " [ImpliesElim]\n" ++
  showProof_ pool (pad++"  ") p1 ++ "\n" ++
  showProof_ pool (pad++"  ") p2
showProof_ pool pad (OrIntroL formula p) =
  pad ++ show formula ++ " [OrIntroL]\n" ++
  showProof_ pool (pad++"  ") p
showProof_ pool pad (OrIntroR formula p) =
  pad ++ show formula ++ " [OrIntroR]\n" ++
  showProof_ pool (pad++"  ") p
showProof_ pool pad (OrElim formula p1 p2 p3)
  | Or f g <- conclusion p1 =
    pad ++ show formula ++ " [OrElim]\n" ++
    showProof_ pool (pad++"  ") p1 ++ "\n" ++
    showProof_ (S.insert f pool) (pad++"  ") p2 ++ "\n" ++
    showProof_ (S.insert g pool) (pad++"  ") p3
showProof_ pool pad (BottomElim formula p) =
  pad ++ show formula ++ " [BottomElim]\n" ++
  showProof_ pool (pad++"  ") p
showProof_ pool pad (ExcludedMiddle formula) =
  pad ++ show formula ++ " [ExcludedMiddle]"

showProof :: Proof -> String
showProof = showProof_ S.empty ""

instance Show Proof where
  show = showProof

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
