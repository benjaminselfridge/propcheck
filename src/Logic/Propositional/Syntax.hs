-- | Logic.Propositional.Syntax

-- This module defines the syntax of constructive propositional
-- calculus. We introduce two major datatypes, Formula and Proof.

module Logic.Propositional.Syntax
  ( Formula(..),
    Proof(..),
    a, b, c,
    (~&), (~|), (~>), bot, neg, iff
  ) where

data Formula = Var String
             | And Formula Formula
             | Or Formula Formula
             | Implies Formula Formula
             | Bottom
  deriving (Eq, Ord)

instance Show Formula where
  show (Var s) = s
  show (And (Implies a b) (Implies c d))
    | a == d && b == c = "(" ++ show a ++ " <=> " ++ show b ++ ")"
  show (And a b) = "(" ++ show a ++ " & " ++ show b ++ ")"
  show (Or a b) = "(" ++ show a ++ " | " ++ show b ++ ")"
  show (Implies a Bottom) = "!" ++ show a
  show (Implies a b) = "(" ++ show a ++ " => " ++ show b ++ ")"
  show Bottom = "_|_"

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

showProof_ :: String -> Proof -> String
showProof_ pad (Assumption formula) =
  pad ++ show formula ++ " [Assumption]"
showProof_ pad (AndIntro formula p1 p2) =
  pad ++ show formula ++ " [AndIntro]\n" ++
  showProof_ (pad++"  ") p1 ++ "\n" ++
  showProof_ (pad++"  ") p2
showProof_ pad (AndElimL formula p) =
  pad ++ show formula ++ " [AndElimL]\n" ++
  showProof_ (pad++"  ") p
showProof_ pad (AndElimR formula p) =
  pad ++ show formula ++ " [AndElimR]\n" ++
  showProof_ (pad++"  ") p
showProof_ pad (ImpliesIntro formula p) =
  pad ++ show formula ++ " [ImpliesIntro]\n" ++
  showProof_ (pad++"  ") p
showProof_ pad (ImpliesElim formula p1 p2) =
  pad ++ show formula ++ " [ImpliesElim]\n" ++
  showProof_ (pad++"  ") p1 ++ "\n" ++
  showProof_ (pad++"  ") p2
showProof_ pad (OrIntroL formula p) =
  pad ++ show formula ++ " [OrIntroL]\n" ++
  showProof_ (pad++"  ") p
showProof_ pad (OrIntroR formula p) =
  pad ++ show formula ++ " [OrIntroR]\n" ++
  showProof_ (pad++"  ") p
showProof_ pad (OrElim formula p1 p2 p3) =
  pad ++ show formula ++ " [OrElim]\n" ++
  showProof_ (pad++"  ") p1 ++ "\n" ++
  showProof_ (pad++"  ") p2 ++ "\n" ++
  showProof_ (pad++"  ") p3
showProof_ pad (BottomElim formula p) =
  pad ++ show formula ++ " [BottomElim]\n" ++
  showProof_ (pad++"  ") p

showProof :: Proof -> String
showProof = showProof_ ""

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
