-- | Logic.Propositional.Semantics

-- This module introduces a function called checkProof, which analyzes
-- a proof object and both 1) checks it for syntactic correctness and
-- 2) determines under what assumptions it is valid. We also export
-- the conclusion function, which takes a proof and tells you what the
-- conclusion is.

module Logic.Propositional.Semantics
  ( Assumptions
  , checkProof
  , ppTheorem
  , ppTheoremAndProof
  ) where

import Logic.Propositional.Syntax

import Data.List
import qualified Data.Set as S

type Assumptions = S.Set Formula

checkProof :: Proof -> Either String Assumptions
checkProof proof
  | Assumption f <- proof = return $ S.singleton f
  | AndIntro (And f g) p1 p2 <- proof,
    conclusion p1 == f,
    conclusion p2 == g =
      do a1 <- checkProof p1
         a2 <- checkProof p2
         return $ S.union a1 a2
  | AndElimL f p <- proof,
    And g _ <- conclusion p,
    g == f =
      checkProof p
  | AndElimR f p <- proof,
    And _ g <- conclusion p,
    g == f =
      checkProof p
  | ImpliesIntro (Implies f g) p <- proof,
    conclusion p == g =
      do a <- checkProof p
         return $ S.delete f a
  | ImpliesElim f p1 p2 <- proof,
    Implies g h <- conclusion p2,
    conclusion p1 == g,
    h == f =
      do a1 <- checkProof p1
         a2 <- checkProof p2
         return $ S.union a1 a2
  | OrIntroL (Or f g) p <- proof,
    conclusion p == f =
      checkProof p
  | OrIntroR (Or f g) p <- proof,
    conclusion p == g =
      checkProof p
  | OrElim f p1 p2 p3 <- proof,
    conclusion p2 == f,
    conclusion p3 == f,
    Or g h <- conclusion p1 =
      do a1 <- checkProof p1
         a2 <- checkProof p2
         a3 <- checkProof p3
         let a2' = S.delete g a2
         let a3' = S.delete h a3
         return $ S.union a1 (S.union a2' a3')
  | BottomElim f p <- proof,
    Bottom <- conclusion p =
      do checkProof p
  | ExcludedMiddle (Or f (Implies g Bottom)) <- proof,
    f == g =
      return S.empty
  | otherwise = Left $ "Ill-formed proof:\n" ++ show proof

ppTheorem :: Proof -> String
ppTheorem p = case checkProof p of
  Right as -> "Thm: [" ++ showAssumptions as ++ "]"  ++
              " |- " ++ show (conclusion p)
  Left s -> s
  where showAssumptions = intercalate ", " . map show . S.toList

ppTheoremAndProof :: Proof -> String
ppTheoremAndProof p = case checkProof p of
  Right as -> "Thm: [" ++ showAssumptions as ++ "]"  ++
              " |- " ++ show (conclusion p) ++ "\n" ++
              "Proof:\n" ++ show p
  Left s -> s
  where showAssumptions = intercalate ", " . map show . S.toList
