-- | Logic.Propositional.Natural

module Logic.Propositional.Natural
  ( Proof(..)
  , conclusion
  , Assumptions
  , checkProof
  , ppTheorem
  , ppTheoremAndProof
  ) where

import Logic.Propositional

import Data.List
import qualified Data.Set as S

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

type Assumptions = S.Set Formula

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
