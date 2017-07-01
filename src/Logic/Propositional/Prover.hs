module Logic.Propositional.Prover
  ( prover1
  , prover2
--  , conjuncts
  ) where

import Logic.Propositional

import Control.Applicative
import Data.List
import Data.Maybe
import qualified Data.Set as S

-------------------------------------------------------
--                      prover1                      --
-------------------------------------------------------

-- Our first attempt at a prover just assumes the formula it is trying to
-- prove. Not the most intelligent way to do it.
prover1 :: Assumptions -> Formula -> Proof
prover1 assumptions f = Assumption f


-------------------------------------------------------
--                      prover2                      --
-------------------------------------------------------

-- Our second attempt at a prover will, after first checking the list of
-- assumptions for the formula, see if it can build up an And formula from
-- provable subformulas.
prover2 :: Assumptions -> Formula -> Proof
prover2 assumptions f
  | f `S.member` assumptions = Assumption f
  | (And g h) <- f,
    g_proof <- prover2 assumptions g,
    h_proof <- prover2 assumptions h =
      AndIntro f g_proof h_proof
  | otherwise = Assumption f


-------------------------------------------------------
--                      prover3                      --
-------------------------------------------------------

-- prover3 will incorporate prover2, and it will also attempt to conclude
-- formulas from the various conjuncts of the assumptions.

findAsLConjunct :: Formula -> Formula -> Maybe Formula
findAsLConjunct f (And g h)
  | g == f = Just $ And g h
  | Just conjunct <- findAsLConjunct f g = Just conjunct
  | Just conjunct <- findAsLConjunct f h = Just conjunct
findAsLConjunct _ _ = Nothing

findAsRConjunct :: Formula -> Formula -> Maybe Formula
findAsRConjunct f (And g h)
  | h == f = Just $ And g h
  | Just conjunct <- findAsRConjunct f g = Just conjunct
  | Just conjunct <- findAsRConjunct f h = Just conjunct
findAsRConjunct _ _ = Nothing
    
prover3 :: Assumptions -> Formula -> Proof
prover3 assumptions f
  | f `S.member` assumptions = Assumption f
  | (conjunct:_) <- catMaybes $ (findAsLConjunct f) <$> (S.toList assumptions) =
      AndElimL f (prover3 assumptions conjunct)
  | (conjunct:_) <- catMaybes $ (findAsRConjunct f) <$> (S.toList assumptions) =
      AndElimR f (prover3 assumptions conjunct)
  | (And g h) <- f,
    g_proof <- prover3 assumptions g,
    h_proof <- prover3 assumptions h =
      AndIntro f g_proof h_proof
  | otherwise = Assumption f

-- Note that there is a smarter way to do this, by finding ALL instances of the
-- formula on the left and the right, finding the shallowest occurrence, and
-- using that one. However, we don't want to get that fancy just yet. See below
-- for the definitions.

-- findAsLConjunct' :: Int -> Formula -> Formula -> [(Int, Formula)]
-- findAsLConjunct' i f (And g h)
--   | g == f = (i, And g h) : findAsLConjunct' (i+1) f g ++ findAsLConjunct' (i+1) f h
--   | otherwise = findAsLConjunct' (i+1) f g ++ findAsLConjunct' (i+1) f h
-- findAsLConjunct' _ _ _ = []

-- findAsLConjunct :: Formula -> Formula -> [(Int, Formula)]
-- findAsLConjunct = findAsLConjunct' 1

-- findAsRConjunct' :: Int -> Formula -> Formula -> [(Int, Formula)]
-- findAsRConjunct' i f (And g h)
--   | h == f = (i, And g h) : findAsRConjunct' (i+1) f g ++ findAsRConjunct' (i+1) f h
--   | otherwise = findAsRConjunct' (i+1) f g ++ findAsRConjunct' (i+1) f h
-- findAsRConjunct' _ _ _ = []

-- findAsRConjunct :: Formula -> Formula -> [(Int, Formula)]
-- findAsRConjunct = findAsRConjunct' 1




-------------------------------------------------------
--                      prover4                      --
-------------------------------------------------------

-- prover4 will incorporate prover3 , with the additional ability to use the
-- implies introduction rule whenever it encounters an implication in the
-- conclusion (and the other techniques have failed).

prover4 :: Assumptions -> Formula -> Proof
prover4 assumptions f
  | f `S.member` assumptions = Assumption f
  | (conjunct:_) <- catMaybes $ (findAsLConjunct f) <$> (S.toList assumptions) =
      AndElimL f (prover4 assumptions conjunct)
  | (conjunct:_) <- catMaybes $ (findAsRConjunct f) <$> (S.toList assumptions) =
      AndElimR f (prover4 assumptions conjunct)
  | And g h <- f,
    g_proof <- prover4 assumptions g,
    h_proof <- prover4 assumptions h =
      AndIntro f g_proof h_proof
  | Implies g h <- f,
    h_proof <- prover4 (S.insert g assumptions) h =
      ImpliesIntro f h_proof
  | otherwise = Assumption f




-------------------------------------------------------
--                      prover5                      --
-------------------------------------------------------

-- prover5 will incorporate prover4, with the additional ability to use the
-- implies elimination rule. This is the first time the prover will be
-- considering several potential proofs and deciding between each of them.

-- Takes a formula f and a formula g, and returns a set of subformulas of g
-- where f appears on the right hand side of an implication.
findAsRHS :: Formula -> Formula -> S.Set Formula
findAsRHS f (Implies g h)
  | h == f = S.singleton $ Implies g h
  | otherwise = findAsRHS f h
findAsRHS f (And g h) = findAsRHS f g `S.union` findAsRHS f h
findAsRHS f (Or g h)  = findAsRHS f g `S.union` findAsRHS f h
findAsRHS f _ = S.empty

fewerAssumptions :: Proof -> Proof -> Bool
fewerAssumptions p1 p2
  | Right a1 <- checkProof p1,
    Right a2 <- checkProof p2 =
      length a1 < length a2

prover5 :: Assumptions -> Formula -> Proof
prover5 assumptions f
  | f `S.member` assumptions = Assumption f
  | (conjunct:_) <- catMaybes $ (findAsLConjunct f) <$> (S.toList assumptions) =
      AndElimL f (prover5 assumptions conjunct)
  | (conjunct:_) <- catMaybes $ (findAsRConjunct f) <$> (S.toList assumptions) =
      AndElimR f (prover5 assumptions conjunct)
  | And g h <- f,
    g_proof <- prover5 assumptions g,
    h_proof <- prover5 assumptions h =
      AndIntro f g_proof h_proof
  | Implies g h <- f,
    h_proof <- prover5 (S.insert g assumptions) h =
      ImpliesIntro f h_proof
  | otherwise = Assumption f

-- prover5' :: Assumptions -> Formula -> [Proof]
-- prover5' assumptions f
--   | f `S.member` assumptions = [Assumption f]
--   | (conjunct:_) <- catMaybes $ (findAsLConjunct f) <$> (S.toList assumptions) =
--       map (AndElimL f) (prover5' assumptions conjunct)
--   | (conjunct:_) <- catMaybes $ (findAsRConjunct f) <$> (S.toList assumptions) =
--       map (AndElimR f) (prover5' assumptions conjunct)
--  | impliers@(_:_) <- (S.toList . S.unions) $ findAsRHS f <$> (S.toList assumptions) =
--       let candidateProofs@(p1:_) = concat (map makeImpliesProof impliers)
-- --          smallestProof = pickProof candidateProofs
--       in candidateProofs
--   | And g h <- f,
--     g_proofs <- prover5' assumptions g,
--     h_proofs <- prover5' assumptions h =
--       liftA2 (AndIntro f) g_proofs h_proofs
--   | Implies g h <- f,
--     h_proofs <- prover5' (S.insert g assumptions) h =
--       map (ImpliesIntro f) h_proofs
--   | otherwise = [Assumption f]

--   where makeImpliesProof g@(Implies h _) =
--           liftA2 (ImpliesElim f) (prover5' assumptions h) (prover5' assumptions g)

-- prover5 assumptions proof = pickProof $ prover5' assumptions proof
--   where  pickProof (c:cs) = foldl withFewerAssumptions c (c:cs)
--          withFewerAssumptions p1 p2 = if p1 `fewerAssumptions` p2 then p1 else p2
--        pickProof (c:cs) = foldl fewerAssumptions c (c:cs)
-- It's not the candidate proof with the fewest assumptions. It's the one where
-- the proof of h has the fewest assumptions! ... or is it?
