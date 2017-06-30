module Logic.Propositional.Prover
  ( prover
  ) where

import Logic.Propositional

import qualified Data.Set as S

prover :: Assumptions -> Formula -> Maybe Proof
prover = error "prover not implemented"
