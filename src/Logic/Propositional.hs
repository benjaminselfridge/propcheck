module Logic.Propositional
  ( Formula(..),
    Proof(..),
    a, b, c,
    (~&), (~|), (~>), bot, neg, iff,
    conclusion,
    Assumptions,
    checkProof,
    ppTheorem,
    ppTheoremAndProof
  ) where

import Logic.Propositional.Syntax
import Logic.Propositional.Semantics
