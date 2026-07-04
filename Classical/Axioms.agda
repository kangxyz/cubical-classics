{-# OPTIONS --safe #-}
module Classical.Axioms where

open import Cubical.Foundations.Prelude
import Cubical.Axiom.ExcludedMiddle as CubicalEM

open import Classical.Axioms.Choice public
open import Classical.Axioms.ExcludedMiddle public

-- Most classical modules take this record as an instance argument.
record Oracle : Typeω where
  field
    decide : LEM

AC→LEM : AC → LEM
AC→LEM choose {ℓ} = CubicalEM.Diaconescu ℓ λ X → choose X

record MegaPicker : Typeω where
  field
    choose : AC

  decide : LEM
  decide = AC→LEM choose
