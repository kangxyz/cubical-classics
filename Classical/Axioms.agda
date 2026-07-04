{-# OPTIONS --safe #-}
module Classical.Axioms where

open import Cubical.Foundations.Prelude
import Cubical.Axiom.ExcludedMiddle as CubicalEM

open import Classical.Axioms.Choice public
open import Classical.Axioms.ExcludedMiddle public

-- We record up axioms to make use of Agda's instance argument,
-- so no one needs to write them everywhere explicitly.

----------------------------------------------

-- Here the oracle is named 🤖:
-- where silent propositions choose their way,
-- and h-level shadows split into day.

-- Summon it with
-- `module _ ⦃ 🤖 : Oracle ⦄ where`;
-- open the record, and waiting there,
-- `decide : LEM` will answer fair.

-- by ChatGPT, under human supervision

----------------------------------------------

-- Examples are almost all files in this library.

record Oracle : Typeω where
  field
    decide : LEM

AC→LEM : AC → LEM
AC→LEM choose {ℓ} = CubicalEM.Diaconescu ℓ λ X → choose X

----------------------------------------------

-- Warning:

-- 🤖 may tell which side is true,
-- but not the witness meant for you.
-- It parts the dark, it clears the view;
-- the proof itself remains to do.

-- by ChatGPT, under human supervision

----------------------------------------------

record MegaPicker : Typeω where
  field
    choose : AC

  decide : LEM
  decide = AC→LEM choose
