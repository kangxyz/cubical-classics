{-

Cauchy-real sequences with explicit moduli

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Sequences.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)

open import Constructive.Analysis.Reals.CauchyReals.Base


Sequence : Type₀
Sequence =
  ℕ → ℝᶜ


constantSequence : ℝᶜ → Sequence
constantSequence x _ =
  x
