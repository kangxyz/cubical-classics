{-

Constructive apartness-field packaging for Dedekind cuts.

Cubical's `Field` record asks for inverses from mere inequality `x != 0`.
Constructively, Dedekind reals provide inverses from apartness `x # 0`
instead.  This module packages exactly that LEM-free field content together
with the ordered commutative ring from M3.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.DedekindCut.Arithmetic.ApartnessField where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.Algebra.OrderedCommRing

open import Constructive.Algebra.OrderedField
open import Cubical.DedekindCut
open import Cubical.DedekindCut.Arithmetic
open import Cubical.DedekindCut.Arithmetic.OrderedCommRing
open import Cubical.DedekindCut.Arithmetic.PositiveInverse

module DedekindApartnessField {ℓ : Level} where
  open Order {ℓ}
  open RationalEmbeddingAt {ℓ}
  open Addition {ℓ}
  open SignedMultiplication {ℓ}
  open DedekindOrderedCommRing {ℓ}
  open PositiveInverse {ℓ}

  orderedCommRing : OrderedCommRing (ℓ-suc ℓ) ℓ
  orderedCommRing = DedekindCutOrderedCommRing

  inverse#-left' :
    (x : DedekindCut ℓ) →
    x # 0D →
    Σ[ y ∈ DedekindCut ℓ ] y * x ≡ 1D
  inverse#-left' x x#0 =
    y , *-comm y x ∙ y-right
    where
    y : DedekindCut ℓ
    y = inverse# x x#0 .fst

    y-right : x * y ≡ 1D
    y-right = inverse# x x#0 .snd

  0#1 : 0D # 1D
  0#1 = Sum.inl 0<1-cut

  DedekindCutIsOrderedField : IsOrderedField DedekindCutOrderedCommRing
  DedekindCutIsOrderedField .IsOrderedField.inverse# =
    inverse#
  DedekindCutIsOrderedField .IsOrderedField.0#1 =
    0#1

  DedekindCutOrderedField : OrderedField (ℓ-suc ℓ) ℓ
  DedekindCutOrderedField =
    DedekindCutOrderedCommRing , DedekindCutIsOrderedField
