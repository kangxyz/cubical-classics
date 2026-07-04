{-

Constructive apartness-field packaging for Dedekind cuts.

Cubical's `Field` record asks for inverses from mere inequality `x != 0`.
Constructively, Dedekind reals provide inverses from apartness `x # 0`
instead.  This module packages exactly that LEM-free field content together
with the ordered commutative ring from M3.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.DedekindCut.Arithmetic.OrderedField where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.Algebra.OrderedCommRing

open import Constructive.Algebra.OrderedField
open import Cubical.DedekindCut
open import Cubical.DedekindCut.Arithmetic
open import Cubical.DedekindCut.Arithmetic.OrderedCommRing
open import Cubical.DedekindCut.Arithmetic.Inverse

module OrderedFieldStructure {ℓ : Level} where
  open Order {ℓ}
  open RationalEmbedding {ℓ}
  open Addition {ℓ}
  open Multiplication {ℓ}
  open OrderedCommRingStructure {ℓ}
  open Inverse {ℓ}

  orderedCommRing : OrderedCommRing (ℓ-suc ℓ) ℓ
  orderedCommRing = DedekindOrderedCommRing

  ·-lInv#' :
    (x : DedekindCut ℓ) →
    x # 0𝔻 →
    Σ[ y ∈ DedekindCut ℓ ] y * x ≡ 1𝔻
  ·-lInv#' x x#0 =
    y , *-comm y x ∙ y-right
    where
    y : DedekindCut ℓ
    y = inv# x x#0 .fst

    y-right : x * y ≡ 1𝔻
    y-right = inv# x x#0 .snd

  0#1 : 0𝔻 # 1𝔻
  0#1 = Sum.inl 0𝔻<1𝔻

  DedekindIsOrderedField : IsOrderedField DedekindOrderedCommRing
  DedekindIsOrderedField .IsOrderedField.inv# =
    inv#
  DedekindIsOrderedField .IsOrderedField.0#1 =
    0#1

  DedekindOrderedField : OrderedField (ℓ-suc ℓ) ℓ
  DedekindOrderedField =
    DedekindOrderedCommRing , DedekindIsOrderedField
