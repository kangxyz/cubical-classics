{-

Ordered Heyting field structure for constructive Dedekind completions

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.DedekindCompletion.Arithmetic.OrderedHeytingField where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.Algebra.OrderedCommRing

import Constructive.Algebra.OrderedHeytingField.Base as OrderedHeytingField
open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedean
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.DedekindCompletion
open import Constructive.DedekindCompletion.Arithmetic.Base
open import Constructive.DedekindCompletion.Arithmetic.Multiplication
open import Constructive.DedekindCompletion.Arithmetic.Order
open import Constructive.DedekindCompletion.Arithmetic.OrderedCommRing
open import Constructive.DedekindCompletion.Arithmetic.Inverse

private
  variable
    ℓ ℓ' ℓᴾ : Level


module OrderedHeytingFieldStructure
  (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') {ℓᴾ : Level} where

  baseField : LinearlyOrderedField ℓ ℓ'
  baseField = 𝒜 .fst

  private
    ℓ≤ : Level
    ℓ≤ = ℓ-max ℓ (ℓ-max ℓ' ℓᴾ)

    ℓ𝔻 : Level
    ℓ𝔻 = ℓ-suc ℓ≤

  open CompletionBase baseField
  module CutOrder = CompletionOrder baseField
  open CutOrder using (_#_)

  open ArithmeticBase 𝒜
  open Addition {ℓᴾ}
  open Multiplication 𝒜 {ℓᴾ}
  open OrderProperties 𝒜 {ℓᴾ}
  open OrderedCommRingStructure 𝒜 {ℓᴾ}
  open Inverse 𝒜 {ℓᴾ} public
    using (inv#)

  orderedCommRing : OrderedCommRing ℓ𝔻 ℓ≤
  orderedCommRing = DedekindCompletionOrderedCommRing

  DedekindCompletionIsHeytingFieldOnOrderedCommRing :
    OrderedHeytingField.IsHeytingFieldOnOrderedCommRing DedekindCompletionOrderedCommRing
  DedekindCompletionIsHeytingFieldOnOrderedCommRing
    .OrderedHeytingField.IsHeytingFieldOnOrderedCommRing.inv# =
      inv#

  DedekindCompletionOrderedHeytingField :
    OrderedHeytingField.OrderedHeytingField ℓ𝔻 ℓ≤
  DedekindCompletionOrderedHeytingField =
    DedekindCompletionOrderedCommRing ,
    DedekindCompletionIsHeytingFieldOnOrderedCommRing

  ·-lInv#' :
    (x : DedekindCompletion ℓᴾ) →
    x # 0𝔻 →
    Σ[ y ∈ DedekindCompletion ℓᴾ ] y *𝔻 x ≡ 1𝔻
  ·-lInv#' x x#0 =
    y , *𝔻-comm y x ∙ y-right
    where
    y : DedekindCompletion ℓᴾ
    y = inv# x x#0 .fst

    y-right : x *𝔻 y ≡ 1𝔻
    y-right = inv# x x#0 .snd

  0#1 : 0𝔻 # 1𝔻
  0#1 = Sum.inl 0𝔻<1𝔻
