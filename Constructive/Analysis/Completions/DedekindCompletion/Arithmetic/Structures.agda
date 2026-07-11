{-

Algebraic structures on constructive Dedekind completions

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Structures where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Nullary

import Constructive.Algebra.OrderedHeytingField.Base as OrderedHeytingField
open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedean
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.Analysis.Completions.DedekindCompletion.Base
open import Constructive.Analysis.Completions.DedekindCompletion.Order
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Addition
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Negation
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Multiplication
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Unit
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Distributivity
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Associativity
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Order
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Inverse

private
  variable
    ℓ ℓ' ℓᴾ : Level


module CommRingStructure
  (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') {ℓᴾ : Level} where

  baseField : LinearlyOrderedField ℓ ℓ'
  baseField = 𝒜 .fst

  private
    ℓ𝔻 : Level
    ℓ𝔻 = ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))

  open CompletionBase baseField
  open Addition 𝒜 {ℓᴾ}
  open Negation 𝒜 {ℓᴾ}
  open AdditiveGroup 𝒜 {ℓᴾ}
  open Multiplication 𝒜 {ℓᴾ}
  open UnitProperties 𝒜 {ℓᴾ}
  open MultiplicationDistributivity 𝒜 {ℓᴾ}
  open MultiplicationAssociativity 𝒜 {ℓᴾ}

  DedekindCompletionCommRing : CommRing ℓ𝔻
  DedekindCompletionCommRing =
    makeCommRing
      0𝔻
      1𝔻
      _+𝔻_
      _*𝔻_
      -𝔻_
      isSetDedekindCompletion
      +-assoc
      +-idR
      +-invR
      +-comm
      (λ x y z → sym (*𝔻-assoc x y z))
      *𝔻-idR
      *𝔻-distribL
      *𝔻-comm


module OrderedCommRingStructure
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
  open CutOrder
    using
      ( isStrictOrder< ; isProp≤ ; ≤→¬> ; ¬>→≤
      ; <-≤-trans ; ≤-<-trans ; <→≤
      ; DedekindCompletion≤Pseudolattice
      )
    renaming
      ( _≤_ to _≤D_
      ; _<_ to _<D_
      )

  open Addition 𝒜 {ℓᴾ}
  open Negation 𝒜 {ℓᴾ}
  open AdditiveGroup 𝒜 {ℓᴾ}
  open Multiplication 𝒜 {ℓᴾ}
  open CommRingStructure 𝒜 {ℓᴾ}
  open OrderProperties 𝒜 {ℓᴾ}

  DedekindCompletionIsOrderedCommRing :
    IsOrderedCommRing 0𝔻 1𝔻 _+𝔻_ _*𝔻_ (-𝔻_) _<D_ _≤D_
  DedekindCompletionIsOrderedCommRing .IsOrderedCommRing.isCommRing =
    DedekindCompletionCommRing .snd .CommRingStr.isCommRing
  DedekindCompletionIsOrderedCommRing .IsOrderedCommRing.isPseudolattice =
    DedekindCompletion≤Pseudolattice {ℓᴾ = ℓᴾ}
      .snd .PseudolatticeStr.is-pseudolattice
  DedekindCompletionIsOrderedCommRing .IsOrderedCommRing.isStrictOrder =
    isStrictOrder<
  DedekindCompletionIsOrderedCommRing .IsOrderedCommRing.<-≤-weaken =
    <→≤
  DedekindCompletionIsOrderedCommRing .IsOrderedCommRing.≤≃¬> =
    λ x y →
      propBiimpl→Equiv (isProp≤ x y) (isProp¬ (y <D x))
        (≤→¬> x y)
        (¬>→≤ x y)
  DedekindCompletionIsOrderedCommRing .IsOrderedCommRing.+MonoR≤ =
    +-monoR-≤
  DedekindCompletionIsOrderedCommRing .IsOrderedCommRing.+MonoR< =
    +-monoR-<
  DedekindCompletionIsOrderedCommRing .IsOrderedCommRing.posSum→pos∨pos =
    posSum→pos∨pos
  DedekindCompletionIsOrderedCommRing .IsOrderedCommRing.<-≤-trans =
    <-≤-trans
  DedekindCompletionIsOrderedCommRing .IsOrderedCommRing.≤-<-trans =
    ≤-<-trans
  DedekindCompletionIsOrderedCommRing .IsOrderedCommRing.·MonoR≤ =
    λ x y z 0≤z x≤y → *𝔻-rPosPres≤ x y z x≤y 0≤z
  DedekindCompletionIsOrderedCommRing .IsOrderedCommRing.·MonoR< =
    *𝔻-rPosPres<
  DedekindCompletionIsOrderedCommRing .IsOrderedCommRing.0<1 =
    0𝔻<1𝔻

  DedekindCompletionOrderedCommRing : OrderedCommRing ℓ𝔻 ℓ≤
  DedekindCompletionOrderedCommRing .fst = DedekindCompletion ℓᴾ
  DedekindCompletionOrderedCommRing .snd =
    orderedcommringstr
      0𝔻
      1𝔻
      _+𝔻_
      _*𝔻_
      (-𝔻_)
      _<D_
      _≤D_
      DedekindCompletionIsOrderedCommRing


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

  open Addition 𝒜 {ℓᴾ}
  open Multiplication 𝒜 {ℓᴾ}
  open OrderProperties 𝒜 {ℓᴾ}
  open OrderedCommRingStructure 𝒜 {ℓᴾ}
  open Inverse 𝒜 {ℓᴾ} public
    using (inv#)

  DedekindCompletionIsHeytingFieldOnOrderedCommRing :
    OrderedHeytingField.IsHeytingFieldOnOrderedCommRing
      DedekindCompletionOrderedCommRing
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
