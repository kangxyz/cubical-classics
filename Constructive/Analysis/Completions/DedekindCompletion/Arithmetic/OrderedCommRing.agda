{-

Ordered commutative ring structure for constructive Dedekind completions

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.OrderedCommRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Nullary

open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedean
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.Analysis.Completions.DedekindCompletion
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Base
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Negation
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Multiplication
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.CommRing
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Order

private
  variable
    ℓ ℓ' ℓᴾ : Level


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

  open ArithmeticBase 𝒜
  open Addition {ℓᴾ}
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
    DedekindCompletion≤Pseudolattice {ℓᴾ = ℓᴾ} .snd .PseudolatticeStr.is-pseudolattice
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
