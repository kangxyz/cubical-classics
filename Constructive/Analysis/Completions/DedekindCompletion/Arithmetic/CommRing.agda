{-

Commutative ring structure for constructive Dedekind completions

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.CommRing where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing

open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedean
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.Analysis.Completions.DedekindCompletion
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Base
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Negation
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Multiplication
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Unit
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Distributivity
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Associativity

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
  open ArithmeticBase 𝒜
  open Addition {ℓᴾ}
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
