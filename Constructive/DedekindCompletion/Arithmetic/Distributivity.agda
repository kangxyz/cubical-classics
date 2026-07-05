{-

Signed distributivity for constructive Dedekind-completion multiplication

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.DedekindCompletion.Arithmetic.Distributivity where

open import Cubical.Foundations.Prelude

open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedean
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.DedekindCompletion
open import Constructive.DedekindCompletion.Arithmetic.Base
open import Constructive.DedekindCompletion.Arithmetic.Negation
open import Constructive.DedekindCompletion.Arithmetic.AdditiveGroup
open import Constructive.DedekindCompletion.Arithmetic.NonNegative
open import Constructive.DedekindCompletion.Arithmetic.Multiplication
open import Constructive.DedekindCompletion.Arithmetic.Difference

private
  variable
    ℓ ℓ' ℓᴾ : Level


module MultiplicationDistributivity
  (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') {ℓᴾ : Level} where

  baseField : LinearlyOrderedField ℓ ℓ'
  baseField = 𝒜 .fst

  open CompletionBase baseField
  open ArithmeticBase 𝒜
  open Addition {ℓᴾ}
  open Negation 𝒜 {ℓᴾ}
  open AdditiveGroup 𝒜 {ℓᴾ}
  open NonNegativeMultiplication 𝒜 {ℓᴾ}
  open Multiplication 𝒜 {ℓᴾ}
  open DifferenceProperties 𝒜 {ℓᴾ}

  *𝔻-right-decomposition-form :
    (x z : DedekindCompletion ℓᴾ) →
    (x *𝔻 posPart z) +𝔻 (-𝔻 (x *𝔻 negPart z)) ≡ x *𝔻 z
  *𝔻-right-decomposition-form x z =
    cong₂ _+𝔻_
      (*𝔻-r≥0-form x (posPart z) (posPart≥0 z))
      (cong -𝔻_
        (*𝔻-r≥0-form x (negPart z) (negPart≥0 z))) ∙
    algebra-path
    where
    A : DedekindCompletion ℓᴾ
    A =
      nnMul (posPart x) (posPart z)
        (posPart≥0 x)
        (posPart≥0 z)

    B : DedekindCompletion ℓᴾ
    B =
      nnMul (negPart x) (negPart z)
        (negPart≥0 x)
        (negPart≥0 z)

    C : DedekindCompletion ℓᴾ
    C =
      nnMul (posPart x) (negPart z)
        (posPart≥0 x)
        (negPart≥0 z)

    D : DedekindCompletion ℓᴾ
    D =
      nnMul (negPart x) (posPart z)
        (negPart≥0 x)
        (posPart≥0 z)

    algebra-path :
      (A +𝔻 (-𝔻 D)) +𝔻 (-𝔻 (C +𝔻 (-𝔻 B)))
      ≡
      (A +𝔻 B) +𝔻 (-𝔻 (C +𝔻 D))
    algebra-path =
      cong ((A +𝔻 (-𝔻 D)) +𝔻_) (neg-difference-swap C B) ∙
      sum-differences A D B C ∙
      cong ((A +𝔻 B) +𝔻_) (cong -𝔻_ (+-comm D C))

  *𝔻-right-decomposition :
    (x z : DedekindCompletion ℓᴾ) →
    x *𝔻 z ≡ (x *𝔻 posPart z) +𝔻 (-𝔻 (x *𝔻 negPart z))
  *𝔻-right-decomposition x z =
    sym (*𝔻-right-decomposition-form x z)

  *𝔻-distribR :
    (x y z : DedekindCompletion ℓᴾ) →
    (x +𝔻 y) *𝔻 z ≡ (x *𝔻 z) +𝔻 (y *𝔻 z)
  *𝔻-distribR x y z =
    *𝔻-right-decomposition (x +𝔻 y) z ∙
    cong₂ _+𝔻_
      (*𝔻-distribR-≥0 x y (posPart z) (posPart≥0 z))
      (cong -𝔻_
        (*𝔻-distribR-≥0 x y (negPart z) (negPart≥0 z))) ∙
    sym
      (sum-differences
        (x *𝔻 posPart z)
        (x *𝔻 negPart z)
        (y *𝔻 posPart z)
        (y *𝔻 negPart z)) ∙
    cong₂ _+𝔻_
      (*𝔻-right-decomposition-form x z)
      (*𝔻-right-decomposition-form y z)

  *𝔻-distribL :
    (x y z : DedekindCompletion ℓᴾ) →
    x *𝔻 (y +𝔻 z) ≡ (x *𝔻 y) +𝔻 (x *𝔻 z)
  *𝔻-distribL x y z =
    *𝔻-comm x (y +𝔻 z) ∙
    *𝔻-distribR y z x ∙
    cong₂ _+𝔻_ (*𝔻-comm y x) (*𝔻-comm z x)
