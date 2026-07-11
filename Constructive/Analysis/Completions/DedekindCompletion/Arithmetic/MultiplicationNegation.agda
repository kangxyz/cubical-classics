{-

Interaction of multiplication and negation on Dedekind completions

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.MultiplicationNegation where

open import Cubical.Foundations.Prelude

open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedean
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.Analysis.Completions.DedekindCompletion.Base
open import Constructive.Analysis.Completions.DedekindCompletion.Order
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Addition
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Negation
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.NonnegativeProduct
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Multiplication

private
  variable
    ℓ ℓ' ℓᴾ : Level


module MultiplicationNegation
  (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') {ℓᴾ : Level} where

  baseField : LinearlyOrderedField ℓ ℓ'
  baseField = 𝒜 .fst

  open CompletionBase baseField
  module CutOrder = CompletionOrder baseField
  open CutOrder using (_⊔_)

  open Addition 𝒜 {ℓᴾ}
  open Negation 𝒜 {ℓᴾ}
  open AdditiveGroup 𝒜 {ℓᴾ}
  open NonnegativeProduct 𝒜 {ℓᴾ}
  open Multiplication 𝒜 {ℓᴾ}

  posPart-neg :
    (x : DedekindCompletion ℓᴾ) →
    posPart (-𝔻 x) ≡ negPart x
  posPart-neg x = refl

  negPart-neg :
    (x : DedekindCompletion ℓᴾ) →
    negPart (-𝔻 x) ≡ posPart x
  negPart-neg x =
    cong (λ z → z ⊔ 0𝔻) (neg-involutive x)

  posProducts-negL :
    (x y : DedekindCompletion ℓᴾ) →
    posProducts (-𝔻 x) y ≡ negProducts x y
  posProducts-negL x y =
    cong₂ _+𝔻_ first second ∙
    +-comm
      (nnMul (negPart x) (posPart y)
        (negPart≥0 x)
        (posPart≥0 y))
      (nnMul (posPart x) (negPart y)
        (posPart≥0 x)
        (negPart≥0 y))
    where
    first :
      nnMul (posPart (-𝔻 x)) (posPart y)
        (posPart≥0 (-𝔻 x))
        (posPart≥0 y)
      ≡
      nnMul (negPart x) (posPart y)
        (negPart≥0 x)
        (posPart≥0 y)
    first =
      nnMul-congL
        (posPart (-𝔻 x))
        (negPart x)
        (posPart y)
        (posPart-neg x)
        (posPart≥0 (-𝔻 x))
        (negPart≥0 x)
        (posPart≥0 y)
        (posPart≥0 y)

    second :
      nnMul (negPart (-𝔻 x)) (negPart y)
        (negPart≥0 (-𝔻 x))
        (negPart≥0 y)
      ≡
      nnMul (posPart x) (negPart y)
        (posPart≥0 x)
        (negPart≥0 y)
    second =
      nnMul-congL
        (negPart (-𝔻 x))
        (posPart x)
        (negPart y)
        (negPart-neg x)
        (negPart≥0 (-𝔻 x))
        (posPart≥0 x)
        (negPart≥0 y)
        (negPart≥0 y)

  negProducts-negL :
    (x y : DedekindCompletion ℓᴾ) →
    negProducts (-𝔻 x) y ≡ posProducts x y
  negProducts-negL x y =
    cong₂ _+𝔻_ first second ∙
    +-comm
      (nnMul (negPart x) (negPart y)
        (negPart≥0 x)
        (negPart≥0 y))
      (nnMul (posPart x) (posPart y)
        (posPart≥0 x)
        (posPart≥0 y))
    where
    first :
      nnMul (posPart (-𝔻 x)) (negPart y)
        (posPart≥0 (-𝔻 x))
        (negPart≥0 y)
      ≡
      nnMul (negPart x) (negPart y)
        (negPart≥0 x)
        (negPart≥0 y)
    first =
      nnMul-congL
        (posPart (-𝔻 x))
        (negPart x)
        (negPart y)
        (posPart-neg x)
        (posPart≥0 (-𝔻 x))
        (negPart≥0 x)
        (negPart≥0 y)
        (negPart≥0 y)

    second :
      nnMul (negPart (-𝔻 x)) (posPart y)
        (negPart≥0 (-𝔻 x))
        (posPart≥0 y)
      ≡
      nnMul (posPart x) (posPart y)
        (posPart≥0 x)
        (posPart≥0 y)
    second =
      nnMul-congL
        (negPart (-𝔻 x))
        (posPart x)
        (posPart y)
        (negPart-neg x)
        (negPart≥0 (-𝔻 x))
        (posPart≥0 x)
        (posPart≥0 y)
        (posPart≥0 y)

  *𝔻-negL :
    (x y : DedekindCompletion ℓᴾ) →
    (-𝔻 x) *𝔻 y ≡ -𝔻 (x *𝔻 y)
  *𝔻-negL x y =
    cong₂ _+𝔻_
      (posProducts-negL x y)
      (cong -𝔻_ (negProducts-negL x y)) ∙
    sym (neg-difference-swap (posProducts x y) (negProducts x y))

  *𝔻-negR :
    (x y : DedekindCompletion ℓᴾ) →
    x *𝔻 (-𝔻 y) ≡ -𝔻 (x *𝔻 y)
  *𝔻-negR x y =
    *𝔻-comm x (-𝔻 y) ∙
    *𝔻-negL y x ∙
    cong -𝔻_ (*𝔻-comm y x)

  *𝔻-negL-negR :
    (x y : DedekindCompletion ℓᴾ) →
    (-𝔻 x) *𝔻 (-𝔻 y) ≡ x *𝔻 y
  *𝔻-negL-negR x y =
    *𝔻-negL x (-𝔻 y) ∙
    cong -𝔻_ (*𝔻-negR x y) ∙
    neg-involutive (x *𝔻 y)
