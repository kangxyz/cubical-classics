{-

Compatibility of constructive Dedekind-real multiplication with negation

Signed multiplication is defined through positive and negative parts.  These
lemmas give the expected sign laws without trichotomy.

-}
{-# OPTIONS --safe #-}
module Constructive.DedekindReals.Arithmetic.Negation where

open import Cubical.Foundations.Prelude

open import Constructive.DedekindReals
open import Constructive.DedekindReals.Arithmetic.Base
open import Constructive.DedekindReals.Arithmetic.AdditiveGroup


module NegationProperties {ℓ : Level} where
  open Algebra {ℓ}
  open Lattice {ℓ}
  open Addition {ℓ}
  open NonNegativeMultiplication {ℓ}
  open Multiplication {ℓ}
  open AdditiveGroup {ℓ}

  posPart-neg :
    (x : DedekindReal ℓ) →
    posPart (- x) ≡ negPart x
  posPart-neg x = refl

  negPart-neg :
    (x : DedekindReal ℓ) →
    negPart (- x) ≡ posPart x
  negPart-neg x =
    cong (λ z → z ⊔ 0𝔻) (neg-involutive x)

  posProducts-negL :
    (x y : DedekindReal ℓ) →
    posProducts (- x) y ≡ negProducts x y
  posProducts-negL x y =
    cong₂ _+_ first second ∙
    +-comm
      (nnMul (negPart x) (posPart y)
        (negPart≥0 x)
        (posPart≥0 y))
      (nnMul (posPart x) (negPart y)
        (posPart≥0 x)
        (negPart≥0 y))
    where
    first :
      nnMul (posPart (- x)) (posPart y)
        (posPart≥0 (- x))
        (posPart≥0 y)
      ≡
      nnMul (negPart x) (posPart y)
        (negPart≥0 x)
        (posPart≥0 y)
    first =
      nnMul-congL
        (posPart (- x))
        (negPart x)
        (posPart y)
        (posPart-neg x)
        (posPart≥0 (- x))
        (negPart≥0 x)
        (posPart≥0 y)
        (posPart≥0 y)

    second :
      nnMul (negPart (- x)) (negPart y)
        (negPart≥0 (- x))
        (negPart≥0 y)
      ≡
      nnMul (posPart x) (negPart y)
        (posPart≥0 x)
        (negPart≥0 y)
    second =
      nnMul-congL
        (negPart (- x))
        (posPart x)
        (negPart y)
        (negPart-neg x)
        (negPart≥0 (- x))
        (posPart≥0 x)
        (negPart≥0 y)
        (negPart≥0 y)

  negProducts-negL :
    (x y : DedekindReal ℓ) →
    negProducts (- x) y ≡ posProducts x y
  negProducts-negL x y =
    cong₂ _+_ first second ∙
    +-comm
      (nnMul (negPart x) (negPart y)
        (negPart≥0 x)
        (negPart≥0 y))
      (nnMul (posPart x) (posPart y)
        (posPart≥0 x)
        (posPart≥0 y))
    where
    first :
      nnMul (posPart (- x)) (negPart y)
        (posPart≥0 (- x))
        (negPart≥0 y)
      ≡
      nnMul (negPart x) (negPart y)
        (negPart≥0 x)
        (negPart≥0 y)
    first =
      nnMul-congL
        (posPart (- x))
        (negPart x)
        (negPart y)
        (posPart-neg x)
        (posPart≥0 (- x))
        (negPart≥0 x)
        (negPart≥0 y)
        (negPart≥0 y)

    second :
      nnMul (negPart (- x)) (posPart y)
        (negPart≥0 (- x))
        (posPart≥0 y)
      ≡
      nnMul (posPart x) (posPart y)
        (posPart≥0 x)
        (posPart≥0 y)
    second =
      nnMul-congL
        (negPart (- x))
        (posPart x)
        (posPart y)
        (negPart-neg x)
        (negPart≥0 (- x))
        (posPart≥0 x)
        (posPart≥0 y)
        (posPart≥0 y)

  *-negL :
    (x y : DedekindReal ℓ) →
    (- x) * y ≡ - (x * y)
  *-negL x y =
    cong₂ _+_
      (posProducts-negL x y)
      (cong -_ (negProducts-negL x y)) ∙
    sym (neg-difference-swap (posProducts x y) (negProducts x y))

  *-negR :
    (x y : DedekindReal ℓ) →
    x * (- y) ≡ - (x * y)
  *-negR x y =
    *-comm x (- y) ∙
    *-negL y x ∙
    cong -_ (*-comm y x)

  *-negL-negR :
    (x y : DedekindReal ℓ) →
    (- x) * (- y) ≡ x * y
  *-negL-negR x y =
    *-negL x (- y) ∙
    cong -_ (*-negR x y) ∙
    neg-involutive (x * y)
