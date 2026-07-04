{-

Compatibility of constructive Dedekind-cut multiplication with negation.

The signed multiplication in Cubical.DedekindCut.Arithmetic is defined through
positive and negative parts.  These lemmas make the expected sign laws
available without any trichotomy.

-}
{-# OPTIONS --safe #-}
module Cubical.DedekindCut.Arithmetic.Negation where

open import Cubical.Foundations.Prelude

open import Cubical.DedekindCut
open import Cubical.DedekindCut.Arithmetic
open import Cubical.DedekindCut.Arithmetic.AdditiveGroup


module NegationProperties {ℓ : Level} where
  open Algebra {ℓ}
  open Lattice {ℓ}
  open Addition {ℓ}
  open NonNegativeMultiplication {ℓ}
  open Multiplication {ℓ}
  open AdditiveGroup {ℓ}

  posPart-neg :
    (x : DedekindCut ℓ) →
    posPart (- x) ≡ negPart x
  posPart-neg x = refl

  negPart-neg :
    (x : DedekindCut ℓ) →
    negPart (- x) ≡ posPart x
  negPart-neg x =
    cong (λ z → z ⊔ 0𝔻) (neg-involutive x)

  posProducts-negL :
    (x y : DedekindCut ℓ) →
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
    (x y : DedekindCut ℓ) →
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
    (x y : DedekindCut ℓ) →
    (- x) * y ≡ - (x * y)
  *-negL x y =
    cong₂ _+_
      (posProducts-negL x y)
      (cong -_ (negProducts-negL x y)) ∙
    sym (neg-difference-swap (posProducts x y) (negProducts x y))

  *-negR :
    (x y : DedekindCut ℓ) →
    x * (- y) ≡ - (x * y)
  *-negR x y =
    *-comm x (- y) ∙
    *-negL y x ∙
    cong -_ (*-comm y x)

  *-negL-negR :
    (x y : DedekindCut ℓ) →
    (- x) * (- y) ≡ x * y
  *-negL-negR x y =
    *-negL x (- y) ∙
    cong -_ (*-negR x y) ∙
    neg-involutive (x * y)

