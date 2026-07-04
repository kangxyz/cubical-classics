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


module MultiplicationNegation {ℓ : Level} where
  open Algebra {ℓ}
  open Lattice {ℓ}
  open Addition {ℓ}
  open NonnegativeMultiplication {ℓ}
  open SignedMultiplication {ℓ}
  open AdditiveGroup {ℓ}

  positivePart-neg :
    (x : DedekindCut ℓ) →
    positivePart (- x) ≡ negativePart x
  positivePart-neg x = refl

  negativePart-neg :
    (x : DedekindCut ℓ) →
    negativePart (- x) ≡ positivePart x
  negativePart-neg x =
    cong (λ z → z ⊔ 0D) (neg-involutive x)

  positiveProducts-negL :
    (x y : DedekindCut ℓ) →
    positiveProducts (- x) y ≡ negativeProducts x y
  positiveProducts-negL x y =
    cong₂ _+_ first second ∙
    +-comm
      (nnMul (negativePart x) (positivePart y)
        (negativePart-nonnegative x)
        (positivePart-nonnegative y))
      (nnMul (positivePart x) (negativePart y)
        (positivePart-nonnegative x)
        (negativePart-nonnegative y))
    where
    first :
      nnMul (positivePart (- x)) (positivePart y)
        (positivePart-nonnegative (- x))
        (positivePart-nonnegative y)
      ≡
      nnMul (negativePart x) (positivePart y)
        (negativePart-nonnegative x)
        (positivePart-nonnegative y)
    first =
      nnMul-congL
        (positivePart (- x))
        (negativePart x)
        (positivePart y)
        (positivePart-neg x)
        (positivePart-nonnegative (- x))
        (negativePart-nonnegative x)
        (positivePart-nonnegative y)
        (positivePart-nonnegative y)

    second :
      nnMul (negativePart (- x)) (negativePart y)
        (negativePart-nonnegative (- x))
        (negativePart-nonnegative y)
      ≡
      nnMul (positivePart x) (negativePart y)
        (positivePart-nonnegative x)
        (negativePart-nonnegative y)
    second =
      nnMul-congL
        (negativePart (- x))
        (positivePart x)
        (negativePart y)
        (negativePart-neg x)
        (negativePart-nonnegative (- x))
        (positivePart-nonnegative x)
        (negativePart-nonnegative y)
        (negativePart-nonnegative y)

  negativeProducts-negL :
    (x y : DedekindCut ℓ) →
    negativeProducts (- x) y ≡ positiveProducts x y
  negativeProducts-negL x y =
    cong₂ _+_ first second ∙
    +-comm
      (nnMul (negativePart x) (negativePart y)
        (negativePart-nonnegative x)
        (negativePart-nonnegative y))
      (nnMul (positivePart x) (positivePart y)
        (positivePart-nonnegative x)
        (positivePart-nonnegative y))
    where
    first :
      nnMul (positivePart (- x)) (negativePart y)
        (positivePart-nonnegative (- x))
        (negativePart-nonnegative y)
      ≡
      nnMul (negativePart x) (negativePart y)
        (negativePart-nonnegative x)
        (negativePart-nonnegative y)
    first =
      nnMul-congL
        (positivePart (- x))
        (negativePart x)
        (negativePart y)
        (positivePart-neg x)
        (positivePart-nonnegative (- x))
        (negativePart-nonnegative x)
        (negativePart-nonnegative y)
        (negativePart-nonnegative y)

    second :
      nnMul (negativePart (- x)) (positivePart y)
        (negativePart-nonnegative (- x))
        (positivePart-nonnegative y)
      ≡
      nnMul (positivePart x) (positivePart y)
        (positivePart-nonnegative x)
        (positivePart-nonnegative y)
    second =
      nnMul-congL
        (negativePart (- x))
        (positivePart x)
        (positivePart y)
        (negativePart-neg x)
        (negativePart-nonnegative (- x))
        (positivePart-nonnegative x)
        (positivePart-nonnegative y)
        (positivePart-nonnegative y)

  *-negL :
    (x y : DedekindCut ℓ) →
    (- x) * y ≡ - (x * y)
  *-negL x y =
    cong₂ _+_
      (positiveProducts-negL x y)
      (cong -_ (negativeProducts-negL x y)) ∙
    sym (neg-difference-swap (positiveProducts x y) (negativeProducts x y))

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

