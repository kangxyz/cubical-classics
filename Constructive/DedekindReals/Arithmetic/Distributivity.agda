{-

Full signed distributivity for constructive Dedekind-real multiplication

The proof avoids trichotomy of reals.  It rewrites each right factor as
`z+ - z-`, distributes over the nonnegative factors separately, and then uses
additive-group algebra.

-}
{-# OPTIONS --safe #-}
module Constructive.DedekindReals.Arithmetic.Distributivity where

open import Cubical.Foundations.Prelude

open import Constructive.DedekindReals
open import Constructive.DedekindReals.Arithmetic.Base
open import Constructive.DedekindReals.Arithmetic.AdditiveGroup
open import Constructive.DedekindReals.Arithmetic.Difference


module MultiplicationDistributivity {ℓ : Level} where
  open Algebra {ℓ}
  open Addition {ℓ}
  open NonNegativeMultiplication {ℓ}
  open Multiplication {ℓ}
  open AdditiveGroup {ℓ}
  open DifferenceProperties {ℓ}

  *-right-decomposition-form :
    (x z : DedekindReal ℓ) →
    (x * posPart z) + (- (x * negPart z)) ≡ x * z
  *-right-decomposition-form x z =
    cong₂ _+_
      (*-r≥0-form x (posPart z) (posPart≥0 z))
      (cong -_
        (*-r≥0-form x (negPart z) (negPart≥0 z))) ∙
    algebra-path
    where
    A : DedekindReal ℓ
    A =
      nnMul (posPart x) (posPart z)
        (posPart≥0 x)
        (posPart≥0 z)

    B : DedekindReal ℓ
    B =
      nnMul (negPart x) (negPart z)
        (negPart≥0 x)
        (negPart≥0 z)

    C : DedekindReal ℓ
    C =
      nnMul (posPart x) (negPart z)
        (posPart≥0 x)
        (negPart≥0 z)

    D : DedekindReal ℓ
    D =
      nnMul (negPart x) (posPart z)
        (negPart≥0 x)
        (posPart≥0 z)

    algebra-path :
      (A + (- D)) + (- (C + (- B))) ≡ (A + B) + (- (C + D))
    algebra-path =
      cong ((A + (- D)) +_) (neg-difference-swap C B) ∙
      sum-differences A D B C ∙
      cong ((A + B) +_) (cong -_ (+-comm D C))

  *-right-decomposition :
    (x z : DedekindReal ℓ) →
    x * z ≡ (x * posPart z) + (- (x * negPart z))
  *-right-decomposition x z =
    sym (*-right-decomposition-form x z)

  *-distribR :
    (x y z : DedekindReal ℓ) →
    (x + y) * z ≡ (x * z) + (y * z)
  *-distribR x y z =
    *-right-decomposition (x + y) z ∙
    cong₂ _+_
      (*-distribR-≥0 x y (posPart z) (posPart≥0 z))
      (cong -_
        (*-distribR-≥0 x y (negPart z) (negPart≥0 z))) ∙
    sym
      (sum-differences
        (x * posPart z)
        (x * negPart z)
        (y * posPart z)
        (y * negPart z)) ∙
    cong₂ _+_
      (*-right-decomposition-form x z)
      (*-right-decomposition-form y z)

  *-distribL :
    (x y z : DedekindReal ℓ) →
    x * (y + z) ≡ (x * y) + (x * z)
  *-distribL x y z =
    *-comm x (y + z) ∙
    *-distribR y z x ∙
    cong₂ _+_ (*-comm y x) (*-comm z x)
