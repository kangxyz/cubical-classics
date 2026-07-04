{-

Full signed distributivity for constructive Dedekind-cut multiplication.

The proof avoids trichotomy of reals.  It rewrites every right factor as
`z+ - z-`, distributes over the nonnegative factors separately, and then uses
additive-group algebra.

-}
{-# OPTIONS --safe #-}
module Cubical.DedekindCut.Arithmetic.Distributivity where

open import Cubical.Foundations.Prelude

open import Cubical.DedekindCut
open import Cubical.DedekindCut.Arithmetic
open import Cubical.DedekindCut.Arithmetic.AdditiveGroup
open import Cubical.DedekindCut.Arithmetic.Difference


module SignedDistributivity {ℓ : Level} where
  open Algebra {ℓ}
  open Addition {ℓ}
  open NonnegativeMultiplication {ℓ}
  open SignedMultiplication {ℓ}
  open AdditiveGroup {ℓ}
  open DifferenceMultiplication {ℓ}

  *-right-decomposition-form :
    (x z : DedekindCut ℓ) →
    (x * positivePart z) + (- (x * negativePart z)) ≡ x * z
  *-right-decomposition-form x z =
    cong₂ _+_
      (*-right-nonnegative-form x (positivePart z) (positivePart-nonnegative z))
      (cong -_
        (*-right-nonnegative-form x (negativePart z) (negativePart-nonnegative z))) ∙
    algebra-path
    where
    A : DedekindCut ℓ
    A =
      nnMul (positivePart x) (positivePart z)
        (positivePart-nonnegative x)
        (positivePart-nonnegative z)

    B : DedekindCut ℓ
    B =
      nnMul (negativePart x) (negativePart z)
        (negativePart-nonnegative x)
        (negativePart-nonnegative z)

    C : DedekindCut ℓ
    C =
      nnMul (positivePart x) (negativePart z)
        (positivePart-nonnegative x)
        (negativePart-nonnegative z)

    D : DedekindCut ℓ
    D =
      nnMul (negativePart x) (positivePart z)
        (negativePart-nonnegative x)
        (positivePart-nonnegative z)

    algebra-path :
      (A + (- D)) + (- (C + (- B))) ≡ (A + B) + (- (C + D))
    algebra-path =
      cong ((A + (- D)) +_) (neg-difference-swap C B) ∙
      sum-differences A D B C ∙
      cong ((A + B) +_) (cong -_ (+-comm D C))

  *-right-decomposition :
    (x z : DedekindCut ℓ) →
    x * z ≡ (x * positivePart z) + (- (x * negativePart z))
  *-right-decomposition x z =
    sym (*-right-decomposition-form x z)

  *-distribR :
    (x y z : DedekindCut ℓ) →
    (x + y) * z ≡ (x * z) + (y * z)
  *-distribR x y z =
    *-right-decomposition (x + y) z ∙
    cong₂ _+_
      (*-distribR-nonnegative x y (positivePart z) (positivePart-nonnegative z))
      (cong -_
        (*-distribR-nonnegative x y (negativePart z) (negativePart-nonnegative z))) ∙
    sym
      (sum-differences
        (x * positivePart z)
        (x * negativePart z)
        (y * positivePart z)
        (y * negativePart z)) ∙
    cong₂ _+_
      (*-right-decomposition-form x z)
      (*-right-decomposition-form y z)

  *-distribL :
    (x y z : DedekindCut ℓ) →
    x * (y + z) ≡ (x * y) + (x * z)
  *-distribL x y z =
    *-comm x (y + z) ∙
    *-distribR y z x ∙
    cong₂ _+_ (*-comm y x) (*-comm z x)

