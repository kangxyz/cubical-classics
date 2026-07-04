{-

Full signed associativity for constructive Dedekind-cut multiplication.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.DedekindCut.Arithmetic.Associativity where

open import Cubical.Foundations.Prelude

open import Cubical.DedekindCut
open import Cubical.DedekindCut.Arithmetic
open import Cubical.DedekindCut.Arithmetic.AdditiveGroup
open import Cubical.DedekindCut.Arithmetic.Difference
open import Cubical.DedekindCut.Arithmetic.Distributivity
open import Cubical.DedekindCut.Arithmetic.Negation
open import Cubical.DedekindCut.Arithmetic.NonnegativeLaws


module SignedAssociativity {ℓ : Level} where
  open Algebra {ℓ}
  open Addition {ℓ}
  open NonnegativeMultiplication {ℓ}
  open SignedMultiplication {ℓ}
  open AdditiveGroup {ℓ}
  open DifferenceMultiplication {ℓ}
  open SignedDistributivity {ℓ}
  open MultiplicationNegation {ℓ}
  open NonnegativeLaws {ℓ}

  *-assoc-two-right-nonnegative :
    (x a n : DedekindCut ℓ) →
    (0≤a : Nonnegative a) →
    (0≤n : Nonnegative n) →
    (x * a) * n ≡ x * (nnMul a n 0≤a 0≤n)
  *-assoc-two-right-nonnegative x a n 0≤a 0≤n =
    cong (_* n) (*-right-nonnegative-form x a 0≤a) ∙
    *-distribR-nonnegative
      (nnMul (positivePart x) a (positivePart-nonnegative x) 0≤a)
      (- nnMul (negativePart x) a (negativePart-nonnegative x) 0≤a)
      n
      0≤n ∙
    cong₂ _+_
      left-assoc
      (cong (_* n) refl ∙
       *-negL (nnMul (negativePart x) a (negativePart-nonnegative x) 0≤a) n ∙
       cong -_ right-assoc) ∙
    sym (*-right-nonnegative-form x (nnMul a n 0≤a 0≤n) 0≤an)
    where
    0≤an : Nonnegative (nnMul a n 0≤a 0≤n)
    0≤an = nnMul-nonnegative a n 0≤a 0≤n

    left-assoc :
      nnMul (positivePart x) a (positivePart-nonnegative x) 0≤a * n
      ≡
      nnMul (positivePart x) (nnMul a n 0≤a 0≤n)
        (positivePart-nonnegative x)
        0≤an
    left-assoc =
      *-of-nonnegative
        (nnMul (positivePart x) a (positivePart-nonnegative x) 0≤a)
        n
        (nnMul-nonnegative (positivePart x) a (positivePart-nonnegative x) 0≤a)
        0≤n ∙
      sym
        (nnMul-assoc
          (positivePart x)
          a
          n
          (positivePart-nonnegative x)
          0≤a
          0≤n)

    right-assoc :
      nnMul (negativePart x) a (negativePart-nonnegative x) 0≤a * n
      ≡
      nnMul (negativePart x) (nnMul a n 0≤a 0≤n)
        (negativePart-nonnegative x)
        0≤an
    right-assoc =
      *-of-nonnegative
        (nnMul (negativePart x) a (negativePart-nonnegative x) 0≤a)
        n
        (nnMul-nonnegative (negativePart x) a (negativePart-nonnegative x) 0≤a)
        0≤n ∙
      sym
        (nnMul-assoc
          (negativePart x)
          a
          n
          (negativePart-nonnegative x)
          0≤a
          0≤n)

  *-assocR-nonnegative :
    (x y n : DedekindCut ℓ) →
    (0≤n : Nonnegative n) →
    (x * y) * n ≡ x * (y * n)
  *-assocR-nonnegative x y n 0≤n =
    cong (_* n) (*-right-decomposition x y) ∙
    *-distribR-nonnegative
      (x * positivePart y)
      (- (x * negativePart y))
      n
      0≤n ∙
    cong₂ _+_
      (*-assoc-two-right-nonnegative x (positivePart y) n
        (positivePart-nonnegative y)
        0≤n)
      (*-negL (x * negativePart y) n ∙
       cong -_
        (*-assoc-two-right-nonnegative x (negativePart y) n
          (negativePart-nonnegative y)
          0≤n)) ∙
    distrib-back ∙
    cong (x *_) (sym (*-right-nonnegative-form y n 0≤n))
    where
    yn+ : DedekindCut ℓ
    yn+ =
      nnMul (positivePart y) n
        (positivePart-nonnegative y)
        0≤n

    yn- : DedekindCut ℓ
    yn- =
      nnMul (negativePart y) n
        (negativePart-nonnegative y)
        0≤n

    distrib-back :
      x * yn+ + (- (x * yn-)) ≡ x * (yn+ + (- yn-))
    distrib-back =
      sym
        (*-distribL x yn+ (- yn-) ∙
         cong₂ _+_ refl (*-negR x yn-))

  *-assoc :
    (x y z : DedekindCut ℓ) →
    (x * y) * z ≡ x * (y * z)
  *-assoc x y z =
    *-right-decomposition (x * y) z ∙
    cong₂ _+_
      (*-assocR-nonnegative x y (positivePart z) (positivePart-nonnegative z))
      (cong -_
        (*-assocR-nonnegative x y (negativePart z) (negativePart-nonnegative z))) ∙
    distrib-back ∙
    cong (x *_) (sym (*-right-decomposition y z))
    where
    yz+ : DedekindCut ℓ
    yz+ = y * positivePart z

    yz- : DedekindCut ℓ
    yz- = y * negativePart z

    distrib-back :
      x * yz+ + (- (x * yz-)) ≡ x * (yz+ + (- yz-))
    distrib-back =
      sym
        (*-distribL x yz+ (- yz-) ∙
         cong₂ _+_ refl (*-negR x yz-))
