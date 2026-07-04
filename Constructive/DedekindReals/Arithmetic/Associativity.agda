{-

Full signed associativity for constructive Dedekind-real multiplication

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.DedekindReals.Arithmetic.Associativity where

open import Cubical.Foundations.Prelude

open import Constructive.DedekindReals
open import Constructive.DedekindReals.Arithmetic.Base
open import Constructive.DedekindReals.Arithmetic.AdditiveGroup
open import Constructive.DedekindReals.Arithmetic.Difference
open import Constructive.DedekindReals.Arithmetic.Distributivity
open import Constructive.DedekindReals.Arithmetic.Negation
open import Constructive.DedekindReals.Arithmetic.NonNegative


module MultiplicationAssociativity {ℓ : Level} where
  open Algebra {ℓ}
  open Addition {ℓ}
  open NonNegativeMultiplication {ℓ}
  open Multiplication {ℓ}
  open AdditiveGroup {ℓ}
  open DifferenceProperties {ℓ}
  open MultiplicationDistributivity {ℓ}
  open NegationProperties {ℓ}
  open NonNegativeProperties {ℓ}

  *-assoc-two-r≥0 :
    (x a n : DedekindReal ℓ) →
    (0≤a : a ≥0) →
    (0≤n : n ≥0) →
    (x * a) * n ≡ x * (nnMul a n 0≤a 0≤n)
  *-assoc-two-r≥0 x a n 0≤a 0≤n =
    cong (_* n) (*-r≥0-form x a 0≤a) ∙
    *-distribR-≥0
      (nnMul (posPart x) a (posPart≥0 x) 0≤a)
      (- nnMul (negPart x) a (negPart≥0 x) 0≤a)
      n
      0≤n ∙
    cong₂ _+_
      left-assoc
      (*-negL (nnMul (negPart x) a (negPart≥0 x) 0≤a) n ∙
       cong -_ right-assoc) ∙
    sym (*-r≥0-form x (nnMul a n 0≤a 0≤n) 0≤an)
    where
    0≤an : (nnMul a n 0≤a 0≤n) ≥0
    0≤an = nnMul-Pres≥0 a n 0≤a 0≤n

    left-assoc :
      nnMul (posPart x) a (posPart≥0 x) 0≤a * n
      ≡
      nnMul (posPart x) (nnMul a n 0≤a 0≤n)
        (posPart≥0 x)
        0≤an
    left-assoc =
      *-of-≥0
        (nnMul (posPart x) a (posPart≥0 x) 0≤a)
        n
        (nnMul-Pres≥0 (posPart x) a (posPart≥0 x) 0≤a)
        0≤n ∙
      sym
        (nnMul-assoc
          (posPart x)
          a
          n
          (posPart≥0 x)
          0≤a
          0≤n)

    right-assoc :
      nnMul (negPart x) a (negPart≥0 x) 0≤a * n
      ≡
      nnMul (negPart x) (nnMul a n 0≤a 0≤n)
        (negPart≥0 x)
        0≤an
    right-assoc =
      *-of-≥0
        (nnMul (negPart x) a (negPart≥0 x) 0≤a)
        n
        (nnMul-Pres≥0 (negPart x) a (negPart≥0 x) 0≤a)
        0≤n ∙
      sym
        (nnMul-assoc
          (negPart x)
          a
          n
          (negPart≥0 x)
          0≤a
          0≤n)

  *-assocR-≥0 :
    (x y n : DedekindReal ℓ) →
    (0≤n : n ≥0) →
    (x * y) * n ≡ x * (y * n)
  *-assocR-≥0 x y n 0≤n =
    cong (_* n) (*-right-decomposition x y) ∙
    *-distribR-≥0
      (x * posPart y)
      (- (x * negPart y))
      n
      0≤n ∙
    cong₂ _+_
      (*-assoc-two-r≥0 x (posPart y) n
        (posPart≥0 y)
        0≤n)
      (*-negL (x * negPart y) n ∙
       cong -_
        (*-assoc-two-r≥0 x (negPart y) n
          (negPart≥0 y)
          0≤n)) ∙
    distrib-back ∙
    cong (x *_) (sym (*-r≥0-form y n 0≤n))
    where
    yn+ : DedekindReal ℓ
    yn+ =
      nnMul (posPart y) n
        (posPart≥0 y)
        0≤n

    yn- : DedekindReal ℓ
    yn- =
      nnMul (negPart y) n
        (negPart≥0 y)
        0≤n

    distrib-back :
      x * yn+ + (- (x * yn-)) ≡ x * (yn+ + (- yn-))
    distrib-back =
      sym
        (*-distribL x yn+ (- yn-) ∙
         cong₂ _+_ refl (*-negR x yn-))

  *-assoc :
    (x y z : DedekindReal ℓ) →
    (x * y) * z ≡ x * (y * z)
  *-assoc x y z =
    *-right-decomposition (x * y) z ∙
    cong₂ _+_
      (*-assocR-≥0 x y (posPart z) (posPart≥0 z))
      (cong -_
        (*-assocR-≥0 x y (negPart z) (negPart≥0 z))) ∙
    distrib-back ∙
    cong (x *_) (sym (*-right-decomposition y z))
    where
    yz+ : DedekindReal ℓ
    yz+ = y * posPart z

    yz- : DedekindReal ℓ
    yz- = y * negPart z

    distrib-back :
      x * yz+ + (- (x * yz-)) ≡ x * (yz+ + (- yz-))
    distrib-back =
      sym
        (*-distribL x yz+ (- yz-) ∙
         cong₂ _+_ refl (*-negR x yz-))
