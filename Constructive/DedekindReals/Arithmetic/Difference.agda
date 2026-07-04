{-

Multiplication by a nonnegative Dedekind real respects difference
representations.  This is the Grothendieck-style bridge from the nonnegative
semiring laws to signed multiplication laws.

-}
{-# OPTIONS --safe #-}
module Constructive.DedekindReals.Arithmetic.Difference where

open import Cubical.Foundations.Prelude

open import Constructive.DedekindReals
open import Constructive.DedekindReals.Arithmetic.Base
open import Constructive.DedekindReals.Arithmetic.AdditiveGroup
open import Constructive.DedekindReals.Arithmetic.NonNegative
open import Constructive.DedekindReals.Arithmetic.Unit


module DifferenceProperties {ℓ : Level} where
  open Algebra {ℓ}
  open Lattice {ℓ}
  open Addition {ℓ}
  open NonNegativeMultiplication {ℓ}
  open Multiplication {ℓ}
  open AdditiveGroup {ℓ}
  open NonNegativeProperties {ℓ}
  open UnitProperties {ℓ}

  nnMul-difference-congR :
    (a b c d n : DedekindReal ℓ) →
    (0≤a : a ≥0) →
    (0≤b : b ≥0) →
    (0≤c : c ≥0) →
    (0≤d : d ≥0) →
    (0≤n : n ≥0) →
    a + (- b) ≡ c + (- d) →
    nnMul a n 0≤a 0≤n + (- nnMul b n 0≤b 0≤n)
    ≡
    nnMul c n 0≤c 0≤n + (- nnMul d n 0≤d 0≤n)
  nnMul-difference-congR a b c d n 0≤a 0≤b 0≤c 0≤d 0≤n diff-path =
    cross-sum→difference-eq
      (nnMul a n 0≤a 0≤n)
      (nnMul b n 0≤b 0≤n)
      (nnMul c n 0≤c 0≤n)
      (nnMul d n 0≤d 0≤n)
      product-cross
    where
    0≤a+d : (a + d) ≥0
    0≤a+d = +-Pres≥0 a d 0≤a 0≤d

    0≤c+b : (c + b) ≥0
    0≤c+b = +-Pres≥0 c b 0≤c 0≤b

    cross-path : a + d ≡ c + b
    cross-path =
      difference-eq→cross-sum a b c d diff-path

    product-sums :
      nnMul (a + d) n 0≤a+d 0≤n
      ≡
      nnMul (c + b) n 0≤c+b 0≤n
    product-sums =
      nnMul-congL
        (a + d)
        (c + b)
        n
        cross-path
        0≤a+d
        0≤c+b
        0≤n
        0≤n

    product-cross :
      nnMul a n 0≤a 0≤n + nnMul d n 0≤d 0≤n
      ≡
      nnMul c n 0≤c 0≤n + nnMul b n 0≤b 0≤n
    product-cross =
      sym (nnMul-distribR a d n 0≤a 0≤d 0≤n) ∙
      product-sums ∙
      nnMul-distribR c b n 0≤c 0≤b 0≤n

  sum-decomposition :
    (x y : DedekindReal ℓ) →
    x + y ≡
    (posPart x + posPart y) +
    (- (negPart x + negPart y))
  sum-decomposition x y =
    cong₂ _+_
      (sym (positive-negative-decomposition x))
      (sym (positive-negative-decomposition y)) ∙
    sum-differences
      (posPart x)
      (negPart x)
      (posPart y)
      (negPart y)

  rMul≥0-difference :
    (x a b n : DedekindReal ℓ) →
    (0≤a : a ≥0) →
    (0≤b : b ≥0) →
    (0≤n : n ≥0) →
    x ≡ a + (- b) →
    rMul≥0 x n 0≤n
    ≡
    nnMul a n 0≤a 0≤n + (- nnMul b n 0≤b 0≤n)
  rMul≥0-difference x a b n 0≤a 0≤b 0≤n x≡a-b =
    nnMul-difference-congR
      (posPart x)
      (negPart x)
      a
      b
      n
      (posPart≥0 x)
      (negPart≥0 x)
      0≤a
      0≤b
      0≤n
      (positive-negative-decomposition x ∙ x≡a-b)

  *-distribR-≥0 :
    (x y n : DedekindReal ℓ) →
    (0≤n : n ≥0) →
    (x + y) * n ≡ (x * n) + (y * n)
  *-distribR-≥0 x y n 0≤n =
    *-r≥0-form (x + y) n 0≤n ∙
    rMul≥0-difference
      (x + y)
      (posPart x + posPart y)
      (negPart x + negPart y)
      n
      (+-Pres≥0
        (posPart x)
        (posPart y)
        (posPart≥0 x)
        (posPart≥0 y))
      (+-Pres≥0
        (negPart x)
        (negPart y)
        (negPart≥0 x)
        (negPart≥0 y))
      0≤n
      (sum-decomposition x y) ∙
    cong₂ _+_
      (nnMul-distribR
        (posPart x)
        (posPart y)
        n
        (posPart≥0 x)
        (posPart≥0 y)
        0≤n)
      (cong -_
        (nnMul-distribR
          (negPart x)
          (negPart y)
          n
          (negPart≥0 x)
          (negPart≥0 y)
          0≤n)) ∙
    sym
      (sum-differences
        (nnMul (posPart x) n (posPart≥0 x) 0≤n)
        (nnMul (negPart x) n (negPart≥0 x) 0≤n)
        (nnMul (posPart y) n (posPart≥0 y) 0≤n)
        (nnMul (negPart y) n (negPart≥0 y) 0≤n)) ∙
    cong₂ _+_
      (sym (*-r≥0-form x n 0≤n))
      (sym (*-r≥0-form y n 0≤n))

