{-

Multiplication by a nonnegative Dedekind cut respects difference
representations.  This is the Grothendieck-style bridge from the nonnegative
semiring laws to signed multiplication laws.

-}
{-# OPTIONS --safe #-}
module Cubical.DedekindCut.Arithmetic.Difference where

open import Cubical.Foundations.Prelude

open import Cubical.DedekindCut
open import Cubical.DedekindCut.Arithmetic
open import Cubical.DedekindCut.Arithmetic.AdditiveGroup
open import Cubical.DedekindCut.Arithmetic.NonnegativeLaws
open import Cubical.DedekindCut.Arithmetic.Unit


module DifferenceMultiplication {ℓ : Level} where
  open Algebra {ℓ}
  open Lattice {ℓ}
  open Addition {ℓ}
  open NonnegativeMultiplication {ℓ}
  open SignedMultiplication {ℓ}
  open AdditiveGroup {ℓ}
  open NonnegativeLaws {ℓ}
  open NonnegativeUnit {ℓ}

  nnMul-difference-congR :
    (a b c d n : DedekindCut ℓ) →
    (0≤a : Nonnegative a) →
    (0≤b : Nonnegative b) →
    (0≤c : Nonnegative c) →
    (0≤d : Nonnegative d) →
    (0≤n : Nonnegative n) →
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
    0≤a+d : Nonnegative (a + d)
    0≤a+d = +-nonnegative a d 0≤a 0≤d

    0≤c+b : Nonnegative (c + b)
    0≤c+b = +-nonnegative c b 0≤c 0≤b

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
    (x y : DedekindCut ℓ) →
    x + y ≡
    (positivePart x + positivePart y) +
    (- (negativePart x + negativePart y))
  sum-decomposition x y =
    cong₂ _+_
      (sym (positive-negative-decomposition x))
      (sym (positive-negative-decomposition y)) ∙
    sum-differences
      (positivePart x)
      (negativePart x)
      (positivePart y)
      (negativePart y)

  rightNonnegativeProduct-difference :
    (x a b n : DedekindCut ℓ) →
    (0≤a : Nonnegative a) →
    (0≤b : Nonnegative b) →
    (0≤n : Nonnegative n) →
    x ≡ a + (- b) →
    rightNonnegativeProduct x n 0≤n
    ≡
    nnMul a n 0≤a 0≤n + (- nnMul b n 0≤b 0≤n)
  rightNonnegativeProduct-difference x a b n 0≤a 0≤b 0≤n x≡a-b =
    nnMul-difference-congR
      (positivePart x)
      (negativePart x)
      a
      b
      n
      (positivePart-nonnegative x)
      (negativePart-nonnegative x)
      0≤a
      0≤b
      0≤n
      (positive-negative-decomposition x ∙ x≡a-b)

  *-distribR-nonnegative :
    (x y n : DedekindCut ℓ) →
    (0≤n : Nonnegative n) →
    (x + y) * n ≡ (x * n) + (y * n)
  *-distribR-nonnegative x y n 0≤n =
    *-right-nonnegative-form (x + y) n 0≤n ∙
    rightNonnegativeProduct-difference
      (x + y)
      (positivePart x + positivePart y)
      (negativePart x + negativePart y)
      n
      (+-nonnegative
        (positivePart x)
        (positivePart y)
        (positivePart-nonnegative x)
        (positivePart-nonnegative y))
      (+-nonnegative
        (negativePart x)
        (negativePart y)
        (negativePart-nonnegative x)
        (negativePart-nonnegative y))
      0≤n
      (sum-decomposition x y) ∙
    cong₂ _+_
      (nnMul-distribR
        (positivePart x)
        (positivePart y)
        n
        (positivePart-nonnegative x)
        (positivePart-nonnegative y)
        0≤n)
      (cong -_
        (nnMul-distribR
          (negativePart x)
          (negativePart y)
          n
          (negativePart-nonnegative x)
          (negativePart-nonnegative y)
          0≤n)) ∙
    sym
      (sum-differences
        (nnMul (positivePart x) n (positivePart-nonnegative x) 0≤n)
        (nnMul (negativePart x) n (negativePart-nonnegative x) 0≤n)
        (nnMul (positivePart y) n (positivePart-nonnegative y) 0≤n)
        (nnMul (negativePart y) n (negativePart-nonnegative y) 0≤n)) ∙
    cong₂ _+_
      (sym (*-right-nonnegative-form x n 0≤n))
      (sym (*-right-nonnegative-form y n 0≤n))

