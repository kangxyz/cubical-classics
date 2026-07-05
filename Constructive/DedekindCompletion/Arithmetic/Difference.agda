{-

Difference of constructive Dedekind completions

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.DedekindCompletion.Arithmetic.Difference where

open import Cubical.Foundations.Prelude

open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedes
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.DedekindCompletion
open import Constructive.DedekindCompletion.Arithmetic.Base
open import Constructive.DedekindCompletion.Arithmetic.Negation
open import Constructive.DedekindCompletion.Arithmetic.AdditiveGroup
open import Constructive.DedekindCompletion.Arithmetic.NonNegative
open import Constructive.DedekindCompletion.Arithmetic.Multiplication
open import Constructive.DedekindCompletion.Arithmetic.Unit

private
  variable
    ℓ ℓ' ℓᴾ : Level


module Difference (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') {ℓᴾ : Level} where

  𝒦 : LinearlyOrderedField ℓ ℓ'
  𝒦 = 𝒜 .fst

  open CompletionBase 𝒦
  open ArithmeticBase 𝒜
  open Addition {ℓᴾ}
  open Negation 𝒜 {ℓᴾ}
  open AdditiveGroup 𝒜 {ℓᴾ}

  _-𝔻_ : DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ
  x -𝔻 y = x +𝔻 (-𝔻 y)

  infixl 6 _-𝔻_

  difference-neg-swap' :
    (a b : DedekindCompletion ℓᴾ) →
    a -𝔻 b ≡ -𝔻 (b -𝔻 a)
  difference-neg-swap' = difference-neg-swap


module DifferenceProperties
  (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') {ℓᴾ : Level} where

  baseField : LinearlyOrderedField ℓ ℓ'
  baseField = 𝒜 .fst

  open CompletionBase baseField
  open ArithmeticBase 𝒜
  open Addition {ℓᴾ}
  open Negation 𝒜 {ℓᴾ}
  open AdditiveGroup 𝒜 {ℓᴾ}
  open NonNegativeMultiplication 𝒜 {ℓᴾ}
  open NonNegativeProperties 𝒜 {ℓᴾ}
  open Multiplication 𝒜 {ℓᴾ}
  open UnitProperties 𝒜 {ℓᴾ}

  nnMul-difference-congR :
    (a b c d n : DedekindCompletion ℓᴾ) →
    (0≤a : a ≥0) →
    (0≤b : b ≥0) →
    (0≤c : c ≥0) →
    (0≤d : d ≥0) →
    (0≤n : n ≥0) →
    a +𝔻 (-𝔻 b) ≡ c +𝔻 (-𝔻 d) →
    nnMul a n 0≤a 0≤n +𝔻 (-𝔻 nnMul b n 0≤b 0≤n)
    ≡
    nnMul c n 0≤c 0≤n +𝔻 (-𝔻 nnMul d n 0≤d 0≤n)
  nnMul-difference-congR a b c d n 0≤a 0≤b 0≤c 0≤d 0≤n diff-path =
    cross-sum→difference-eq
      (nnMul a n 0≤a 0≤n)
      (nnMul b n 0≤b 0≤n)
      (nnMul c n 0≤c 0≤n)
      (nnMul d n 0≤d 0≤n)
      product-cross
    where
    0≤a+d : (a +𝔻 d) ≥0
    0≤a+d = +-Pres≥0 a d 0≤a 0≤d

    0≤c+b : (c +𝔻 b) ≥0
    0≤c+b = +-Pres≥0 c b 0≤c 0≤b

    cross-path : a +𝔻 d ≡ c +𝔻 b
    cross-path =
      difference-eq→cross-sum a b c d diff-path

    product-sums :
      nnMul (a +𝔻 d) n 0≤a+d 0≤n
      ≡
      nnMul (c +𝔻 b) n 0≤c+b 0≤n
    product-sums =
      nnMul-congL
        (a +𝔻 d)
        (c +𝔻 b)
        n
        cross-path
        0≤a+d
        0≤c+b
        0≤n
        0≤n

    product-cross :
      nnMul a n 0≤a 0≤n +𝔻 nnMul d n 0≤d 0≤n
      ≡
      nnMul c n 0≤c 0≤n +𝔻 nnMul b n 0≤b 0≤n
    product-cross =
      sym (nnMul-distribR a d n 0≤a 0≤d 0≤n) ∙
      product-sums ∙
      nnMul-distribR c b n 0≤c 0≤b 0≤n

  sum-decomposition :
    (x y : DedekindCompletion ℓᴾ) →
    x +𝔻 y ≡
    (posPart x +𝔻 posPart y) +𝔻
    (-𝔻 (negPart x +𝔻 negPart y))
  sum-decomposition x y =
    cong₂ _+𝔻_
      (sym (positive-negative-decomposition x))
      (sym (positive-negative-decomposition y)) ∙
    sum-differences
      (posPart x)
      (negPart x)
      (posPart y)
      (negPart y)

  rMul≥0-difference :
    (x a b n : DedekindCompletion ℓᴾ) →
    (0≤a : a ≥0) →
    (0≤b : b ≥0) →
    (0≤n : n ≥0) →
    x ≡ a +𝔻 (-𝔻 b) →
    rMul≥0 x n 0≤n
    ≡
    nnMul a n 0≤a 0≤n +𝔻 (-𝔻 nnMul b n 0≤b 0≤n)
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

  *𝔻-distribR-≥0 :
    (x y n : DedekindCompletion ℓᴾ) →
    (0≤n : n ≥0) →
    (x +𝔻 y) *𝔻 n ≡ (x *𝔻 n) +𝔻 (y *𝔻 n)
  *𝔻-distribR-≥0 x y n 0≤n =
    *𝔻-r≥0-form (x +𝔻 y) n 0≤n ∙
    rMul≥0-difference
      (x +𝔻 y)
      (posPart x +𝔻 posPart y)
      (negPart x +𝔻 negPart y)
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
    cong₂ _+𝔻_
      (nnMul-distribR
        (posPart x)
        (posPart y)
        n
        (posPart≥0 x)
        (posPart≥0 y)
        0≤n)
      (cong -𝔻_
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
    cong₂ _+𝔻_
      (sym (*𝔻-r≥0-form x n 0≤n))
      (sym (*𝔻-r≥0-form y n 0≤n))
