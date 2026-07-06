{-

Signed associativity for constructive Dedekind-completion multiplication

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Associativity where

open import Cubical.Foundations.Prelude

open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedean
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.Analysis.Completions.DedekindCompletion
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Base
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Negation
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.NonNegative
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Multiplication
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Difference
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Distributivity

private
  variable
    ℓ ℓ' ℓᴾ : Level


module MultiplicationAssociativity
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
  open MultiplicationNegation 𝒜 {ℓᴾ}
  open DifferenceProperties 𝒜 {ℓᴾ}
  open MultiplicationDistributivity 𝒜 {ℓᴾ}

  *𝔻-assoc-two-r≥0 :
    (x a n : DedekindCompletion ℓᴾ) →
    (0≤a : a ≥0) →
    (0≤n : n ≥0) →
    (x *𝔻 a) *𝔻 n ≡ x *𝔻 (nnMul a n 0≤a 0≤n)
  *𝔻-assoc-two-r≥0 x a n 0≤a 0≤n =
    cong (_*𝔻 n) (*𝔻-r≥0-form x a 0≤a) ∙
    *𝔻-distribR-≥0
      (nnMul (posPart x) a (posPart≥0 x) 0≤a)
      (-𝔻 nnMul (negPart x) a (negPart≥0 x) 0≤a)
      n
      0≤n ∙
    cong₂ _+𝔻_
      left-assoc
      (*𝔻-negL (nnMul (negPart x) a (negPart≥0 x) 0≤a) n ∙
       cong -𝔻_ right-assoc) ∙
    sym (*𝔻-r≥0-form x (nnMul a n 0≤a 0≤n) 0≤an)
    where
    0≤an : (nnMul a n 0≤a 0≤n) ≥0
    0≤an = nnMul-Pres≥0 a n 0≤a 0≤n

    left-assoc :
      nnMul (posPart x) a (posPart≥0 x) 0≤a *𝔻 n
      ≡
      nnMul (posPart x) (nnMul a n 0≤a 0≤n)
        (posPart≥0 x)
        0≤an
    left-assoc =
      *𝔻-of-≥0
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
      nnMul (negPart x) a (negPart≥0 x) 0≤a *𝔻 n
      ≡
      nnMul (negPart x) (nnMul a n 0≤a 0≤n)
        (negPart≥0 x)
        0≤an
    right-assoc =
      *𝔻-of-≥0
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

  *𝔻-assocR-≥0 :
    (x y n : DedekindCompletion ℓᴾ) →
    (0≤n : n ≥0) →
    (x *𝔻 y) *𝔻 n ≡ x *𝔻 (y *𝔻 n)
  *𝔻-assocR-≥0 x y n 0≤n =
    cong (_*𝔻 n) (*𝔻-right-decomposition x y) ∙
    *𝔻-distribR-≥0
      (x *𝔻 posPart y)
      (-𝔻 (x *𝔻 negPart y))
      n
      0≤n ∙
    cong₂ _+𝔻_
      (*𝔻-assoc-two-r≥0 x (posPart y) n
        (posPart≥0 y)
        0≤n)
      (*𝔻-negL (x *𝔻 negPart y) n ∙
       cong -𝔻_
        (*𝔻-assoc-two-r≥0 x (negPart y) n
          (negPart≥0 y)
          0≤n)) ∙
    distrib-back ∙
    cong (x *𝔻_) (sym (*𝔻-r≥0-form y n 0≤n))
    where
    yn+ : DedekindCompletion ℓᴾ
    yn+ =
      nnMul (posPart y) n
        (posPart≥0 y)
        0≤n

    yn- : DedekindCompletion ℓᴾ
    yn- =
      nnMul (negPart y) n
        (negPart≥0 y)
        0≤n

    distrib-back :
      x *𝔻 yn+ +𝔻 (-𝔻 (x *𝔻 yn-)) ≡ x *𝔻 (yn+ +𝔻 (-𝔻 yn-))
    distrib-back =
      sym
        (*𝔻-distribL x yn+ (-𝔻 yn-) ∙
         cong₂ _+𝔻_ refl (*𝔻-negR x yn-))

  *𝔻-assoc :
    (x y z : DedekindCompletion ℓᴾ) →
    (x *𝔻 y) *𝔻 z ≡ x *𝔻 (y *𝔻 z)
  *𝔻-assoc x y z =
    *𝔻-right-decomposition (x *𝔻 y) z ∙
    cong₂ _+𝔻_
      (*𝔻-assocR-≥0 x y (posPart z) (posPart≥0 z))
      (cong -𝔻_
        (*𝔻-assocR-≥0 x y (negPart z) (negPart≥0 z))) ∙
    distrib-back ∙
    cong (x *𝔻_) (sym (*𝔻-right-decomposition y z))
    where
    yz+ : DedekindCompletion ℓᴾ
    yz+ = y *𝔻 posPart z

    yz- : DedekindCompletion ℓᴾ
    yz- = y *𝔻 negPart z

    distrib-back :
      x *𝔻 yz+ +𝔻 (-𝔻 (x *𝔻 yz-)) ≡ x *𝔻 (yz+ +𝔻 (-𝔻 yz-))
    distrib-back =
      sym
        (*𝔻-distribL x yz+ (-𝔻 yz-) ∙
         cong₂ _+𝔻_ refl (*𝔻-negR x yz-))
