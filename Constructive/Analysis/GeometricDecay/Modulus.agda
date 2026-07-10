{-

Antitone moduli for positive geometric decay

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.GeometricDecay.Modulus where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax)
open import Cubical.Relation.Nullary using (¬_)

open import Constructive.Analysis.Modulus
open import Constructive.Data.PositiveRationals
open import Constructive.Preliminary.Nat.BoundedSearch
import Constructive.Data.Rationals as Rational


positiveGeometricGap :
  ℚ⁺ →
  ℚ
positiveGeometricGap ρ =
  Rational.1ℚ ℚ.- radius ρ


positiveGeometricGap-positive :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  Rational.0ℚ ℚOrder.< positiveGeometricGap ρ
positiveGeometricGap-positive ρ ρ<1 =
  Rational.diff-positive {p = radius ρ} {q = Rational.1ℚ} ρ<1


positiveGeometricPowerStep :
  (ρ : ℚ⁺) →
  ℚ⁺ →
  ℚ
positiveGeometricPowerStep ρ ε =
  (radius ε ℚ.· positiveGeometricGap ρ) ℚ.· positiveGeometricGap ρ


positiveGeometricPowerStep-positive :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (ε : ℚ⁺) →
  Rational.0ℚ ℚOrder.< positiveGeometricPowerStep ρ ε
positiveGeometricPowerStep-positive ρ ρ<1 ε =
  Rational.mul-positive
    {a = radius ε ℚ.· gap}
    {b = gap}
    (Rational.mul-positive {a = radius ε} {b = gap} (ε .snd) gap>0)
    gap>0
  where
  gap : ℚ
  gap =
    positiveGeometricGap ρ

  gap>0 : Rational.0ℚ ℚOrder.< gap
  gap>0 =
    positiveGeometricGap-positive ρ ρ<1


PositiveGeometricPowerModulusTest :
  (ρ : ℚ⁺) →
  ℚ⁺ →
  ℕ →
  Type₀
PositiveGeometricPowerModulusTest ρ ε n =
  Rational.1ℚ ℚOrder.< Rational.natMul n (positiveGeometricPowerStep ρ ε)




positiveGeometricPowerModulusLeast :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (ε : ℚ⁺) →
  BoundedLeast (PositiveGeometricPowerModulusTest ρ ε)
positiveGeometricPowerModulusLeast ρ ρ<1 ε =
  boundedLeast
    (λ n → Rational.dec< Rational.1ℚ
      (Rational.natMul n (positiveGeometricPowerStep ρ ε)))
    bound
    boundWorks
  where
  boundData :
    Σ[ n ∈ ℕ ] PositiveGeometricPowerModulusTest ρ ε n
  boundData =
    Rational.archimedean
      Rational.1ℚ
      (positiveGeometricPowerStep ρ ε)
      (positiveGeometricPowerStep-positive ρ ρ<1 ε)

  bound : ℕ
  bound =
    boundData .fst

  boundWorks : PositiveGeometricPowerModulusTest ρ ε bound
  boundWorks =
    boundData .snd


positiveGeometricPowerModulus :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  NatModulus
positiveGeometricPowerModulus ρ ρ<1 ε =
  positiveGeometricPowerModulusLeast ρ ρ<1 ε .fst


positiveGeometricPowerModulus-large :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (ε : ℚ⁺) →
  PositiveGeometricPowerModulusTest
    ρ
    ε
    (positiveGeometricPowerModulus ρ ρ<1 ε)
positiveGeometricPowerModulus-large ρ ρ<1 ε =
  positiveGeometricPowerModulusLeast ρ ρ<1 ε .snd .fst


positiveGeometricPowerStep-mono≤ :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  {ε δ : ℚ⁺} →
  radius ε ℚOrder.≤ radius δ →
  positiveGeometricPowerStep ρ ε ℚOrder.≤ positiveGeometricPowerStep ρ δ
positiveGeometricPowerStep-mono≤ ρ ρ<1 {ε = ε} {δ = δ} ε≤δ =
  ℚOrder.≤-·o
    (radius ε ℚ.· gap)
    (radius δ ℚ.· gap)
    gap
    gap≥0
    (ℚOrder.≤-·o
      (radius ε)
      (radius δ)
      gap
      gap≥0
      ε≤δ)
  where
  gap : ℚ
  gap =
    positiveGeometricGap ρ

  gap≥0 : Rational.0ℚ ℚOrder.≤ gap
  gap≥0 =
    Rational.<→≤
      {p = Rational.0ℚ}
      {q = gap}
      (positiveGeometricGap-positive ρ ρ<1)


positiveGeometricPowerModulus-antitone :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  AntitoneNatModulus (positiveGeometricPowerModulus ρ ρ<1)
positiveGeometricPowerModulus-antitone ρ ρ<1 {ε = ε} {δ = δ} ε≤δ =
  boundedLeast-monotone
    (positiveGeometricPowerModulusLeast ρ ρ<1 ε)
    (positiveGeometricPowerModulusLeast ρ ρ<1 δ)
    ε-test→δ-test
  where
  step≤ :
    positiveGeometricPowerStep ρ ε ℚOrder.≤
    positiveGeometricPowerStep ρ δ
  step≤ =
    positiveGeometricPowerStep-mono≤
      ρ
      ρ<1
      {ε = ε}
      {δ = δ}
      ε≤δ

  ε-test→δ-test :
    (n : ℕ) →
    PositiveGeometricPowerModulusTest ρ ε n →
    PositiveGeometricPowerModulusTest ρ δ n
  ε-test→δ-test n ε-test =
    Rational.<≤-trans
      {p = Rational.1ℚ}
      {q = Rational.natMul n (positiveGeometricPowerStep ρ ε)}
      {r = Rational.natMul n (positiveGeometricPowerStep ρ δ)}
      ε-test
      (Rational.natMul-factor-mono-≤ n step≤)
