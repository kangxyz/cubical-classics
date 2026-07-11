{-

Geometric-series bridge for logarithm functional equations

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.FunctionalEquation.GeometricBridge where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Modulus using (AntitoneNatModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedDivision
  using
    ( BoundedAwayPositiveᶜ
    ; reciprocalPositiveᶜ
    ; reciprocalPositiveᶜ-right
    )
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Inverse
  using (right-inverse-uniqueᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.PowerSeries.Base
  using (powerSeriesTerm)
open import Constructive.Analysis.Reals.PowerSeries.Examples.Geometric
  using
    ( alternatingGeometricPowerSeries
    ; alternatingGeometricPowerSeriesOnBallWith
    ; alternatingGeometricPowerSeriesTerm
    ; alternatingGeometricPowerSeriesTermPath
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.Base
  using
    ( derivativePowerSeries-logOnePlus
    ; logOnePlusPowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.FormalDerivative
  using (derivativePowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Radius
  using
    ( HasPowerSeriesOnBallWith
    ; hasPowerSeriesOnBallWith-cong
    ; powerSeriesSumOnBall
    ; powerSeriesSumOnBall-coefficients-path
    )
open import Constructive.Analysis.Reals.Series.Finite using (partialSum)
open import Constructive.Analysis.Reals.Series.Neumann
  using (seriesSumFromFiniteTailBound-neumannRightInverse)
open import Constructive.Analysis.Reals.Series.Tail using (TailBound)
open import Constructive.Analysis.GeometricDecay
  using
    ( positiveGeometricPowerModulus
    )
open import Constructive.Analysis.Reals.Series.Geometric.Real
  using (realGeometricFiniteIdentity)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Power
  using (realPower)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


logOnePlusDerivativePowerSeriesOnSubunitBallWith :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesOnBallWith
    (derivativePowerSeries logOnePlusPowerSeries)
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
logOnePlusDerivativePowerSeriesOnSubunitBallWith ρ ρ<1 =
  hasPowerSeriesOnBallWith-cong
    (λ n → sym (derivativePowerSeries-logOnePlus n))
    (alternatingGeometricPowerSeriesOnBallWith ρ ρ<1)


alternatingGeometricPowerSeriesFiniteIdentity :
  (h : ℝᶜ) →
  (n : ℕ) →
  (1ᶜ +ᶜ h) ·ᶜ
    partialSum (powerSeriesTerm alternatingGeometricPowerSeries h) n
  ≡
  1ᶜ +ᶜ
    (-ᶜ powerSeriesTerm alternatingGeometricPowerSeries h n)
alternatingGeometricPowerSeriesFiniteIdentity h n =
  cong₂
    _·ᶜ_
    (sym (cong (1ᶜ +ᶜ_) (neg-involutive h)))
    (cong (λ u → partialSum u n)
      (alternatingGeometricPowerSeriesTermPath h)) ∙
  realGeometricFiniteIdentity (-ᶜ h) n ∙
  cong
    (λ term → 1ᶜ +ᶜ (-ᶜ term))
    (sym (alternatingGeometricPowerSeriesTerm h n))


alternatingGeometricPowerSeriesNeumannRightInverseOnBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (1ᶜ +ᶜ h) →
  (1ᶜ +ᶜ h) ·ᶜ
    powerSeriesSumOnBall
      alternatingGeometricPowerSeries
      ρ
      (positiveGeometricPowerModulus ρ ρ<1)
      (alternatingGeometricPowerSeriesOnBallWith ρ ρ<1)
      h
      h-bound
  ≡
  1ᶜ
alternatingGeometricPowerSeriesNeumannRightInverseOnBall
  ρ
  ρ<1
  h
  h-bound
  κ
  factorBound =
  seriesSumFromFiniteTailBound-neumannRightInverse
    factor
    κ
    factorBound
    (powerSeriesTerm alternatingGeometricPowerSeries h)
    μ
    tailBound
    μ-antitone
    (λ n → n)
    (λ _ → NatOrder.≤-refl)
    (alternatingGeometricPowerSeriesFiniteIdentity h)
  where
  μ : ℚ⁺ → ℕ
  μ =
    positiveGeometricPowerModulus ρ ρ<1

  convergence :
    HasPowerSeriesOnBallWith
      alternatingGeometricPowerSeries
      ρ
      μ
  convergence =
    alternatingGeometricPowerSeriesOnBallWith ρ ρ<1

  μ-antitone : AntitoneNatModulus μ
  μ-antitone =
    HasPowerSeriesOnBallWith.antitoneModulus convergence

  tailBound :
    TailBound (powerSeriesTerm alternatingGeometricPowerSeries h) μ
  tailBound =
    HasPowerSeriesOnBallWith.tailBound convergence h h-bound

  factor : ℝᶜ
  factor =
    1ᶜ +ᶜ h


logOnePlusDerivativePowerSeriesNeumannRightInverseOnBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (1ᶜ +ᶜ h) →
  (1ᶜ +ᶜ h) ·ᶜ
    powerSeriesSumOnBall
      (derivativePowerSeries logOnePlusPowerSeries)
      ρ
      (positiveGeometricPowerModulus ρ ρ<1)
      (logOnePlusDerivativePowerSeriesOnSubunitBallWith ρ ρ<1)
      h
      h-bound
  ≡
  1ᶜ
logOnePlusDerivativePowerSeriesNeumannRightInverseOnBall
  ρ
  ρ<1
  h
  h-bound
  κ
  factorBound =
  cong
    ((1ᶜ +ᶜ h) ·ᶜ_)
    (sym derivativeSumPath) ∙
  alternatingGeometricPowerSeriesNeumannRightInverseOnBall
    ρ
    ρ<1
    h
    h-bound
    κ
    factorBound
  where
  derivativeSumPath :
    powerSeriesSumOnBall
      alternatingGeometricPowerSeries
      ρ
      (positiveGeometricPowerModulus ρ ρ<1)
      (alternatingGeometricPowerSeriesOnBallWith ρ ρ<1)
      h
      h-bound
    ≡
    powerSeriesSumOnBall
      (derivativePowerSeries logOnePlusPowerSeries)
      ρ
      (positiveGeometricPowerModulus ρ ρ<1)
      (logOnePlusDerivativePowerSeriesOnSubunitBallWith ρ ρ<1)
      h
      h-bound
  derivativeSumPath =
    powerSeriesSumOnBall-coefficients-path
      (λ n → sym (derivativePowerSeries-logOnePlus n))
      (alternatingGeometricPowerSeriesOnBallWith ρ ρ<1)
      (logOnePlusDerivativePowerSeriesOnSubunitBallWith ρ ρ<1)
      h
      h-bound
      h-bound


logOnePlusDerivativePowerSeriesReciprocalOnBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  (factorLower κ : ℚ⁺) →
  (factorAway : BoundedAwayPositiveᶜ factorLower (1ᶜ +ᶜ h)) →
  BoundedByᶜ κ (1ᶜ +ᶜ h) →
  powerSeriesSumOnBall
    (derivativePowerSeries logOnePlusPowerSeries)
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (logOnePlusDerivativePowerSeriesOnSubunitBallWith ρ ρ<1)
    h
    h-bound
  ≡
  reciprocalPositiveᶜ factorLower (1ᶜ +ᶜ h) factorAway
logOnePlusDerivativePowerSeriesReciprocalOnBall
  ρ
  ρ<1
  h
  h-bound
  factorLower
  κ
  factorAway
  factorBound =
  sym
    (right-inverse-uniqueᶜ
      (reciprocalPositiveᶜ-right
        factorLower
        (1ᶜ +ᶜ h)
        factorAway)
      (logOnePlusDerivativePowerSeriesNeumannRightInverseOnBall
        ρ
        ρ<1
        h
        h-bound
        κ
        factorBound))
