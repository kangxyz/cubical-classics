{-

Subunit-ball convergence for atanh and atan

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Convergence where

open import Cubical.Foundations.Prelude using (sym)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Rationals.Order as ℚOrder
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using (derivativePowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using (majorizedOnBall→hasPowerSeriesOnBallWith)
open import Constructive.Analysis.Reals.PowerSeries.Radius
  using (HasPowerSeriesOnBallWith ; hasPowerSeriesOnBallWith-cong)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Bounds
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Majorants
open import Constructive.Analysis.GeometricDecay
  using (positiveGeometricPowerModulus)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


private
  unitCoefficientPowerSeriesOnSubunitBallWith :
    (a : PowerSeries) →
    ((n : ℕ) → BoundedByᶜ 1⁺ (a n)) →
    (ρ : ℚ⁺) →
    (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    HasPowerSeriesOnBallWith
      a
      ρ
      (positiveGeometricPowerModulus ρ ρ<1)
  unitCoefficientPowerSeriesOnSubunitBallWith a coefficientBound ρ ρ<1 =
    majorizedOnBall→hasPowerSeriesOnBallWith
      (unitCoefficientPowerSeriesMajorizedOnBall
        a
        coefficientBound
        ρ
        ρ<1)


evenGeometricPowerSeriesOnSubunitBallWith :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesOnBallWith
    evenGeometricPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
evenGeometricPowerSeriesOnSubunitBallWith =
  unitCoefficientPowerSeriesOnSubunitBallWith
    evenGeometricPowerSeries
    evenGeometricPowerSeriesCoefficientBoundOne


atanhPowerSeriesOnSubunitBallWith :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesOnBallWith
    atanhPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
atanhPowerSeriesOnSubunitBallWith =
  unitCoefficientPowerSeriesOnSubunitBallWith
    atanhPowerSeries
    atanhPowerSeriesCoefficientBoundOne


atanhDerivativePowerSeriesOnSubunitBallWith :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesOnBallWith
    (derivativePowerSeries atanhPowerSeries)
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
atanhDerivativePowerSeriesOnSubunitBallWith ρ ρ<1 =
  hasPowerSeriesOnBallWith-cong
    (λ n → sym (derivativePowerSeries-atanh n))
    (evenGeometricPowerSeriesOnSubunitBallWith ρ ρ<1)


atanPowerSeriesOnSubunitBallWith :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesOnBallWith
    atanPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
atanPowerSeriesOnSubunitBallWith =
  unitCoefficientPowerSeriesOnSubunitBallWith
    atanPowerSeries
    atanPowerSeriesCoefficientBoundOne
