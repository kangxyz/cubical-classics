{-

Subunit-ball convergence for hyperbolic arctangent

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Convergence where

open import Cubical.Foundations.Prelude using (sym)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Rationals.Order as ℚOrder
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.FormalDerivative
  using (derivativePowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using (majorizedOnBall→hasPowerSeriesOnBallWith)
open import Constructive.Analysis.Reals.PowerSeries.Radius
  using (HasPowerSeriesOnBallWith ; hasPowerSeriesOnBallWith-cong)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Bounds
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Majorants
open import Constructive.Analysis.Reals.PowerSeries.Elementary.SubunitMajorant
  using (unitCoefficientPowerSeriesOnSubunitBallWith)
open import Constructive.Analysis.GeometricDecay
  using (positiveGeometricPowerModulus)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


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
