{-

Subunit-ball convergence for atanh and atan

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Convergence where

open import Cubical.Foundations.Prelude using (sym)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (_,_)

open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using (derivativePowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Majorant
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Bounds
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Majorants
open import Constructive.Analysis.GeometricDecay
  using (positiveGeometricPowerModulus)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


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


unitCoefficientPowerSeriesOnSubunitBall :
  (a : PowerSeries) →
  ((n : ℕ) → BoundedByᶜ 1⁺ (a n)) →
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesOnBall a ρ
unitCoefficientPowerSeriesOnSubunitBall a coefficientBound ρ ρ<1 =
  positiveGeometricPowerModulus ρ ρ<1 ,
  unitCoefficientPowerSeriesOnSubunitBallWith
    a
    coefficientBound
    ρ
    ρ<1


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


alternatingEvenGeometricPowerSeriesOnSubunitBallWith :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesOnBallWith
    alternatingEvenGeometricPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
alternatingEvenGeometricPowerSeriesOnSubunitBallWith =
  unitCoefficientPowerSeriesOnSubunitBallWith
    alternatingEvenGeometricPowerSeries
    alternatingEvenGeometricPowerSeriesCoefficientBoundOne


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


evenGeometricPowerSeriesOnSubunitBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesOnBall evenGeometricPowerSeries ρ
evenGeometricPowerSeriesOnSubunitBall =
  unitCoefficientPowerSeriesOnSubunitBall
    evenGeometricPowerSeries
    evenGeometricPowerSeriesCoefficientBoundOne


alternatingEvenGeometricPowerSeriesOnSubunitBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesOnBall alternatingEvenGeometricPowerSeries ρ
alternatingEvenGeometricPowerSeriesOnSubunitBall =
  unitCoefficientPowerSeriesOnSubunitBall
    alternatingEvenGeometricPowerSeries
    alternatingEvenGeometricPowerSeriesCoefficientBoundOne


atanhPowerSeriesOnSubunitBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesOnBall atanhPowerSeries ρ
atanhPowerSeriesOnSubunitBall =
  unitCoefficientPowerSeriesOnSubunitBall
    atanhPowerSeries
    atanhPowerSeriesCoefficientBoundOne


atanPowerSeriesOnSubunitBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesOnBall atanPowerSeries ρ
atanPowerSeriesOnSubunitBall =
  unitCoefficientPowerSeriesOnSubunitBall
    atanPowerSeries
    atanPowerSeriesCoefficientBoundOne


evenGeometricPowerSeriesRadius :
  HasPowerSeriesRadius evenGeometricPowerSeries 1⁺
evenGeometricPowerSeriesRadius =
  hasPowerSeriesRadius
    {a = evenGeometricPowerSeries}
    {R = 1⁺}
    (λ ρ ρ<1 →
      evenGeometricPowerSeriesOnSubunitBall ρ ρ<1)


alternatingEvenGeometricPowerSeriesRadius :
  HasPowerSeriesRadius alternatingEvenGeometricPowerSeries 1⁺
alternatingEvenGeometricPowerSeriesRadius =
  hasPowerSeriesRadius
    {a = alternatingEvenGeometricPowerSeries}
    {R = 1⁺}
    (λ ρ ρ<1 →
      alternatingEvenGeometricPowerSeriesOnSubunitBall ρ ρ<1)


atanhPowerSeriesRadius :
  HasPowerSeriesRadius atanhPowerSeries 1⁺
atanhPowerSeriesRadius =
  hasPowerSeriesRadius
    {a = atanhPowerSeries}
    {R = 1⁺}
    (λ ρ ρ<1 →
      atanhPowerSeriesOnSubunitBall ρ ρ<1)


atanPowerSeriesRadius :
  HasPowerSeriesRadius atanPowerSeries 1⁺
atanPowerSeriesRadius =
  hasPowerSeriesRadius
    {a = atanPowerSeries}
    {R = 1⁺}
    (λ ρ ρ<1 →
      atanPowerSeriesOnSubunitBall ρ ρ<1)
