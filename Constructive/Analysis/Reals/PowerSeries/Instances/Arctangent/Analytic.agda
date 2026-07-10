{-

Local analytic functions for atanh and atan on subunit balls

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Analytic where

open import Cubical.Foundations.Prelude

import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
  using (0ᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using (centeredPowerSeriesSumOnBall-center)
open import Constructive.Analysis.Reals.PowerSeries.Analytic
  using
    ( AnalyticWithinAt
    ; HasPowerSeriesWithinAtWith
    ; centeredPowerSeriesWithinBallAnalyticWithinAt
    ; centeredPowerSeriesWithinBallFunction
    ; centeredPowerSeriesWithinBallHasPowerSeriesWithinAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius
  using (InPowerSeriesBall)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Convergence
open import Constructive.Analysis.GeometricDecay
  using (positiveGeometricPowerModulus)
open import Constructive.Data.PositiveRationals using (ℚ⁺ ; radius)
import Constructive.Data.Rationals as Rational


atanhᶜWithinSubunitBall :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  (x : ℝᶜ) →
  InPowerSeriesBall 0ᶜ ρ x →
  ℝᶜ
atanhᶜWithinSubunitBall ρ ρ<1 =
  centeredPowerSeriesWithinBallFunction
    atanhPowerSeries
    0ᶜ
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (atanhPowerSeriesOnSubunitBallWith ρ ρ<1)


atanᶜWithinSubunitBall :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  (x : ℝᶜ) →
  InPowerSeriesBall 0ᶜ ρ x →
  ℝᶜ
atanᶜWithinSubunitBall ρ ρ<1 =
  centeredPowerSeriesWithinBallFunction
    atanPowerSeries
    0ᶜ
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (atanPowerSeriesOnSubunitBallWith ρ ρ<1)


atanhᶜWithinSubunitBall-zero :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (zero-inBall : InPowerSeriesBall 0ᶜ ρ 0ᶜ) →
  atanhᶜWithinSubunitBall ρ ρ<1 0ᶜ zero-inBall ≡ 0ᶜ
atanhᶜWithinSubunitBall-zero ρ ρ<1 zero-inBall =
  centeredPowerSeriesSumOnBall-center
    (atanhPowerSeriesOnSubunitBallWith ρ ρ<1)
    0ᶜ
    zero-inBall


atanᶜWithinSubunitBall-zero :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (zero-inBall : InPowerSeriesBall 0ᶜ ρ 0ᶜ) →
  atanᶜWithinSubunitBall ρ ρ<1 0ᶜ zero-inBall ≡ 0ᶜ
atanᶜWithinSubunitBall-zero ρ ρ<1 zero-inBall =
  centeredPowerSeriesSumOnBall-center
    (atanPowerSeriesOnSubunitBallWith ρ ρ<1)
    0ᶜ
    zero-inBall


atanhᶜHasPowerSeriesWithinAtWithZero :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesWithinAtWith
    (atanhᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    atanhPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
atanhᶜHasPowerSeriesWithinAtWithZero ρ ρ<1 =
  centeredPowerSeriesWithinBallHasPowerSeriesWithinAtWith
    atanhPowerSeries
    0ᶜ
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (atanhPowerSeriesOnSubunitBallWith ρ ρ<1)


atanᶜHasPowerSeriesWithinAtWithZero :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesWithinAtWith
    (atanᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    atanPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
atanᶜHasPowerSeriesWithinAtWithZero ρ ρ<1 =
  centeredPowerSeriesWithinBallHasPowerSeriesWithinAtWith
    atanPowerSeries
    0ᶜ
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (atanPowerSeriesOnSubunitBallWith ρ ρ<1)


atanhᶜAnalyticWithinAtZero :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  AnalyticWithinAt
    (atanhᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
atanhᶜAnalyticWithinAtZero ρ ρ<1 =
  centeredPowerSeriesWithinBallAnalyticWithinAt
    atanhPowerSeries
    0ᶜ
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (atanhPowerSeriesOnSubunitBallWith ρ ρ<1)


atanᶜAnalyticWithinAtZero :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  AnalyticWithinAt
    (atanᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
atanᶜAnalyticWithinAtZero ρ ρ<1 =
  centeredPowerSeriesWithinBallAnalyticWithinAt
    atanPowerSeries
    0ᶜ
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (atanPowerSeriesOnSubunitBallWith ρ ρ<1)
