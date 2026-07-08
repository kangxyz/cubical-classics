{-

Local analytic functions for atanh and atan on subunit balls

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Analytic where

open import Cubical.Foundations.Prelude

import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using (centeredPowerSeriesSumOnBall-center)
open import Constructive.Analysis.Reals.PowerSeries.Analytic
  using
    ( AnalyticWithinAt
    ; HasPowerSeriesWithinAt
    ; HasPowerSeriesWithinAtContinuousAt
    ; HasPowerSeriesWithinAtMerelyContinuousAt
    ; HasPowerSeriesWithinAtMerelyUniformlyContinuousOnBall
    ; HasPowerSeriesWithinAtOnBall
    ; HasPowerSeriesWithinAtUniformlyContinuousOnBall
    ; HasPowerSeriesWithinAtWith
    ; HasPowerSeriesWithinAtWithBounds
    ; centeredPowerSeriesWithinBallAnalyticWithinAt
    ; centeredPowerSeriesWithinBallFunction
    ; centeredPowerSeriesWithinBallHasPowerSeriesWithinAt
    ; centeredPowerSeriesWithinBallHasPowerSeriesWithinAtOnBall
    ; centeredPowerSeriesWithinBallHasPowerSeriesWithinAtWith
    ; hasPowerSeriesWithinAtWithBounds→continuousAt
    ; hasPowerSeriesWithinAtWithBounds→merelyContinuousAt
    ; hasPowerSeriesWithinAtWithBounds→merelyUniformlyContinuousOnBall
    ; hasPowerSeriesWithinAtWithBounds→uniformlyContinuousOnBall
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Bounds
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Convergence
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
  using (positiveGeometricPowerModulus)
open import Constructive.Data.PositiveRationals
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


atanhᶜHasPowerSeriesWithinAtWithBoundsZero :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesWithinAtWithBounds
    (atanhᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    atanhPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
atanhᶜHasPowerSeriesWithinAtWithBoundsZero ρ ρ<1 =
  atanhᶜHasPowerSeriesWithinAtWithZero ρ ρ<1 ,
  atanhPowerSeriesCoefficientBounds


atanᶜHasPowerSeriesWithinAtWithBoundsZero :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesWithinAtWithBounds
    (atanᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    atanPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
atanᶜHasPowerSeriesWithinAtWithBoundsZero ρ ρ<1 =
  atanᶜHasPowerSeriesWithinAtWithZero ρ ρ<1 ,
  atanPowerSeriesCoefficientBounds


atanhᶜWithinSubunitBallUniformlyContinuousFromCoefficientBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesWithinAtUniformlyContinuousOnBall
    (atanhᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    ρ
atanhᶜWithinSubunitBallUniformlyContinuousFromCoefficientBounds ρ ρ<1 =
  hasPowerSeriesWithinAtWithBounds→uniformlyContinuousOnBall
    (atanhᶜHasPowerSeriesWithinAtWithBoundsZero ρ ρ<1)


atanᶜWithinSubunitBallUniformlyContinuousFromCoefficientBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesWithinAtUniformlyContinuousOnBall
    (atanᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    ρ
atanᶜWithinSubunitBallUniformlyContinuousFromCoefficientBounds ρ ρ<1 =
  hasPowerSeriesWithinAtWithBounds→uniformlyContinuousOnBall
    (atanᶜHasPowerSeriesWithinAtWithBoundsZero ρ ρ<1)


atanhᶜWithinSubunitBallMerelyUniformlyContinuousFromBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesWithinAtMerelyUniformlyContinuousOnBall
    (atanhᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    ρ
atanhᶜWithinSubunitBallMerelyUniformlyContinuousFromBounds ρ ρ<1 =
  hasPowerSeriesWithinAtWithBounds→merelyUniformlyContinuousOnBall
    (atanhᶜHasPowerSeriesWithinAtWithBoundsZero ρ ρ<1)


atanᶜWithinSubunitBallMerelyUniformlyContinuousFromBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesWithinAtMerelyUniformlyContinuousOnBall
    (atanᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    ρ
atanᶜWithinSubunitBallMerelyUniformlyContinuousFromBounds ρ ρ<1 =
  hasPowerSeriesWithinAtWithBounds→merelyUniformlyContinuousOnBall
    (atanᶜHasPowerSeriesWithinAtWithBoundsZero ρ ρ<1)


atanhᶜWithinSubunitBallContinuousAtFromCoefficientBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall 0ᶜ ρ x) →
  HasPowerSeriesWithinAtContinuousAt
    (atanhᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    ρ
    x
    x-inBall
    x-inBall
atanhᶜWithinSubunitBallContinuousAtFromCoefficientBounds
  ρ
  ρ<1
  x
  x-inBall =
  hasPowerSeriesWithinAtWithBounds→continuousAt
    (atanhᶜHasPowerSeriesWithinAtWithBoundsZero ρ ρ<1)
    x
    x-inBall
    x-inBall


atanᶜWithinSubunitBallContinuousAtFromCoefficientBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall 0ᶜ ρ x) →
  HasPowerSeriesWithinAtContinuousAt
    (atanᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    ρ
    x
    x-inBall
    x-inBall
atanᶜWithinSubunitBallContinuousAtFromCoefficientBounds
  ρ
  ρ<1
  x
  x-inBall =
  hasPowerSeriesWithinAtWithBounds→continuousAt
    (atanᶜHasPowerSeriesWithinAtWithBoundsZero ρ ρ<1)
    x
    x-inBall
    x-inBall


atanhᶜWithinSubunitBallMerelyContinuousAtFromBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall 0ᶜ ρ x) →
  HasPowerSeriesWithinAtMerelyContinuousAt
    (atanhᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    ρ
    x
    x-inBall
    x-inBall
atanhᶜWithinSubunitBallMerelyContinuousAtFromBounds
  ρ
  ρ<1
  x
  x-inBall =
  hasPowerSeriesWithinAtWithBounds→merelyContinuousAt
    (atanhᶜHasPowerSeriesWithinAtWithBoundsZero ρ ρ<1)
    x
    x-inBall
    x-inBall


atanᶜWithinSubunitBallMerelyContinuousAtFromBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall 0ᶜ ρ x) →
  HasPowerSeriesWithinAtMerelyContinuousAt
    (atanᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    ρ
    x
    x-inBall
    x-inBall
atanᶜWithinSubunitBallMerelyContinuousAtFromBounds
  ρ
  ρ<1
  x
  x-inBall =
  hasPowerSeriesWithinAtWithBounds→merelyContinuousAt
    (atanᶜHasPowerSeriesWithinAtWithBoundsZero ρ ρ<1)
    x
    x-inBall
    x-inBall


atanhᶜHasPowerSeriesWithinAtOnBallZero :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesWithinAtOnBall
    (atanhᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    atanhPowerSeries
    ρ
atanhᶜHasPowerSeriesWithinAtOnBallZero ρ ρ<1 =
  centeredPowerSeriesWithinBallHasPowerSeriesWithinAtOnBall
    atanhPowerSeries
    0ᶜ
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (atanhPowerSeriesOnSubunitBallWith ρ ρ<1)


atanᶜHasPowerSeriesWithinAtOnBallZero :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesWithinAtOnBall
    (atanᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    atanPowerSeries
    ρ
atanᶜHasPowerSeriesWithinAtOnBallZero ρ ρ<1 =
  centeredPowerSeriesWithinBallHasPowerSeriesWithinAtOnBall
    atanPowerSeries
    0ᶜ
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (atanPowerSeriesOnSubunitBallWith ρ ρ<1)


atanhᶜHasPowerSeriesWithinAtZero :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesWithinAt
    (atanhᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    atanhPowerSeries
atanhᶜHasPowerSeriesWithinAtZero ρ ρ<1 =
  centeredPowerSeriesWithinBallHasPowerSeriesWithinAt
    atanhPowerSeries
    0ᶜ
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (atanhPowerSeriesOnSubunitBallWith ρ ρ<1)


atanᶜHasPowerSeriesWithinAtZero :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesWithinAt
    (atanᶜWithinSubunitBall ρ ρ<1)
    0ᶜ
    atanPowerSeries
atanᶜHasPowerSeriesWithinAtZero ρ ρ<1 =
  centeredPowerSeriesWithinBallHasPowerSeriesWithinAt
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
