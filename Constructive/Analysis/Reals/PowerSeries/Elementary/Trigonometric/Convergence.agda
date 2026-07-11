{-

Entire convergence and zero-centered sums for sine and cosine

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Trigonometric.Convergence where

open import Cubical.Foundations.Prelude

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
  using (0ᶜ ; 1ᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
  using (-ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( centeredPowerSeriesSumEverywhere-center
    ; centeredPowerSeriesSumEverywhere-neg
    ; negPowerSeries
    ; negPowerSeriesInfiniteRadius
    )
open import Constructive.Analysis.Reals.PowerSeries.Analytic
  using
    ( HasPowerSeriesAtWith
    ; centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using (majorizedOnBall→hasPowerSeriesOnBallWith)
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals using (ℚ⁺)

open import Constructive.Analysis.Reals.PowerSeries.Elementary.FactorialBounds
  using (factorialMajorantModulus)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Trigonometric.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Trigonometric.Majorants


sinPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius sinPowerSeries
sinPowerSeriesInfiniteRadius ρ =
  factorialMajorantModulus ρ ,
  majorizedOnBall→hasPowerSeriesOnBallWith
    (sinPowerSeriesFactorialMajorized ρ)


cosPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius cosPowerSeries
cosPowerSeriesInfiniteRadius ρ =
  factorialMajorantModulus ρ ,
  majorizedOnBall→hasPowerSeriesOnBallWith
    (cosPowerSeriesFactorialMajorized ρ)


sinᶜ :
  ℝᶜ →
  ℝᶜ
sinᶜ =
  centeredPowerSeriesSumEverywhere
    sinPowerSeries
    0ᶜ
    sinPowerSeriesInfiniteRadius


cosᶜ :
  ℝᶜ →
  ℝᶜ
cosᶜ =
  centeredPowerSeriesSumEverywhere
    cosPowerSeries
    0ᶜ
    cosPowerSeriesInfiniteRadius


sinᶜ-zero :
  sinᶜ 0ᶜ ≡ 0ᶜ
sinᶜ-zero =
  centeredPowerSeriesSumEverywhere-center
    sinPowerSeriesInfiniteRadius
    0ᶜ


cosᶜ-zero :
  cosᶜ 0ᶜ ≡ 1ᶜ
cosᶜ-zero =
  centeredPowerSeriesSumEverywhere-center
    cosPowerSeriesInfiniteRadius
    0ᶜ


negSinᶜ :
  ℝᶜ →
  ℝᶜ
negSinᶜ =
  centeredPowerSeriesSumEverywhere
    (negPowerSeries sinPowerSeries)
    0ᶜ
    (negPowerSeriesInfiniteRadius sinPowerSeriesInfiniteRadius)


negSinᶜ-path :
  (x : ℝᶜ) →
  negSinᶜ x ≡ -ᶜ sinᶜ x
negSinᶜ-path =
  centeredPowerSeriesSumEverywhere-neg
    sinPowerSeriesInfiniteRadius
    0ᶜ


sinᶜHasPowerSeriesAtWithZero :
  (ρ : ℚ⁺) →
  HasPowerSeriesAtWith
    sinᶜ
    0ᶜ
    sinPowerSeries
    ρ
    (sinPowerSeriesInfiniteRadius ρ .fst)
sinᶜHasPowerSeriesAtWithZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
    sinPowerSeriesInfiniteRadius


cosᶜHasPowerSeriesAtWithZero :
  (ρ : ℚ⁺) →
  HasPowerSeriesAtWith
    cosᶜ
    0ᶜ
    cosPowerSeries
    ρ
    (cosPowerSeriesInfiniteRadius ρ .fst)
cosᶜHasPowerSeriesAtWithZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
    cosPowerSeriesInfiniteRadius
