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
