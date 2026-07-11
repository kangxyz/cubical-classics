{-

Local arctangent function on subunit balls

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Arctangent.Analytic where

import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.GeometricDecay
  using (positiveGeometricPowerModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
  using (0ᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Base
  using (centeredPowerSeriesWithinBallFunction)
open import Constructive.Analysis.Reals.PowerSeries.Convergence
  using (HasPowerSeriesOnBallWith)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Arctangent.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Arctangent.Convergence
open import Constructive.Analysis.Reals.PowerSeries.Radius.Centered
  using (InPowerSeriesBall)
open import Constructive.Data.PositiveRationals
  using (ℚ⁺ ; radius)
import Constructive.Data.Rationals as Rational


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
