{-

Subunit-ball convergence for arctangent

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Arctangent.Convergence where

import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.GeometricDecay
  using (positiveGeometricPowerModulus)
open import Constructive.Analysis.Reals.PowerSeries.Convergence
  using (HasPowerSeriesOnBallWith)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Arctangent.Bounds
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Arctangent.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Elementary.SubunitMajorant
  using (unitCoefficientPowerSeriesOnSubunitBallWith)
open import Constructive.Data.PositiveRationals
  using (ℚ⁺ ; radius)
import Constructive.Data.Rationals as Rational


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
