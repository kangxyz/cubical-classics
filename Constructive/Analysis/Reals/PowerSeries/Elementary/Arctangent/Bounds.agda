{-

Coefficient bounds for the arctangent series

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Arctangent.Bounds where

open import Cubical.Data.Nat using (ℕ ; zero ; suc)

open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  using (BoundedByᶜ ; bounded-byᶜ-neg)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Arctangent.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Elementary.CoefficientBounds
  using
    ( oneBoundOne
    ; primitivePowerSeriesCoefficientBoundOne
    ; zeroBoundOne
    )
open import Constructive.Data.PositiveRationals using (1⁺)


alternatingEvenGeometricPowerSeriesCoefficientBoundOne :
  (n : ℕ) →
  BoundedByᶜ 1⁺ (alternatingEvenGeometricPowerSeries n)
alternatingEvenGeometricPowerSeriesCoefficientBoundOne zero =
  oneBoundOne
alternatingEvenGeometricPowerSeriesCoefficientBoundOne (suc zero) =
  zeroBoundOne
alternatingEvenGeometricPowerSeriesCoefficientBoundOne (suc (suc n)) =
  bounded-byᶜ-neg
    1⁺
    (alternatingEvenGeometricPowerSeries n)
    (alternatingEvenGeometricPowerSeriesCoefficientBoundOne n)


atanPowerSeriesCoefficientBoundOne :
  (n : ℕ) →
  BoundedByᶜ 1⁺ (atanPowerSeries n)
atanPowerSeriesCoefficientBoundOne =
  primitivePowerSeriesCoefficientBoundOne
    alternatingEvenGeometricPowerSeries
    alternatingEvenGeometricPowerSeriesCoefficientBoundOne
