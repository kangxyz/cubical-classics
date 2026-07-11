{-

Arctangent power series on the strict subunit ball

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Arctangent where

open import Constructive.Analysis.Reals.PowerSeries.Elementary.Arctangent.Coefficients
  public
  using
    ( alternatingEvenGeometricPowerSeries
    ; atanPowerSeries
    ; derivativePowerSeries-atan
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Arctangent.Bounds
  public
  using
    ( alternatingEvenGeometricPowerSeriesCoefficientBoundOne
    ; atanPowerSeriesCoefficientBoundOne
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Arctangent.Convergence
  public
  using (atanPowerSeriesOnSubunitBallWith)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Arctangent.Analytic
  public
  using (atanᶜWithinSubunitBall)
