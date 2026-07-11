{-

Formal exponential power-series coefficients

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Exponential where

open import Constructive.Analysis.Reals.PowerSeries.Elementary.Exponential.Coefficients
  public
  using
    ( expPowerSeries
    ; expPowerSeries-reciprocalFactorial
    ; expPowerSeriesCoefficientBoundOne
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Exponential.Majorant
  public
  using (expPowerSeriesTermBoundByFactorialMajorant)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Exponential.Convergence
  public
  using
    ( derivativePowerSeries-exp
    ; primitivePowerSeries-exp
    ; expPowerSeriesFactorialMajorized
    ; expPowerSeriesInfiniteRadius
    ; expᶜ
    ; expᶜ-zero
    ; expᶜHasPowerSeriesAtWithZero
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Exponential.Derivative
  public
  using
    ( derivativeExpPowerSeriesInfiniteRadius
    ; expᶜHasDerivativeAtWithFromCoefficientBoundsOnSubball
    )
