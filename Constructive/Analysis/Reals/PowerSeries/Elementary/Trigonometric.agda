{-

Formal sine and cosine power-series coefficients

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Trigonometric where

open import Constructive.Analysis.Reals.PowerSeries.Elementary.Trigonometric.Coefficients
  public
  using
    ( sinPowerSeries
    ; cosPowerSeries
    ; cosPowerSeriesCoefficient-suc
    ; derivativePowerSeries-sin
    ; derivativePowerSeries-cos
    ; primitivePowerSeries-cos
    ; primitivePowerSeries-sin
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Trigonometric.Bounds
  public
  using
    ( sinPowerSeriesCoefficientBoundOne
    ; cosPowerSeriesCoefficientBoundOne
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Trigonometric.Majorants
  public
  using
    ( sinPowerSeriesFactorialMajorized
    ; cosPowerSeriesFactorialMajorized
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Trigonometric.Convergence
  public
  using
    ( sinPowerSeriesInfiniteRadius
    ; cosPowerSeriesInfiniteRadius
    ; sinᶜ
    ; cosᶜ
    ; sinᶜ-zero
    ; cosᶜ-zero
    ; negSinᶜ
    ; negSinᶜ-path
    ; sinᶜHasPowerSeriesAtWithZero
    ; cosᶜHasPowerSeriesAtWithZero
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Trigonometric.Derivative
  public
  using
    ( derivativeSinPowerSeriesInfiniteRadius
    ; derivativeCosPowerSeriesInfiniteRadius
    ; sinᶜHasDerivativeAtWithFromCoefficientBoundsOnSubball
    ; cosᶜHasDerivativeAtWithFromCoefficientBoundsOnSubball
    )
