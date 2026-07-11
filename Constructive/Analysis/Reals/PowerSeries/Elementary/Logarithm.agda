{-

Logarithmic power series and functions

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm where

open import Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.Base
  public
  using
    ( logOnePlusPowerSeries
    ; logOnePlusPowerSeriesCoefficient-zero
    ; derivativePowerSeries-logOnePlus
    ; alternatingGeometricPowerSeriesCoefficientBoundOne
    ; logOnePlusPowerSeriesCoefficientBoundOne
    ; logOnePlusPowerSeriesMajorizedOnBall
    ; logOnePlusPowerSeriesOnSubunitBallWith
    ; logOnePlusᶜWithinSubunitBall
    ; logOnePlusᶜWithinSubunitBall-zero
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.Global
  public
  using
    ( logTransformᶜ
    ; logTransformᶜ-data-independent
    ; LogTransformSubunitDataᶜ
    ; logTransformSubunitDataFromPositiveBoundedᶜ
    ; logᶜ
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.FunctionalEquation
  public
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.GlobalAnalytic
  public
  using (logᶜ-analyticWithinAt)
