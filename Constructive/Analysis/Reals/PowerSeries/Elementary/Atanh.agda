{-

Hyperbolic arctangent on the strict subunit domain

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh where

open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Coefficients
  public
  using
    ( evenGeometricPowerSeries
    ; atanhPowerSeries
    ; atanhPowerSeriesCoefficient-zero
    ; derivativePowerSeries-atanh
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Bounds
  public
  using
    ( evenGeometricPowerSeriesCoefficientBoundOne
    ; atanhPowerSeriesCoefficientBoundOne
    ; atanhPowerSeriesCoefficientBounds
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Majorants
  public
  using
    ( evenGeometricPowerSeriesMajorizedOnBall
    ; atanhPowerSeriesMajorizedOnBall
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Convergence
  public
  using
    ( evenGeometricPowerSeriesOnSubunitBallWith
    ; atanhPowerSeriesOnSubunitBallWith
    ; atanhDerivativePowerSeriesOnSubunitBallWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Analytic
  public
  using (atanhᶜWithinSubunitBall)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Global
  public
  using
    ( StrictSubunitDataᶜ
    ; atanhᶜFromSubunitBound
    ; atanhᶜFromSubunitBound-data-independent
    ; atanhᶜ
    ; atanhᶜ-data-independent
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Derivative.Reciprocal
  public
  using (atanhDerivativePowerSeriesReciprocalOnBall)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Derivative.Within
  public
  using (atanhᶜFromSubunitBoundHasDerivativeWithinDomainAtWith)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.GlobalAnalytic
  public
  using (atanhᶜAnalyticWithinAt)
