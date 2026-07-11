{-

Power-series re-centering infrastructure.

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Recenter where

open import Constructive.Analysis.Reals.PowerSeries.Recenter.Coefficients
  public
  using
    ( recenterCoefficientTerm
    ; recenterCoefficientPartial
    ; RecenterCoefficientConvergenceData
    ; recenterCoefficientSumWith
    ; RecenterPowerSeriesData
    ; recenterPowerSeriesWith
    ; recenterCoefficientConvergenceDataAtZero
    ; recenterPowerSeriesDataAtZero
    ; recenterCoefficientSumAtZero-path
    ; recenterPowerSeriesWithAtZero-path
    )
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Bounds
  public
  using (recenterShiftedDisplacementBound)
open import Constructive.Analysis.Reals.PowerSeries.Recenter.StrictSubball
  public
  using
    ( recenterPowerSeriesDataFromMajorizedOnStrictSubball
    ; recenterPowerSeriesOnStrictSubballFromMajorizedOnBall
    ; centeredPowerSeriesSumRecenteredOnStrictSubball
    )
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Analytic
  public
  using
    ( centeredPowerSeriesWithinBallHasPowerSeriesWithinAtWithFromMajorized
    ; centeredPowerSeriesWithinBallAnalyticWithinAtFromMajorized
    )
