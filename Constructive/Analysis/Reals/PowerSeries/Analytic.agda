{-

Function-facing analytic power-series data

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Analytic where

open import Constructive.Analysis.Reals.PowerSeries.Analytic.Base
  public
  using
    ( HasPowerSeriesAtWith
    ; HasPowerSeriesAtWithBounds
    ; HasPowerSeriesAtOnBall
    ; HasPowerSeriesAt
    ; AnalyticAt
    ; centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
    ; centeredPowerSeriesSumEverywhereAnalyticAt
    ; HasPowerSeriesWithinAtWith
    ; HasPowerSeriesWithinAtWithBounds
    ; HasPowerSeriesWithinAtOnBall
    ; HasPowerSeriesWithinAt
    ; AnalyticWithinAt
    ; centeredPowerSeriesWithinBallFunction
    ; centeredPowerSeriesWithinBallHasPowerSeriesWithinAtWith
    ; centeredPowerSeriesWithinBallAnalyticWithinAt
    )
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Continuity
  public
  using
    ( HasPowerSeriesAtUniformlyContinuousOnBallWith
    ; HasPowerSeriesAtUniformlyContinuousOnBall
    ; HasPowerSeriesAtContinuousAtWith
    ; HasPowerSeriesAtContinuousAt
    ; HasPowerSeriesWithinAtUniformlyContinuousOnBallWith
    ; HasPowerSeriesWithinAtUniformlyContinuousOnBall
    ; HasPowerSeriesWithinAtContinuousAtWith
    ; HasPowerSeriesWithinAtContinuousAt
    )
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Algebra
  public
  using
    ( hasPowerSeriesAtWith-congFunction
    ; hasPowerSeriesAtWith-neg
    ; hasPowerSeriesAtWith-add
    ; hasPowerSeriesAtWith-sub
    ; hasPowerSeriesAtWith-rationalScale
    ; hasPowerSeriesAtWith-realScale
    ; hasPowerSeriesAtWith-cauchyProductFromMajorants
    ; hasPowerSeriesWithinAtWith-cauchyProductFromMajorants
    )
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Consequences
  public
  using
    ( hasPowerSeriesAtWith→hasDerivativeAtWithFromLocalModel
    ; hasPowerSeriesAtWith→hasDerivativeAtWithFromEverywhereModel
    ; hasPowerSeriesAtWithBounds→uniformlyContinuousOnBall
    ; hasPowerSeriesWithinAtWithBounds→uniformlyContinuousOnBall
    ; hasPowerSeriesAtWithBounds→continuousAt
    ; hasPowerSeriesWithinAtWithBounds→continuousAt
    )
