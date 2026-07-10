{-

Function-level consequences of power-series expansions

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Analytic.Consequences.Theorem where

open import Constructive.Analysis.Reals.PowerSeries.Analytic.Consequences.Core public
  using
    ( hasPowerSeriesWithinAtWith-congFunction
    ; hasPowerSeriesAtWith→hasDerivativeAtWithFromLocalModel
    ; hasPowerSeriesAtWith→hasDerivativeAtWithFromEverywhereModel
    ; hasPowerSeriesAtWithBounds→uniformlyContinuousOnBall
    ; hasPowerSeriesAtWithBounds→merelyUniformlyContinuousOnBall
    ; hasPowerSeriesWithinAtWithBounds→uniformlyContinuousOnBall
    ; hasPowerSeriesWithinAtWithBounds→merelyUniformlyContinuousOnBall
    ; hasPowerSeriesAtWith→continuousAt
    ; hasPowerSeriesAtWithBounds→continuousAt
    ; hasPowerSeriesAtWithBounds→merelyContinuousAt
    ; hasPowerSeriesWithinAtWith→continuousAt
    ; hasPowerSeriesWithinAtWithBounds→continuousAt
    ; hasPowerSeriesWithinAtWithBounds→merelyContinuousAt
    )
