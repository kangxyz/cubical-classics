{-# OPTIONS --safe #-}

module Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence where

open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.Core
  public
  using
    ( DerivativePowerSeriesBoundMajorantOnBall
    ; derivativePowerSeriesOnBallWithFromCoefficientBoundsAndMajorant
    ; derivativePowerSeriesOnBallFromCoefficientBoundsAndMajorant
    ; derivativePowerSeriesOnBallFromCoefficientBoundsAndBoundMajorant
    )
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.StrictSubball.Core
  public
  using
    ( derivativePowerSeriesStrictSubballMajorant
    ; derivativePowerSeriesOnStrictSubballWithFromMajorizedOnBall
    ; derivativePowerSeriesMajorizedOnStrictSubballFromMajorizedOnBall
    ; derivativePowerSeriesOnStrictSubballFromMajorizedOnBall
    )
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.StrictSubball.OnBall.Base
  public
  using (derivativeStrictSubballFromOnBallModulus)
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.StrictSubball.OnBall.Tail
  public
  using
    ( derivativePowerSeriesOnStrictSubballWith
    ; derivativePowerSeriesOnStrictSubball
    )
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.Closure
  public
  using
    ( derivativePowerSeriesRadius
    ; derivativePowerSeriesInfiniteRadius
    ; derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    ; primitivePowerSeriesInfiniteRadiusFromCoefficientPath
    )
