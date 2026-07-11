{-

Convergence and termwise differentiation of power series

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Differentiation where

open import Constructive.Analysis.Reals.PowerSeries.Differentiation.Majorant
  public
  using
    ( DerivativePowerSeriesBoundMajorantOnBall
    ; derivativePowerSeriesOnBallWithFromCoefficientBoundsAndMajorant
    ; derivativePowerSeriesOnBallFromCoefficientBoundsAndMajorant
    ; derivativePowerSeriesOnBallFromCoefficientBoundsAndBoundMajorant
    )
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.StrictSubball
  public
  using
    ( derivativePowerSeriesStrictSubballMajorant
    ; derivativePowerSeriesOnStrictSubballWithFromMajorizedOnBall
    ; derivativePowerSeriesMajorizedOnStrictSubballFromMajorizedOnBall
    ; derivativePowerSeriesOnStrictSubballFromMajorizedOnBall
    )
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.SubballParameters
  public
  using (derivativeStrictSubballFromOnBallModulus)
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.SubballConvergence
  public
  using
    ( derivativePowerSeriesOnStrictSubballWith
    ; derivativePowerSeriesOnStrictSubball
    )
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.Radius
  public
  using
    ( derivativePowerSeriesRadius
    ; derivativePowerSeriesInfiniteRadius
    ; derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    ; primitivePowerSeriesInfiniteRadiusFromCoefficientPath
    )
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.SecondDerivativeBounds
  public
  using
    ( PowerSeriesSecondDerivativePartialSumsBoundOnBall
    ; powerSeriesSecondDerivativePartialSumsBoundOnBallFromConvergence
    )
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.UniformPartialSums
  public
  using (PowerSeriesSecondDerivativePartialSumsBoundOnBallWith)
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.Automatic
  public
  using
    ( centeredPowerSeriesSumEverywhereFormalDerivativeAt
    ; hasPowerSeriesAtWith→formalDerivativeAt
    )
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.Within
  public
  using
    ( powerSeriesSumWithinDomainFormalDerivativeAtWithFromSecondDerivativeBound
    )
