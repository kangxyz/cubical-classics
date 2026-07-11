{-

Power-series coefficients, convergence, bounds, and algebra

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Core where

open import Constructive.Analysis.Reals.PowerSeries.Base
  public
  using
    ( PowerSeries
    ; powerSeriesTerm
    ; powerSeriesPartialSum
    ; powerSeriesTerm-cong
    ; powerSeriesTerm-cong-coefficients
    ; powerSeriesPartialSum-cong
    ; PowerSeriesTailBound
    ; powerSeriesSumFromFiniteTailBound
    ; powerSeriesConvergesFromFiniteTailBound
    )
open import Constructive.Analysis.Reals.PowerSeries.Convergence
  public
  using
    ( HasPowerSeriesOnBallWith
    ; hasPowerSeriesOnBallWith
    ; HasPowerSeriesOnBall
    ; powerSeriesSumOnBall
    ; powerSeriesConvergesOnBall
    ; powerSeriesSumOnBallFrom
    ; powerSeriesSumOnBall-bound-independent
    ; powerSeriesSumOnBall-center-path
    ; powerSeriesSumOnBall-data-independent
    ; powerSeriesSumOnBallFrom-data-independent
    ; powerSeriesSumOnBall-coefficients-path
    ; powerSeriesSumOnBallFrom-coefficients-path
    ; hasPowerSeriesOnBallWith-cong
    ; hasPowerSeriesOnBall-cong
    ; hasPowerSeriesOnSmallerBallWith
    ; HasPowerSeriesRadius
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius.Everywhere
  public
  using
    ( HasInfinitePowerSeriesRadius
    ; hasInfinitePowerSeriesRadius→radius
    ; hasPowerSeriesRadius-cong
    ; hasInfinitePowerSeriesRadius-cong
    ; powerSeriesSumEverywhere
    ; powerSeriesSumEverywhere-bound-path
    ; powerSeriesSumEverywhere-coefficients-path
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius.Centered
  public
  using
    ( centeredDisplacement
    ; centeredDisplacement-zero
    ; centeredDisplacement-center-plus
    ; add-center-centeredDisplacement
    ; add-center-centeredDisplacement-forward
    ; InPowerSeriesBall
    ; inPowerSeriesBallAtZeroFromBound
    ; inPowerSeriesBallAtZero→bound
    ; inPowerSeriesBallAtCenterPlusFromBound
    ; centeredPowerSeriesSumOnBall
    ; centeredPowerSeriesSumOnBallAtZero-path
    ; centeredPowerSeriesSumOnBallAtCenterPlus-path
    ; centeredPowerSeriesSumOnBall-inBall-independent
    ; centeredPowerSeriesSumOnBall-data-independent
    ; centeredPowerSeriesSumOnBallFrom
    ; centeredPowerSeriesSumOnBallFrom-data-independent
    ; centeredPowerSeriesSumEverywhere
    ; centeredPowerSeriesSumEverywhere-bound-path
    ; centeredPowerSeriesSumEverywhere-coefficients-path
    )
open import Constructive.Analysis.Reals.PowerSeries.Bounds
  public
  using
    ( PowerSeriesCoefficientBoundsWith
    ; PowerSeriesCoefficientBounds
    ; powerSeriesCoefficientFromRationalProbe
    ; powerSeriesCoefficientBoundsFromRationalProbeTermBoundsWith
    ; powerSeriesCoefficientBoundsFromBallTermBoundsWith
    ; powerSeriesCoefficientBoundsFromBallTermBounds
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  public
  using
    ( PowerSeriesMajorizedOnBall
    ; powerSeriesMajorizedOnBall-cong
    ; powerSeriesMajorizedOnBallFromTermBounds
    ; powerSeriesMajorizedOnBallFromBoundedTerms
    ; majorizedOnBall→hasPowerSeriesOnBallWith
    ; majorizedOnBall→hasPowerSeriesOnBall
    )
open import Constructive.Analysis.Reals.PowerSeries.Algebra.Coefficients
  public
  using
    ( zeroPowerSeries
    ; constantPowerSeries
    ; addPowerSeries
    ; negPowerSeries
    ; subPowerSeries
    ; rationalScalePowerSeries
    ; realScalePowerSeries
    ; shiftPowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.Algebra.ZeroConstant
  public
  using
    ( zeroPowerSeriesOnBallWith
    ; zeroPowerSeriesOnBall
    ; zeroPowerSeriesRadius
    ; zeroPowerSeriesInfiniteRadius
    ; constantPowerSeriesOnBallWith
    ; constantPowerSeriesOnBall
    ; constantPowerSeriesRadius
    ; constantPowerSeriesInfiniteRadius
    )
open import Constructive.Analysis.Reals.PowerSeries.Algebra.Additive
  public
  using
    ( addPowerSeriesOnBallWithMax
    ; addPowerSeriesOnBall
    ; powerSeriesSumOnBallFrom-add
    ; subPowerSeriesOnBallWithMax
    ; subPowerSeriesOnBall
    ; powerSeriesSumOnBallFrom-sub
    )
open import Constructive.Analysis.Reals.PowerSeries.Algebra.Sums
  public
  using
    ( powerSeriesSumOnBall-zero
    ; centeredDisplacement-center
    ; centeredPowerSeriesSumOnBall-center
    ; centeredPowerSeriesSumEverywhere-center
    ; negPowerSeriesOnBallWith
    ; negPowerSeriesOnBall
    ; powerSeriesSumOnBallFrom-neg
    )
open import Constructive.Analysis.Reals.PowerSeries.Algebra.Scaling
  public
  using
    ( rationalScalePowerSeriesOnBallWith
    ; rationalScalePowerSeriesOnBall
    ; realScalePowerSeriesOnBallWith
    ; realScalePowerSeriesOnBall
    ; powerSeriesSumOnBallFrom-rationalScale
    ; powerSeriesSumOnBallFrom-realScale
    )
open import Constructive.Analysis.Reals.PowerSeries.Algebra.InputScaling
  public
  using
    ( inputScalePowerSeries
    ; inputScalePowerSeriesTerm
    ; inputScalePowerSeriesOnBallWith
    ; powerSeriesSumOnBall-inputScale
    )
open import Constructive.Analysis.Reals.PowerSeries.Algebra.Entire
  public
  using
    ( negPowerSeriesRadius
    ; addPowerSeriesRadius
    ; subPowerSeriesRadius
    ; rationalScalePowerSeriesRadius
    ; realScalePowerSeriesRadius
    ; negPowerSeriesInfiniteRadius
    ; addPowerSeriesInfiniteRadius
    ; subPowerSeriesInfiniteRadius
    ; rationalScalePowerSeriesInfiniteRadius
    ; realScalePowerSeriesInfiniteRadius
    ; centeredPowerSeriesSumEverywhere-neg
    ; centeredPowerSeriesSumEverywhere-add
    ; centeredPowerSeriesSumEverywhere-sub
    ; centeredPowerSeriesSumEverywhere-rationalScale
    ; centeredPowerSeriesSumEverywhere-realScale
    )
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct
  public
  using
    ( cauchyProductPowerSeries
    ; cauchyProductPowerSeries-zero
    ; cauchyProductPowerSeries-suc
    ; cauchyProductPowerSeries-suc-right
    ; cauchyProductPowerSeries-cong
    ; cauchyProductPowerSeries-cong-left
    ; cauchyProductPowerSeries-zero-left
    ; cauchyProductPowerSeries-zero-right
    ; cauchyProductPowerSeries-constant-left
    ; cauchyProductPowerSeries-one-left
    ; cauchyProductPowerSeries-comm
    ; cauchyProductPowerSeries-add-left
    ; cauchyProductPowerSeries-neg-left
    ; cauchyProductPowerSeries-sub-left
    ; cauchyProductPowerSeries-rationalScale-left
    ; cauchyProductPowerSeriesOnBallWithFromMajorants
    ; cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTail
    )
open import Constructive.Analysis.Reals.PowerSeries.FormalDerivative
  public
  using
    ( naturalReal
    ; inverseSucReal
    ; derivativePowerSeries
    ; primitivePowerSeries
    ; derivativePowerSeriesCoefficient
    ; derivativePowerSeries-cong
    ; primitivePowerSeriesCoefficient-zero
    ; primitivePowerSeriesCoefficient-suc
    ; derivativePowerSeriesTerm
    ; derivativePowerSeries-zero
    ; derivativePowerSeries-constant
    ; derivativePowerSeries-add
    ; derivativePowerSeries-neg
    ; derivativePowerSeries-sub
    ; derivativePowerSeries-rationalScale
    ; derivativePowerSeries-realScale
    ; derivativePrimitivePowerSeries
    ; primitiveDerivativePowerSeries-suc
    ; primitiveDerivativePowerSeries
    ; primitivePowerSeries-zero
    ; primitivePowerSeries-add
    ; primitivePowerSeries-neg
    ; primitivePowerSeries-sub
    ; primitivePowerSeries-rationalScale
    ; primitivePowerSeries-realScale
    )
