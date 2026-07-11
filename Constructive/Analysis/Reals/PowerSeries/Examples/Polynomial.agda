{-

Finite-support power series

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Examples.Polynomial where

open import Constructive.Analysis.Reals.PowerSeries.Examples.Polynomial.FiniteSupport
  public
  using
    ( PowerSeriesZeroAfter
    ; IsPolynomialPowerSeries
    ; powerSeriesZeroAfter-weaken
    ; finiteSupportPowerSeriesInfiniteRadius
    ; polynomialPowerSeriesInfiniteRadius
    )
open import Constructive.Analysis.Reals.PowerSeries.Examples.Polynomial.Closure
  public
  using
    ( addPowerSeriesPolynomial
    ; negPowerSeriesPolynomial
    ; subPowerSeriesPolynomial
    ; cauchyProductPowerSeriesPolynomial
    ; zeroPowerSeriesPolynomial
    ; constantPowerSeriesPolynomial
    )
open import Constructive.Analysis.Reals.PowerSeries.Examples.Polynomial.FiniteSeries
  public
  using
    ( finitePowerSeries
    ; finitePowerSeriesEval
    ; finitePowerSeriesZeroAfter
    ; finitePowerSeriesEvalAnalyticAt
    ; finitePowerSeriesPolynomial
    ; finitePowerSeriesInfiniteRadius
    ; monomialPowerSeries
    ; monomialPowerSeriesZeroAfter
    ; monomialPowerSeriesPolynomial
    ; monomialPowerSeriesInfiniteRadius
    )
open import Constructive.Analysis.Reals.PowerSeries.Examples.Polynomial.Derivative
  public
  using
    ( derivativePowerSeriesZeroAfter
    ; derivativePowerSeriesPolynomial
    ; finitePowerSeriesFormalDerivativeEval
    ; finitePowerSeriesFormalDerivativeAnalyticAt
    ; derivativePowerSeriesPolynomialInfiniteRadius
    )
open import Constructive.Analysis.Reals.PowerSeries.Examples.Polynomial.Primitive
  public
  using
    ( primitivePowerSeriesZeroAfter
    ; primitivePowerSeriesPolynomial
    ; finitePowerSeriesFormalPrimitiveEval
    ; finitePowerSeriesFormalPrimitiveAnalyticAt
    ; primitivePowerSeriesPolynomialInfiniteRadius
    )
open import Constructive.Analysis.Reals.PowerSeries.Examples.Polynomial.Scaling
  public
  using
    ( rationalScalePowerSeriesZeroAfter
    ; rationalScalePowerSeriesPolynomial
    )
