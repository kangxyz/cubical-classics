{-

Uniform domain derivatives of log(1+x) on strict subunit balls

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.LogOnePlusDerivative where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; suc)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.Derivative.BoundedSegment.Margin
  using (boundedSecondDerivativeMarginModulus)
open import Constructive.Analysis.Reals.Calculus.Derivative.Domain.Base
  using (HasDerivativeWithinDomainAtWith)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
  using (scalarMulᶜ-rational)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.PowerSeries.Bounds
  using (positiveRationalSelfBounded)
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using (derivativePowerSeries ; derivativePowerSeries-cong)
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.Estimates
  using
    ( derivativeStrictSubballModulus
    ; derivativeStrictSubballScale
    )
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.StrictSubball.Core
  using
    ( derivativePowerSeriesMajorizedOnStrictSubballFromMajorizedOnBall
    ; derivativePowerSeriesStrictSubballMajorant
    )
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Majorants
  using (unitCoefficientPowerSeriesMajorizedOnBall)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Geometric
  using (alternatingGeometricPowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.Base
  using
    ( alternatingGeometricPowerSeriesCoefficientBoundOne
    ; derivativePowerSeries-logOnePlus
    ; logOnePlusPowerSeries
    ; logOnePlusPowerSeriesOnSubunitBallWith
    ; logOnePlusᶜWithinSubunitBall
    )
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.GeometricBridge
  using (logOnePlusDerivativePowerSeriesOnSubunitBallWith)
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using (PowerSeriesMajorizedOnBall ; powerSeriesMajorizedOnBall-cong)
open import Constructive.Analysis.Reals.PowerSeries.Radius
  using
    ( centeredPowerSeriesSumOnBallAtZero-path
    ; inPowerSeriesBallAtZeroFromBound
    ; powerSeriesSumOnBall
    )
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.SecondDerivativePartialSumBounds.Finite
  using (PowerSeriesSecondDerivativePartialSumsBoundOnBall)
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.SecondDerivativePartialSumBounds.MajorizedRational
  using
    ( powerSeriesSecondDerivativePartialSumsBoundOnBallFromMajorizedRationalBounds
    )
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.UniformPartialSums
  using (partialSumsDerivativeTargetModulus)
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Within.Core
  using
    ( powerSeriesSumWithinDomainFormalDerivativeAtWithFromSecondDerivativeBound
    )
open import Constructive.Analysis.GeometricDecay
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
open import Constructive.Data.PositiveRationals
  using
    ( ℚ⁺
    ; 1⁺
    ; radius
    ; _⊖_[_]
    ; _+⁺_
    ; _*⁺_
    ; half⁺
    ; half<
    ; quarter⁺
    ; sum<from-difference
    )
import Constructive.Data.Rationals as Rational


private
  derivativeMajorantBound :
    {rho sigma : ℚ⁺} →
    (rho<sigma : radius rho ℚOrder.< radius sigma) →
    (n : ℕ) →
    BoundedByᶜ
      (derivativeStrictSubballScale rho sigma rho<sigma *⁺
        positivePower sigma (suc n))
      (derivativePowerSeriesStrictSubballMajorant
        rho<sigma
        (positiveGeometricTerm sigma)
        n)
  derivativeMajorantBound
    {rho = rho}
    {sigma = sigma}
    rho<sigma
    n =
    subst
      (BoundedByᶜ bound)
      (sym
        (scalarMulᶜ-rational
          (radius (derivativeStrictSubballScale rho sigma rho<sigma))
          (radius (positivePower sigma (suc n)))))
      (positiveRationalSelfBounded bound)
    where
    bound : ℚ⁺
    bound =
      derivativeStrictSubballScale rho sigma rho<sigma *⁺
      positivePower sigma (suc n)

  logSecondDerivativeMajorizedOnStrictSubball :
    {rho sigma : ℚ⁺} →
    (rho<sigma : radius rho ℚOrder.< radius sigma) →
    (sigma<1 : radius sigma ℚOrder.< Rational.1ℚ) →
    PowerSeriesMajorizedOnBall
      (derivativePowerSeries (derivativePowerSeries logOnePlusPowerSeries))
      rho
      (derivativePowerSeriesStrictSubballMajorant
        rho<sigma
        (positiveGeometricTerm sigma))
      (derivativeStrictSubballModulus
        rho<sigma
        (positiveGeometricPowerModulus sigma sigma<1))
  logSecondDerivativeMajorizedOnStrictSubball rho<sigma sigma<1 =
    powerSeriesMajorizedOnBall-cong
      (λ n →
        sym
          (derivativePowerSeries-cong
            derivativePowerSeries-logOnePlus
            n))
      (derivativePowerSeriesMajorizedOnStrictSubballFromMajorizedOnBall
        rho<sigma
        (unitCoefficientPowerSeriesMajorizedOnBall
          alternatingGeometricPowerSeries
          alternatingGeometricPowerSeriesCoefficientBoundOne
          _
          sigma<1))


logOnePlusDerivativeMargin :
  (rho : ℚ⁺) →
  radius rho ℚOrder.< Rational.1ℚ →
  ℚ⁺
logOnePlusDerivativeMargin rho rho<1 =
  quarter⁺ (1⁺ ⊖ rho [ rho<1 ])


private
  outerRadius :
    (rho : ℚ⁺) →
    radius rho ℚOrder.< Rational.1ℚ →
    ℚ⁺
  outerRadius rho rho<1 =
    rho +⁺ half⁺ (1⁺ ⊖ rho [ rho<1 ])

  outerRadius<1 :
    (rho : ℚ⁺) →
    (rho<1 : radius rho ℚOrder.< Rational.1ℚ) →
    radius (outerRadius rho rho<1) ℚOrder.< Rational.1ℚ
  outerRadius<1 rho rho<1 =
    sum<from-difference 1⁺ rho (half⁺ gap) rho<1 (half< gap)
    where
    gap : ℚ⁺
    gap =
      1⁺ ⊖ rho [ rho<1 ]

  inner<outer :
    (rho : ℚ⁺) →
    (rho<1 : radius rho ℚOrder.< Rational.1ℚ) →
    radius (rho +⁺ logOnePlusDerivativeMargin rho rho<1) ℚOrder.<
    radius (outerRadius rho rho<1)
  inner<outer rho rho<1 =
    ℚOrder.<-o+
      (radius (quarter⁺ gap))
      (radius (half⁺ gap))
      (radius rho)
      (half< (half⁺ gap))
    where
    gap : ℚ⁺
    gap =
      1⁺ ⊖ rho [ rho<1 ]


logOnePlusSecondDerivativePartialSumsBoundData :
  (rho : ℚ⁺) →
  (rho<1 : radius rho ℚOrder.< Rational.1ℚ) →
  PowerSeriesSecondDerivativePartialSumsBoundOnBall
    logOnePlusPowerSeries
    (rho +⁺ logOnePlusDerivativeMargin rho rho<1)
logOnePlusSecondDerivativePartialSumsBoundData rho rho<1 =
  powerSeriesSecondDerivativePartialSumsBoundOnBallFromMajorizedRationalBounds
    (logSecondDerivativeMajorizedOnStrictSubball
      (inner<outer rho rho<1)
      (outerRadius<1 rho rho<1))
    (derivativeMajorantBound (inner<outer rho rho<1))


logOnePlusWithinDerivativeModulus :
  (rho : ℚ⁺) →
  (rho<1 : radius rho ℚOrder.< Rational.1ℚ) →
  PrecisionModulus
logOnePlusWithinDerivativeModulus rho rho<1 =
  partialSumsDerivativeTargetModulus
    (boundedSecondDerivativeMarginModulus
      (logOnePlusDerivativeMargin rho rho<1)
      (logOnePlusSecondDerivativePartialSumsBoundData rho rho<1 .fst))


logOnePlusᶜWithinSubunitBallHasDerivativeWithinDomainAtWith :
  (rho : ℚ⁺) →
  (rho<1 : radius rho ℚOrder.< Rational.1ℚ) →
  (x : ℝᶜ) →
  (x-bound : BoundedByᶜ rho x) →
  HasDerivativeWithinDomainAtWith
    {D = BoundedByᶜ rho}
    (λ y y-bound →
      logOnePlusᶜWithinSubunitBall
        rho
        rho<1
        y
        (inPowerSeriesBallAtZeroFromBound y-bound))
    x
    x-bound
    (powerSeriesSumOnBall
      (derivativePowerSeries logOnePlusPowerSeries)
      rho
      (positiveGeometricPowerModulus rho rho<1)
      (logOnePlusDerivativePowerSeriesOnSubunitBallWith rho rho<1)
      x
      x-bound)
    (logOnePlusWithinDerivativeModulus rho rho<1)
logOnePlusᶜWithinSubunitBallHasDerivativeWithinDomainAtWith
  rho
  rho<1
  x
  x-bound =
  powerSeriesSumWithinDomainFormalDerivativeAtWithFromSecondDerivativeBound
    (logOnePlusPowerSeriesOnSubunitBallWith rho rho<1)
    (logOnePlusDerivativePowerSeriesOnSubunitBallWith rho rho<1)
    (λ y y-bound → y-bound)
    (λ y y-bound →
      centeredPowerSeriesSumOnBallAtZero-path
        (logOnePlusPowerSeriesOnSubunitBallWith rho rho<1)
        y
        y-bound)
    x-bound
    (logOnePlusSecondDerivativePartialSumsBoundData rho rho<1 .snd)
