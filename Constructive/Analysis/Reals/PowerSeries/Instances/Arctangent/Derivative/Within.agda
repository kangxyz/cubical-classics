{-

Uniform domain derivatives of atanh on strict subunit balls

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Derivative.Within where

open import Cubical.Foundations.Prelude

import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.Derivative.BoundedSegment.Margin
  using (boundedSecondDerivativeMarginModulus)
open import Constructive.Analysis.Reals.Calculus.Derivative.Domain.Base
  using (HasDerivativeWithinDomainAtWith)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using (derivativePowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Coefficients
  using (atanhPowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Convergence
  using
    ( atanhDerivativePowerSeriesOnSubunitBallWith
    ; atanhPowerSeriesOnSubunitBallWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Derivative.Bounds
  using (atanhSecondDerivativePartialSumsBoundOnStrictSubball)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.Global
  using (atanhᶜFromSubunitBound)
open import Constructive.Analysis.Reals.PowerSeries.Radius
  using
    ( HasPowerSeriesOnBallWith
    ; hasPowerSeriesOnBallWith-cong
    ; powerSeriesSumOnBall
    )
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.UniformPartialSums
  using (partialSumsDerivativeTargetModulus)
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.SecondDerivativePartialSumBounds.Finite
  using (PowerSeriesSecondDerivativePartialSumsBoundOnBall)
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Within.Core
  using
    ( powerSeriesSumWithinDomainFormalDerivativeAtWithFromSecondDerivativeBound
    )
open import Constructive.Analysis.GeometricDecay
  using (positiveGeometricPowerModulus)
open import Constructive.Data.PositiveRationals
  using
    ( ℚ⁺
    ; 1⁺
    ; radius
    ; _⊖_[_]
    ; _+⁺_
    ; half⁺
    ; half<
    ; quarter⁺
    ; sum<from-difference
    )
import Constructive.Data.Rationals as Rational


atanhDerivativeMargin :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  ℚ⁺
atanhDerivativeMargin ρ ρ<1 =
  quarter⁺ (1⁺ ⊖ ρ [ ρ<1 ])


atanhDerivativeOuterRadius :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  ℚ⁺
atanhDerivativeOuterRadius ρ ρ<1 =
  ρ +⁺ half⁺ (1⁺ ⊖ ρ [ ρ<1 ])


private
  atanhDerivativeOuterRadius<1 :
    (ρ : ℚ⁺) →
    (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    radius (atanhDerivativeOuterRadius ρ ρ<1) ℚOrder.< Rational.1ℚ
  atanhDerivativeOuterRadius<1 ρ ρ<1 =
    sum<from-difference
      1⁺
      ρ
      (half⁺ gap)
      ρ<1
      (half< gap)
    where
    gap : ℚ⁺
    gap =
      1⁺ ⊖ ρ [ ρ<1 ]

  atanhDerivativeInner<Outer :
    (ρ : ℚ⁺) →
    (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    radius (ρ +⁺ atanhDerivativeMargin ρ ρ<1) ℚOrder.<
    radius (atanhDerivativeOuterRadius ρ ρ<1)
  atanhDerivativeInner<Outer ρ ρ<1 =
    ℚOrder.<-o+
      (radius (quarter⁺ gap))
      (radius (half⁺ gap))
      (radius ρ)
      (half< (half⁺ gap))
    where
    gap : ℚ⁺
    gap =
      1⁺ ⊖ ρ [ ρ<1 ]


atanhSecondDerivativePartialSumsBoundData :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PowerSeriesSecondDerivativePartialSumsBoundOnBall
    atanhPowerSeries
    (ρ +⁺ atanhDerivativeMargin ρ ρ<1)
atanhSecondDerivativePartialSumsBoundData ρ ρ<1 =
  atanhSecondDerivativePartialSumsBoundOnStrictSubball
    (atanhDerivativeInner<Outer ρ ρ<1)
    (atanhDerivativeOuterRadius<1 ρ ρ<1)


atanhWithinDerivativeModulus :
  (ρ : ℚ⁺) →
  (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PrecisionModulus
atanhWithinDerivativeModulus ρ rho<1 =
  partialSumsDerivativeTargetModulus
    (boundedSecondDerivativeMarginModulus
      (atanhDerivativeMargin ρ rho<1)
      (atanhSecondDerivativePartialSumsBoundData ρ rho<1 .fst))


atanhᶜFromSubunitBoundHasDerivativeWithinDomainAtWith :
  (ρ : ℚ⁺) →
  (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (x : ℝᶜ) →
  (x-bound : BoundedByᶜ ρ x) →
  HasDerivativeWithinDomainAtWith
    {D = BoundedByᶜ ρ}
    (atanhᶜFromSubunitBound ρ rho<1)
    x
    x-bound
    (powerSeriesSumOnBall
      (derivativePowerSeries atanhPowerSeries)
      ρ
      (positiveGeometricPowerModulus ρ rho<1)
      (atanhDerivativePowerSeriesOnSubunitBallWith ρ rho<1)
      x
      x-bound)
    (atanhWithinDerivativeModulus ρ rho<1)
atanhᶜFromSubunitBoundHasDerivativeWithinDomainAtWith
  ρ
  rho<1
  x
  x-bound =
  powerSeriesSumWithinDomainFormalDerivativeAtWithFromSecondDerivativeBound
    (atanhPowerSeriesOnSubunitBallWith ρ rho<1)
    (atanhDerivativePowerSeriesOnSubunitBallWith ρ rho<1)
    (λ y y-bound → y-bound)
    (λ y y-bound → refl)
    x-bound
    (atanhSecondDerivativePartialSumsBoundData ρ rho<1 .snd)
