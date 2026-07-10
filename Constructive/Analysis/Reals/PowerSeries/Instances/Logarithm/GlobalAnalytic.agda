{-

Analyticity of the global positive logarithm

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.GlobalAnalytic where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (suc ; zero)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Reals.Calculus.Derivative.Domain
  using (domainValueAlongPath)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedDivision
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.PowerSeries.Algebra
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Core
  using (AnalyticWithinAt ; HasPowerSeriesWithinAtWith)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm
  using
    ( logOnePlusPowerSeries
    ; logOnePlusPowerSeriesOnSubunitBallWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.DomainScaling
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.GlobalDerivative
  using (logᶜ-positive-bounded-data-independent)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.LocalAdd
  using (logᶜ-positive-bounded-add-local)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.Global
  using (logᶜ-positive-bounded)
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.Series
  using (partialSum ; partialSum-snoc ; partialSum-zero)
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
  using (positiveGeometricPowerModulus)
open import Constructive.Analysis.Reals.Sequences.Base
  using (maxModulus ; splitModulus)
open import Constructive.Data.PositiveRationals


private
  module AtCenter
    (c : ℝᶜ)
    (c-domain : PositiveBoundedDomainᶜ c)
    where

    cLower : ℚ⁺
    cLower =
      lower c-domain

    expansionRadius : ℚ⁺
    expansionRadius =
      half⁺ cLower

    expansionRadius<cLower :
      radius expansionRadius ℚOrder.< radius cLower
    expansionRadius<cLower =
      half< cLower

    reciprocal =
      reciprocalPositiveᶜ cLower c (lowerBound c-domain)

    reciprocalBound : BoundedByᶜ (posInv⁺ cLower) reciprocal
    reciprocalBound =
      reciprocalPositiveᶜ-posInv-bound
        cLower c (lowerBound c-domain)

    sourceRadius : ℚ⁺
    sourceRadius =
      expansionRadius *⁺ posInv⁺ cLower

    sourceRadius<1 :
      radius sourceRadius ℚOrder.< radius 1⁺
    sourceRadius<1 =
      divideByPositiveStrictSubunitRadius<1
        expansionRadius
        cLower
        expansionRadius<cLower

    sourceModulus =
      positiveGeometricPowerModulus sourceRadius sourceRadius<1

    sourceConvergence =
      logOnePlusPowerSeriesOnSubunitBallWith sourceRadius sourceRadius<1

    scaledSeries : PowerSeries
    scaledSeries =
      inputScalePowerSeries reciprocal logOnePlusPowerSeries

    scaledConvergence :
      HasPowerSeriesOnBallWith
        scaledSeries
        expansionRadius
        sourceModulus
    scaledConvergence =
      inputScalePowerSeriesOnBallWith
        reciprocal
        (posInv⁺ cLower)
        reciprocalBound
        sourceConvergence

    centerValue : ℝᶜ
    centerValue =
      logᶜ-positive-bounded c c-domain

    centerSeries : PowerSeries
    centerSeries =
      constantPowerSeries centerValue

    centerConvergence :
      HasPowerSeriesOnBallWith
        centerSeries
        expansionRadius
        (λ _ → suc zero)
    centerConvergence =
      constantPowerSeriesOnBallWith centerValue

    expansionSeries : PowerSeries
    expansionSeries =
      addPowerSeries centerSeries scaledSeries

    expansionModulus =
      splitModulus (maxModulus (λ _ → suc zero) sourceModulus)

    expansionConvergence :
      HasPowerSeriesOnBallWith
        expansionSeries
        expansionRadius
        expansionModulus
    expansionConvergence =
      addPowerSeriesOnBallWithMax centerConvergence scaledConvergence

    centerSumPath :
      (h : ℝᶜ) →
      (h-bound : BoundedByᶜ expansionRadius h) →
      powerSeriesSumOnBall
        centerSeries
        expansionRadius
        (λ _ → suc zero)
        centerConvergence
        h
        h-bound
      ≡ centerValue
    centerSumPath h h-bound =
      powerSeriesSumOnBall-constantModulusPartialSum
        (suc zero)
        centerConvergence
        h
        h-bound ∙
      partialSum-snoc (powerSeriesTerm centerSeries h) zero ∙
      cong (_+ᶜ powerSeriesTerm centerSeries h zero)
        (partialSum-zero (powerSeriesTerm centerSeries h)) ∙
      add-zero-left (powerSeriesTerm centerSeries h zero) ∙
      constantPowerSeriesTerm-zero centerValue h

    localToScaledSum :
      (h : ℝᶜ) →
      (h-bound : BoundedByᶜ expansionRadius h) →
      let
        u = divideByPositiveᶜ h cLower c (lowerBound c-domain)
        u-bound =
          divideByPositiveᶜ-strictSubunitBound
            expansionRadius
            cLower
            expansionRadius<cLower
            h
            c
            h-bound
            (lowerBound c-domain)
      in
      centeredPowerSeriesSumOnBall
        logOnePlusPowerSeries
        0ᶜ
        sourceRadius
        sourceModulus
        sourceConvergence
        u
        (inPowerSeriesBallAtZeroFromBound u-bound)
      ≡
      powerSeriesSumOnBall
        scaledSeries
        expansionRadius
        sourceModulus
        scaledConvergence
        h
        h-bound
    localToScaledSum h h-bound =
      centeredPowerSeriesSumOnBallAtZero-path
        sourceConvergence
        u
        u-bound ∙
      powerSeriesSumOnBall-center-path
        sourceConvergence
        (mulᶜ-comm h reciprocal)
        u-bound
        rh-bound ∙
      sym
        (powerSeriesSumOnBall-inputScale
          reciprocal
          (posInv⁺ cLower)
          reciprocalBound
          sourceConvergence
          h
          h-bound)
      where
      u =
        divideByPositiveᶜ h cLower c (lowerBound c-domain)

      u-bound : BoundedByᶜ sourceRadius u
      u-bound =
        divideByPositiveᶜ-strictSubunitBound
          expansionRadius
          cLower
          expansionRadius<cLower
          h
          c
          h-bound
          (lowerBound c-domain)

      rh-bound : BoundedByᶜ sourceRadius (reciprocal ·ᶜ h)
      rh-bound =
        subst
          (λ θ → BoundedByᶜ θ (reciprocal ·ᶜ h))
          (*⁺-comm (posInv⁺ cLower) expansionRadius)
          (bounded-byᶜ-mul
            (posInv⁺ cLower)
            expansionRadius
            reciprocal
            h
            reciprocalBound
            h-bound)

    expansionPath :
      (y : ℝᶜ) →
      (y-domain : PositiveBoundedDomainᶜ y) →
      (y-inBall : InPowerSeriesBall c expansionRadius y) →
      logᶜ-positive-bounded y y-domain ≡
      centeredPowerSeriesSumOnBall
        expansionSeries
        c
        expansionRadius
        expansionModulus
        expansionConvergence
        y
        y-inBall
    expansionPath y y-domain y-inBall =
      domainValueAlongPath
        logᶜ-positive-bounded-data-independent
        (sym shifted-path)
        y-domain
        shifted-domain ∙
      logᶜ-positive-bounded-add-local
        c
        h
        c-domain
        shifted-domain
        expansionRadius
        h-bound
        expansionRadius<cLower ∙
      cong (centerValue +ᶜ_) (localToScaledSum h h-bound) ∙
      cong (_+ᶜ scaledSum) (sym (centerSumPath h h-bound)) ∙
      sym
        (powerSeriesSumOnBall-addWithMax
          centerConvergence
          scaledConvergence
          h
          h-bound)
      where
      h : ℝᶜ
      h =
        centeredDisplacement c y

      h-bound : BoundedByᶜ expansionRadius h
      h-bound =
        InPowerSeriesBall.displacementBound y-inBall

      shifted-path : c +ᶜ h ≡ y
      shifted-path =
        add-center-centeredDisplacement c y

      shifted-domain : PositiveBoundedDomainᶜ (c +ᶜ h)
      shifted-domain =
        subst PositiveBoundedDomainᶜ (sym shifted-path) y-domain

      scaledSum : ℝᶜ
      scaledSum =
        powerSeriesSumOnBall
          scaledSeries
          expansionRadius
          sourceModulus
          scaledConvergence
          h
          h-bound

    expansion :
      HasPowerSeriesWithinAtWith
        {D = PositiveBoundedDomainᶜ}
        logᶜ-positive-bounded
        c
        expansionSeries
        expansionRadius
        expansionModulus
    expansion =
      expansionConvergence , expansionPath


logᶜ-positive-bounded-analyticWithinAt :
  (c : ℝᶜ) →
  (c-domain : PositiveBoundedDomainᶜ c) →
  AnalyticWithinAt
    {D = PositiveBoundedDomainᶜ}
    logᶜ-positive-bounded
    c
logᶜ-positive-bounded-analyticWithinAt c c-domain =
  AtCenter.expansionSeries c c-domain ,
  AtCenter.expansionRadius c c-domain ,
  AtCenter.expansionModulus c c-domain ,
  AtCenter.expansion c c-domain
