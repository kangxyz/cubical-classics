{-

The local log(1+x) power series agrees with the global positive logarithm

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.LogOnePlusGlobal where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.Derivative.BoundedSegment
  using (bounded-byᶜ-scale-unitInterval ; bounded-byᶜ-zero ; segmentPoint)
open import Constructive.Analysis.Reals.Calculus.Derivative.Domain
open import Constructive.Analysis.Reals.Calculus.Derivative.Domain.BoundedSegment
  using (zeroDerivativeWithinDomainSegment)
open import Constructive.Analysis.Reals.Calculus.Derivative.Domain.Rules
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedDivision
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.CommRing
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Inverse
  using (right-inverse-uniqueᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
  using (scalarMulᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Derivative
  using
    ( atanhDerivativePowerSeriesReciprocalOnBall
    ; atanhWithinDerivativeModulus
    ; atanhᶜFromSubunitBoundHasDerivativeWithinDomainAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm
  using
    ( logOnePlusPowerSeriesOnSubunitBallWith
    ; logOnePlusᶜWithinSubunitBall
    ; logOnePlusᶜWithinSubunitBall-zero
    )
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation
  using
    ( logTransformᶜ-onePlus-path
    ; logOnePlusᶜWithinSubunitBall-global
    ; onePlusStrictSubunitDomain
    )
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.AtanhTransport
  using (atanhᶜFromSubunitBound-argument-path)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.AtanhZero
  using (atanhᶜFromSubunitBound-zero)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.GeometricBridge
  using (logOnePlusDerivativePowerSeriesReciprocalOnBall)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.LogOnePlusDerivative
  using
    ( logOnePlusWithinDerivativeModulus
    ; logOnePlusᶜWithinSubunitBallHasDerivativeWithinDomainAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.QuotientDerivative
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.Global
  using
    ( LogDomainᶜ
    ; atanhᶜFromSubunitBound
    ; atanhᶜFromSubunitBound-data-independent
    ; denominatorBound
    ; denominatorLower
    ; log-domain-from-positive-boundedᶜ
    ; logᶜ-positive-bounded
    ; transformBound
    ; transformRadius
    ; transformRadius<1
    ; twoᶜ
    ; twoᶜ-bound
    ; two⁺
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius
  using
    ( InPowerSeriesBall
    ; centeredPowerSeriesSumOnBall-inBall-independent
    ; inPowerSeriesBallAtZeroFromBound
    ; inPowerSeriesBallAtZero→bound
    )
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


private
  module SolverHelpers {ℓ : Level} (𝒩 : CommRing ℓ) where
    open CommRingStr (𝒩 .snd)

    factor-from-denominator :
      (x r : 𝒩 .fst) →
      let
        two = 1r + 1r
        denominator = (1r + x) + 1r
      in
      ((denominator · r) · (denominator · r)) +
        (- ((x · r) · (x · r))) ≡
      (((two · (two · (1r + x))) · r) · r)
    factor-from-denominator _ _ =
      solve! 𝒩

    normalized-product :
      (x r p : 𝒩 .fst) →
      (1r + x) ·
        ((1r + 1r) · (p · (((1r + 1r) · r) · r))) ≡
      ((((1r + 1r) · ((1r + 1r) · (1r + x))) · r) · r) · p
    normalized-product _ _ _ =
      solve! 𝒩

    derivative-cancel :
      (d : 𝒩 .fst) →
      d + (- d) ≡ 0r
    derivative-cancel _ =
      solve! 𝒩

    zero-difference :
      (left right : 𝒩 .fst) →
      left ≡ (left + (- right)) + right
    zero-difference _ _ =
      solve! 𝒩

    zero-sum :
      0r + (- 0r) ≡ 0r
    zero-sum =
      solve! 𝒩


  LocalLog :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (x : ℝᶜ) →
    BoundedByᶜ ρ x →
    ℝᶜ
  LocalLog ρ rho<1 x x-bound =
    logOnePlusᶜWithinSubunitBall
      ρ rho<1 x (inPowerSeriesBallAtZeroFromBound x-bound)

  Quotient :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (x : ℝᶜ) →
    BoundedByᶜ ρ x →
    ℝᶜ
  Quotient =
    logTransformQuotient

  GlobalTransform :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (x : ℝᶜ) →
    BoundedByᶜ ρ x →
    ℝᶜ
  GlobalTransform ρ rho<1 x x-bound =
    twoᶜ ·ᶜ
    atanhᶜFromSubunitBound
      quotientRadius
      quotientRadius<1
      quotient
      quotient-bound
    where
    quotientRadius =
      logTransformQuotientRadius ρ rho<1

    quotientRadius<1 =
      logTransformQuotientRadius<1 ρ rho<1

    quotient =
      Quotient ρ rho<1 x x-bound

    quotient-bound =
      logTransformQuotientBound ρ rho<1 x x-bound

  Difference :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (x : ℝᶜ) →
    BoundedByᶜ ρ x →
    ℝᶜ
  Difference ρ rho<1 x x-bound =
    LocalLog ρ rho<1 x x-bound +ᶜ
    (-ᶜ GlobalTransform ρ rho<1 x x-bound)

  qSquaredRadius :
    (ρ : ℚ⁺) →
    radius ρ ℚOrder.< Rational.1ℚ →
    ℚ⁺
  qSquaredRadius ρ rho<1 =
    quotientRadius *⁺ quotientRadius
    where
    quotientRadius =
      logTransformQuotientRadius ρ rho<1

  qSquaredRadius<1 :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    radius (qSquaredRadius ρ rho<1) ℚOrder.< Rational.1ℚ
  qSquaredRadius<1 ρ rho<1 =
    ℚOrder.isTrans<
      (radius qRadius ℚ.· radius qRadius)
      (radius qRadius)
      Rational.1ℚ
      square<radius
      qRadius<1
    where
    qRadius : ℚ⁺
    qRadius =
      logTransformQuotientRadius ρ rho<1

    qRadius<1 : radius qRadius ℚOrder.< Rational.1ℚ
    qRadius<1 =
      logTransformQuotientRadius<1 ρ rho<1

    square<radius :
      radius qRadius ℚ.· radius qRadius ℚOrder.< radius qRadius
    square<radius =
      subst
        (λ t →
          radius qRadius ℚ.· radius qRadius ℚOrder.< t)
        (ℚ.·IdL (radius qRadius))
        (ℚOrder.<-·o
          (radius qRadius)
          Rational.1ℚ
          (radius qRadius)
          (qRadius .snd)
          qRadius<1)

  qFactorLower :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    ℚ⁺
  qFactorLower ρ rho<1 =
    1⁺ ⊖ qSquaredRadius ρ rho<1 [ qSquaredRadius<1 ρ rho<1 ]

  qFactorDomain :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (x : ℝᶜ) →
    (x-bound : BoundedByᶜ ρ x) →
    PositiveBoundedDomainᶜ
      (1ᶜ +ᶜ
        (-ᶜ
          (Quotient ρ rho<1 x x-bound ·ᶜ
           Quotient ρ rho<1 x x-bound)))
  qFactorDomain ρ rho<1 x x-bound =
    onePlusStrictSubunitDomain
      (qSquaredRadius ρ rho<1)
      (qSquaredRadius<1 ρ rho<1)
      (-ᶜ (quotient ·ᶜ quotient))
      (bounded-byᶜ-neg
        (qSquaredRadius ρ rho<1)
        (quotient ·ᶜ quotient)
        (bounded-byᶜ-mul
          quotientRadius
          quotientRadius
          quotient
          quotient
          quotient-bound
          quotient-bound))
    where
    quotientRadius =
      logTransformQuotientRadius ρ rho<1

    quotient =
      Quotient ρ rho<1 x x-bound

    quotient-bound =
      logTransformQuotientBound ρ rho<1 x x-bound

  LocalDerivativeValue :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (x : ℝᶜ) →
    (x-bound : BoundedByᶜ ρ x) →
    ℝᶜ
  LocalDerivativeValue ρ rho<1 x x-bound =
    reciprocalPositiveᶜ
      (lower domain)
      (1ᶜ +ᶜ x)
      (lowerBound domain)
    where
    domain =
      onePlusStrictSubunitDomain ρ rho<1 x x-bound

  AtanhDerivativeValue :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (x : ℝᶜ) →
    (x-bound : BoundedByᶜ ρ x) →
    ℝᶜ
  AtanhDerivativeValue ρ rho<1 x x-bound =
    reciprocalPositiveᶜ
      (lower domain)
      (1ᶜ +ᶜ (-ᶜ (quotient ·ᶜ quotient)))
      (lowerBound domain)
    where
    quotient =
      Quotient ρ rho<1 x x-bound

    domain =
      qFactorDomain ρ rho<1 x x-bound

  NormalizedQuotientDerivativeValue :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (x : ℝᶜ) →
    (x-bound : BoundedByᶜ ρ x) →
    ℝᶜ
  NormalizedQuotientDerivativeValue ρ rho<1 x x-bound =
    (twoᶜ ·ᶜ reciprocal) ·ᶜ reciprocal
    where
    denominator =
      (1ᶜ +ᶜ x) +ᶜ 1ᶜ

    reciprocal =
      reciprocalPositiveᶜ
        (logTransformQuotientDenominatorLower ρ rho<1)
        denominator
        (logTransformQuotientDenominatorAway ρ rho<1 x x-bound)

  NormalizedGlobalDerivativeValue :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (x : ℝᶜ) →
    (x-bound : BoundedByᶜ ρ x) →
    ℝᶜ
  NormalizedGlobalDerivativeValue ρ rho<1 x x-bound =
    (1ᶜ +ᶜ 1ᶜ) ·ᶜ
      (AtanhDerivativeValue ρ rho<1 x x-bound ·ᶜ
        logTransformQuotientDerivativeValue ρ rho<1 x x-bound)

  localLogDerivative :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (x : ℝᶜ) →
    (x-bound : BoundedByᶜ ρ x) →
    HasDerivativeWithinDomainAtWith
      (LocalLog ρ rho<1)
      x
      x-bound
      (LocalDerivativeValue ρ rho<1 x x-bound)
      (logOnePlusWithinDerivativeModulus ρ rho<1)
  localLogDerivative ρ rho<1 x x-bound =
    subst
      (λ d →
        HasDerivativeWithinDomainAtWith
          (LocalLog ρ rho<1)
          x
          x-bound
          d
          (logOnePlusWithinDerivativeModulus ρ rho<1))
      derivative-value-path
      (logOnePlusᶜWithinSubunitBallHasDerivativeWithinDomainAtWith
        ρ rho<1 x x-bound)
    where
    domain =
      onePlusStrictSubunitDomain ρ rho<1 x x-bound

    derivative-value-path =
      logOnePlusDerivativePowerSeriesReciprocalOnBall
        ρ
        rho<1
        x
        x-bound
        (lower domain)
        (upper domain)
        (lowerBound domain)
        (upperBound domain)

  atanhDerivative :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (x : ℝᶜ) →
    (x-bound : BoundedByᶜ ρ x) →
    let
      qRadius = logTransformQuotientRadius ρ rho<1
      qRadius<1 = logTransformQuotientRadius<1 ρ rho<1
      quotient = Quotient ρ rho<1 x x-bound
      quotient-bound = logTransformQuotientBound ρ rho<1 x x-bound
    in
    HasDerivativeWithinDomainAtWith
      (atanhᶜFromSubunitBound qRadius qRadius<1)
      quotient
      quotient-bound
      (AtanhDerivativeValue ρ rho<1 x x-bound)
      (atanhWithinDerivativeModulus qRadius qRadius<1)
  atanhDerivative ρ rho<1 x x-bound =
    subst
      (λ d →
        HasDerivativeWithinDomainAtWith
          (atanhᶜFromSubunitBound qRadius qRadius<1)
          quotient
          quotient-bound
          d
          (atanhWithinDerivativeModulus qRadius qRadius<1))
      derivative-value-path
      (atanhᶜFromSubunitBoundHasDerivativeWithinDomainAtWith
        qRadius qRadius<1 quotient quotient-bound)
    where
    qRadius =
      logTransformQuotientRadius ρ rho<1

    qRadius<1 =
      logTransformQuotientRadius<1 ρ rho<1

    quotient =
      Quotient ρ rho<1 x x-bound

    quotient-bound =
      logTransformQuotientBound ρ rho<1 x x-bound

    domain =
      qFactorDomain ρ rho<1 x x-bound

    derivative-value-path =
      atanhDerivativePowerSeriesReciprocalOnBall
        qRadius
        qRadius<1
        quotient
        quotient-bound
        (lower domain)
        (upper domain)
        (lowerBound domain)
        (upperBound domain)

  quotientDerivativeNormalized :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (x : ℝᶜ) →
    (x-bound : BoundedByᶜ ρ x) →
    HasDerivativeWithinDomainAtWith
      (Quotient ρ rho<1)
      x
      x-bound
      (NormalizedQuotientDerivativeValue ρ rho<1 x x-bound)
      (logTransformQuotientDerivativeModulus ρ rho<1)
  quotientDerivativeNormalized ρ rho<1 x x-bound =
    subst
      (λ d →
        HasDerivativeWithinDomainAtWith
          (Quotient ρ rho<1)
          x
          x-bound
          d
          (logTransformQuotientDerivativeModulus ρ rho<1))
      derivative-value-path
      (logTransformQuotientHasDerivativeWithinDomainAtWith
        ρ rho<1 x x-bound)
    where
    denominator =
      (1ᶜ +ᶜ x) +ᶜ 1ᶜ

    reciprocal =
      reciprocalPositiveᶜ
        (logTransformQuotientDenominatorLower ρ rho<1)
        denominator
        (logTransformQuotientDenominatorAway ρ rho<1 x x-bound)

    derivative-value-path =
      cong
        (λ t → (t ·ᶜ reciprocal) ·ᶜ reciprocal)
        (add-rational Rational.1ℚ Rational.1ℚ)

  globalTransformDerivativeModulus :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    PrecisionModulus
  globalTransformDerivativeModulus ρ rho<1 ε =
    chainModulus (posInv⁺ two⁺ *⁺ ε)
    where
    qRadius =
      logTransformQuotientRadius ρ rho<1

    qRadius<1 =
      logTransformQuotientRadius<1 ρ rho<1

    chainModulus =
      domainChainDerivativeModulus
        (logTransformQuotientDerivativeBoundRadius ρ rho<1)
        (posInv⁺ (qFactorLower ρ rho<1))
        (logTransformQuotientDerivativeModulus ρ rho<1)
        (atanhWithinDerivativeModulus qRadius qRadius<1)

  quotientDerivativeNormalizedBound :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (x : ℝᶜ) →
    (x-bound : BoundedByᶜ ρ x) →
    let
      denominator = (1ᶜ +ᶜ x) +ᶜ 1ᶜ
      reciprocal =
        reciprocalPositiveᶜ
          (logTransformQuotientDenominatorLower ρ rho<1)
          denominator
          (logTransformQuotientDenominatorAway ρ rho<1 x x-bound)
    in
    BoundedByᶜ
      (logTransformQuotientDerivativeBoundRadius ρ rho<1)
      ((twoᶜ ·ᶜ reciprocal) ·ᶜ reciprocal)
  quotientDerivativeNormalizedBound ρ rho<1 x x-bound =
    subst
      (BoundedByᶜ
        (logTransformQuotientDerivativeBoundRadius ρ rho<1))
      derivative-value-path
      (logTransformQuotientDerivativeBound ρ rho<1 x x-bound)
    where
    denominator =
      (1ᶜ +ᶜ x) +ᶜ 1ᶜ

    reciprocal =
      reciprocalPositiveᶜ
        (logTransformQuotientDenominatorLower ρ rho<1)
        denominator
        (logTransformQuotientDenominatorAway ρ rho<1 x x-bound)

    derivative-value-path =
      cong
        (λ t → (t ·ᶜ reciprocal) ·ᶜ reciprocal)
        (add-rational Rational.1ℚ Rational.1ℚ)

  globalTransformDerivativeRaw :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (x : ℝᶜ) →
    (x-bound : BoundedByᶜ ρ x) →
    let
      quotient = Quotient ρ rho<1 x x-bound
      quotient-bound = logTransformQuotientBound ρ rho<1 x x-bound
      qDerivative =
        NormalizedQuotientDerivativeValue ρ rho<1 x x-bound
    in
    HasDerivativeWithinDomainAtWith
      (GlobalTransform ρ rho<1)
      x
      x-bound
      (twoᶜ ·ᶜ
        (AtanhDerivativeValue ρ rho<1 x x-bound ·ᶜ qDerivative))
      (globalTransformDerivativeModulus ρ rho<1)
  globalTransformDerivativeRaw ρ rho<1 x x-bound =
    derivativeWithinDomainMulConstantLeftAtWith
      two⁺
      twoᶜ
      twoᶜ-bound
      (derivativeWithinDomainChainAtWith
        atanh-independent
        quotient-domain
        qDerivativeBoundRadius
        (posInv⁺ factorLower)
        (quotientDerivativeNormalizedBound ρ rho<1 x x-bound)
        (reciprocalPositiveᶜ-posInv-bound
          factorLower
          factor
          factor-away)
        (quotientDerivativeNormalized ρ rho<1 x x-bound)
        (atanhDerivative ρ rho<1 x x-bound))
    where
    qRadius =
      logTransformQuotientRadius ρ rho<1

    qRadius<1 =
      logTransformQuotientRadius<1 ρ rho<1

    quotient =
      Quotient ρ rho<1 x x-bound

    quotient-bound =
      logTransformQuotientBound ρ rho<1 x x-bound

    qDerivativeBoundRadius =
      logTransformQuotientDerivativeBoundRadius ρ rho<1

    factorDomain =
      qFactorDomain ρ rho<1 x x-bound

    factorLower =
      lower factorDomain

    factor =
      1ᶜ +ᶜ (-ᶜ (quotient ·ᶜ quotient))

    factor-away =
      lowerBound factorDomain

    atanh-independent :
      DomainValueIndependent
        (atanhᶜFromSubunitBound qRadius qRadius<1)
    atanh-independent z left right =
      atanhᶜFromSubunitBound-data-independent
        qRadius qRadius qRadius<1 qRadius<1 z left right

    quotient-domain :
      (y : ℝᶜ) →
      (y-bound : BoundedByᶜ ρ y) →
      BoundedByᶜ qRadius (Quotient ρ rho<1 y y-bound)
    quotient-domain =
      logTransformQuotientBound ρ rho<1

  rawGlobalDerivativeValuePath :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (x : ℝᶜ) →
    (x-bound : BoundedByᶜ ρ x) →
    let
      p = AtanhDerivativeValue ρ rho<1 x x-bound
      normalized = NormalizedQuotientDerivativeValue ρ rho<1 x x-bound
    in
    twoᶜ ·ᶜ (p ·ᶜ normalized) ≡
    NormalizedGlobalDerivativeValue ρ rho<1 x x-bound
  rawGlobalDerivativeValuePath ρ rho<1 x x-bound =
    cong₂
      (λ outer inner → outer ·ᶜ (p ·ᶜ inner))
      (sym (add-rational Rational.1ℚ Rational.1ℚ))
      normalized-q-path
    where
    p =
      AtanhDerivativeValue ρ rho<1 x x-bound

    denominator =
      (1ᶜ +ᶜ x) +ᶜ 1ᶜ

    reciprocal =
      reciprocalPositiveᶜ
        (logTransformQuotientDenominatorLower ρ rho<1)
        denominator
        (logTransformQuotientDenominatorAway ρ rho<1 x x-bound)

    normalized-q-path :
      NormalizedQuotientDerivativeValue ρ rho<1 x x-bound ≡
      logTransformQuotientDerivativeValue ρ rho<1 x x-bound
    normalized-q-path =
      cong
        (λ t → (t ·ᶜ reciprocal) ·ᶜ reciprocal)
        (sym (add-rational Rational.1ℚ Rational.1ℚ))

  normalizedGlobalDerivativeRightInverse :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (x : ℝᶜ) →
    (x-bound : BoundedByᶜ ρ x) →
    (1ᶜ +ᶜ x) ·ᶜ
      NormalizedGlobalDerivativeValue ρ rho<1 x x-bound
    ≡ 1ᶜ
  normalizedGlobalDerivativeRightInverse ρ rho<1 x x-bound =
    SolverHelpers.normalized-product CauchyRealsCommRing x r p ∙
    cong (_·ᶜ p) (sym factor-path) ∙
    reciprocalPositiveᶜ-right factorLower factor factor-away
    where
    quotient =
      Quotient ρ rho<1 x x-bound

    qDenominatorLower =
      logTransformQuotientDenominatorLower ρ rho<1

    denominator =
      (1ᶜ +ᶜ x) +ᶜ 1ᶜ

    denominator-away =
      logTransformQuotientDenominatorAway ρ rho<1 x x-bound

    r =
      reciprocalPositiveᶜ qDenominatorLower denominator denominator-away

    denominator-square-path :
      (denominator ·ᶜ r) ·ᶜ (denominator ·ᶜ r) ≡ 1ᶜ
    denominator-square-path =
      cong₂
        _·ᶜ_
        (reciprocalPositiveᶜ-right
          qDenominatorLower denominator denominator-away)
        (reciprocalPositiveᶜ-right
          qDenominatorLower denominator denominator-away) ∙
      mulᶜ-one-left 1ᶜ

    factorDomain =
      qFactorDomain ρ rho<1 x x-bound

    factorLower =
      lower factorDomain

    factor =
      1ᶜ +ᶜ (-ᶜ (quotient ·ᶜ quotient))

    factor-away =
      lowerBound factorDomain

    factor-path :
      factor ≡
      ((((1ᶜ +ᶜ 1ᶜ) ·ᶜ
        ((1ᶜ +ᶜ 1ᶜ) ·ᶜ (1ᶜ +ᶜ x))) ·ᶜ r) ·ᶜ r)
    factor-path =
      cong
        (λ one → one +ᶜ (-ᶜ ((x ·ᶜ r) ·ᶜ (x ·ᶜ r))))
        (sym denominator-square-path) ∙
      SolverHelpers.factor-from-denominator CauchyRealsCommRing x r

    p =
      reciprocalPositiveᶜ factorLower factor factor-away

  normalizedGlobalDerivativeValuePath :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (x : ℝᶜ) →
    (x-bound : BoundedByᶜ ρ x) →
    NormalizedGlobalDerivativeValue ρ rho<1 x x-bound ≡
    LocalDerivativeValue ρ rho<1 x x-bound
  normalizedGlobalDerivativeValuePath ρ rho<1 x x-bound =
    right-inverse-uniqueᶜ
      (normalizedGlobalDerivativeRightInverse ρ rho<1 x x-bound)
      (reciprocalPositiveᶜ-right
        (lower localDomain)
        (1ᶜ +ᶜ x)
        (lowerBound localDomain))
    where
    localDomain =
      onePlusStrictSubunitDomain ρ rho<1 x x-bound

  globalTransformDerivative :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (x : ℝᶜ) →
    (x-bound : BoundedByᶜ ρ x) →
    HasDerivativeWithinDomainAtWith
      (GlobalTransform ρ rho<1)
      x
      x-bound
      (LocalDerivativeValue ρ rho<1 x x-bound)
      (globalTransformDerivativeModulus ρ rho<1)
  globalTransformDerivative ρ rho<1 x x-bound =
    subst
      (λ d →
        HasDerivativeWithinDomainAtWith
          (GlobalTransform ρ rho<1)
          x
          x-bound
          d
          (globalTransformDerivativeModulus ρ rho<1))
      (rawGlobalDerivativeValuePath ρ rho<1 x x-bound ∙
       normalizedGlobalDerivativeValuePath ρ rho<1 x x-bound)
      (globalTransformDerivativeRaw ρ rho<1 x x-bound)

  differenceDerivativeModulus :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    PrecisionModulus
  differenceDerivativeModulus ρ rho<1 ε =
    min⁺
      (logOnePlusWithinDerivativeModulus ρ rho<1 (half⁺ ε))
      (globalTransformDerivativeModulus ρ rho<1 (half⁺ ε))

  differenceDerivative :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (x : ℝᶜ) →
    (x-bound : BoundedByᶜ ρ x) →
    HasDerivativeWithinDomainAtWith
      (Difference ρ rho<1)
      x
      x-bound
      0ᶜ
      (differenceDerivativeModulus ρ rho<1)
  differenceDerivative ρ rho<1 x x-bound =
    subst
      (λ d →
        HasDerivativeWithinDomainAtWith
          (Difference ρ rho<1)
          x
          x-bound
          d
          (differenceDerivativeModulus ρ rho<1))
      (SolverHelpers.derivative-cancel
        CauchyRealsCommRing
        (LocalDerivativeValue ρ rho<1 x x-bound))
      (derivativeWithinDomainAddAtWith
        (localLogDerivative ρ rho<1 x x-bound)
        (derivativeWithinDomainNegAtWith
          (globalTransformDerivative ρ rho<1 x x-bound)))

  differenceIndependent :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    DomainValueIndependent (Difference ρ rho<1)
  differenceIndependent ρ rho<1 x left right =
    cong
      (Difference ρ rho<1 x)
      (isPropBoundedByᶜ ρ x left right)

  globalTransformPath :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (x : ℝᶜ) →
    (x-bound : BoundedByᶜ ρ x) →
    logᶜ-positive-bounded
      (1ᶜ +ᶜ x)
      (onePlusStrictSubunitDomain ρ rho<1 x x-bound)
    ≡
    GlobalTransform ρ rho<1 x x-bound
  globalTransformPath ρ rho<1 x x-bound =
    logOnePlusᶜWithinSubunitBall-global ρ rho<1 x x-bound ∙
    cong
      (twoᶜ ·ᶜ_)
      (atanhᶜFromSubunitBound-data-independent
        (transformRadius domain)
        quotientRadius
        (transformRadius<1 domain)
        quotientRadius<1
        quotient
        transformArgumentBound
        quotient-bound)
    where
    positiveDomain =
      onePlusStrictSubunitDomain ρ rho<1 x x-bound

    domain : LogDomainᶜ (1ᶜ +ᶜ x)
    domain =
      log-domain-from-positive-boundedᶜ (1ᶜ +ᶜ x) positiveDomain

    quotientRadius =
      logTransformQuotientRadius ρ rho<1

    quotientRadius<1 =
      logTransformQuotientRadius<1 ρ rho<1

    quotient =
      Quotient ρ rho<1 x x-bound

    quotient-bound =
      logTransformQuotientBound ρ rho<1 x x-bound

    transformArgumentBound :
      BoundedByᶜ (transformRadius domain) quotient
    transformArgumentBound =
      subst
        (BoundedByᶜ (transformRadius domain))
        (logTransformᶜ-onePlus-path
          x
          (denominatorLower domain)
          (denominatorBound domain))
        (transformBound domain)

  differenceZero :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (zero-bound : BoundedByᶜ ρ 0ᶜ) →
    Difference ρ rho<1 0ᶜ zero-bound ≡ 0ᶜ
  differenceZero ρ rho<1 zero-bound =
    cong₂
      (λ local global → local +ᶜ (-ᶜ global))
      local-zero
      global-zero ∙
    SolverHelpers.zero-sum CauchyRealsCommRing
    where
    quotientRadius =
      logTransformQuotientRadius ρ rho<1

    quotientRadius<1 =
      logTransformQuotientRadius<1 ρ rho<1

    quotient =
      Quotient ρ rho<1 0ᶜ zero-bound

    quotient-bound =
      logTransformQuotientBound ρ rho<1 0ᶜ zero-bound

    quotient-zero =
      logTransformQuotient-zero ρ rho<1 zero-bound

    atanh-zero :
      atanhᶜFromSubunitBound
        quotientRadius
        quotientRadius<1
        quotient
        quotient-bound
      ≡ 0ᶜ
    atanh-zero =
      atanhᶜFromSubunitBound-argument-path
        quotientRadius
        quotientRadius<1
        quotient-zero
        quotient-bound ∙
      atanhᶜFromSubunitBound-zero
        quotientRadius
        quotientRadius<1
        (subst (BoundedByᶜ quotientRadius) quotient-zero quotient-bound)

    local-zero :
      LocalLog ρ rho<1 0ᶜ zero-bound ≡ 0ᶜ
    local-zero =
      logOnePlusᶜWithinSubunitBall-zero
        ρ
        rho<1
        (inPowerSeriesBallAtZeroFromBound zero-bound)

    global-zero :
      GlobalTransform ρ rho<1 0ᶜ zero-bound ≡ 0ᶜ
    global-zero =
      cong (twoᶜ ·ᶜ_) atanh-zero ∙
      mulᶜ-zero-right twoᶜ

  differenceAtPointZero :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (u : ℝᶜ) →
    (u-bound : BoundedByᶜ ρ u) →
    Difference ρ rho<1 u u-bound ≡ 0ᶜ
  differenceAtPointZero ρ rho<1 u u-bound =
    sym endpoint-path ∙
    segment-path ∙
    differenceZero ρ rho<1 zero-bound
    where
    zero-bound : BoundedByᶜ ρ 0ᶜ
    zero-bound =
      bounded-byᶜ-zero ρ

    forward-bound : BoundedByᶜ ρ (0ᶜ +ᶜ u)
    forward-bound =
      subst
        (BoundedByᶜ ρ)
        (sym (add-zero-left u))
        u-bound

    segment-domain :
      (q : ℚ) →
      Rational.0ℚ ℚOrder.≤ q →
      q ℚOrder.≤ Rational.1ℚ →
      BoundedByᶜ ρ (segmentPoint 0ᶜ u q)
    segment-domain q 0≤q q≤1 =
      subst
        (BoundedByᶜ ρ)
        (sym (add-zero-left (scalarMulᶜ q u)))
        (bounded-byᶜ-scale-unitInterval q 0≤q q≤1 u-bound)

    endpoint-path :
      Difference ρ rho<1 (0ᶜ +ᶜ u) forward-bound ≡
      Difference ρ rho<1 u u-bound
    endpoint-path =
      domainValueAlongPath
        (differenceIndependent ρ rho<1)
        (add-zero-left u)
        forward-bound
        u-bound

    segment-path :
      Difference ρ rho<1 (0ᶜ +ᶜ u) forward-bound ≡
      Difference ρ rho<1 0ᶜ zero-bound
    segment-path =
      zeroDerivativeWithinDomainSegment
        (differenceIndependent ρ rho<1)
        (differenceDerivative ρ rho<1)
        0ᶜ
        u
        zero-bound
        forward-bound
        ρ
        u-bound
        segment-domain

  localEqualsGlobalTransform :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    (u : ℝᶜ) →
    (u-bound : BoundedByᶜ ρ u) →
    LocalLog ρ rho<1 u u-bound ≡
    GlobalTransform ρ rho<1 u u-bound
  localEqualsGlobalTransform ρ rho<1 u u-bound =
    SolverHelpers.zero-difference
      CauchyRealsCommRing
      local
      global ∙
    cong (_+ᶜ global)
      (differenceAtPointZero ρ rho<1 u u-bound) ∙
    add-zero-left global
    where
    local =
      LocalLog ρ rho<1 u u-bound

    global =
      GlobalTransform ρ rho<1 u u-bound


logOnePlusᶜWithinSubunitBall-global-eq :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (u : ℝᶜ) →
  (u-inBall : InPowerSeriesBall 0ᶜ ρ u) →
  logOnePlusᶜWithinSubunitBall ρ ρ<1 u u-inBall ≡
  logᶜ-positive-bounded
    (1ᶜ +ᶜ u)
    (onePlusStrictSubunitDomain ρ ρ<1 u
      (inPowerSeriesBallAtZero→bound u-inBall))
logOnePlusᶜWithinSubunitBall-global-eq ρ ρ<1 u u-inBall =
  centeredPowerSeriesSumOnBall-inBall-independent
    (logOnePlusPowerSeriesOnSubunitBallWith ρ ρ<1)
    u
    u-inBall
    (inPowerSeriesBallAtZeroFromBound u-bound) ∙
  localEqualsGlobalTransform ρ ρ<1 u u-bound ∙
  sym (globalTransformPath ρ ρ<1 u u-bound)
  where
  u-bound : BoundedByᶜ ρ u
  u-bound =
    inPowerSeriesBallAtZero→bound u-inBall
