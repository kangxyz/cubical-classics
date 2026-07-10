{-

Local additive identity for the global positive logarithm

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.LocalAdd where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.Derivative.BoundedSegment.Base
  using (bounded-byᶜ-scale-unitInterval ; bounded-byᶜ-zero ; segmentPoint)
open import Constructive.Analysis.Reals.Calculus.Derivative.Domain.Base
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
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
  using (≤ᶜ-add ; negᶜ-pres≤ᶜ)
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using (powerSeriesSumOnBall-zero)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.Base
  using
    ( logOnePlusPowerSeries
    ; logOnePlusPowerSeriesCoefficient-zero
    ; logOnePlusPowerSeriesOnSubunitBallWith
    ; logOnePlusᶜWithinSubunitBall
    )
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.DomainScaling
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.Core
  using
    ( onePlusStrictSubunitDomain
    ; positiveDivision-denominatorMulOnePlus-path
    )
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.GeometricBridge
  using (logOnePlusDerivativePowerSeriesReciprocalOnBall)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.GlobalDerivative
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.LogOnePlusDerivative
  using
    ( logOnePlusWithinDerivativeModulus
    ; logOnePlusᶜWithinSubunitBallHasDerivativeWithinDomainAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.Global
  using (logᶜ-positive-bounded)
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.GeometricDecay
  using (positiveGeometricPowerModulus)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


private
  module SolverHelpers {ℓ : Level} (𝒩 : CommRing ℓ) where
    open CommRingStr (𝒩 .snd)

    affine-remainder :
      (c t h : 𝒩 .fst) →
      (((c + (t + h)) + (- (c + t))) + (- (1r · h))) ≡ 0r
    affine-remainder _ _ _ =
      solve! 𝒩

    linear-remainder :
      (t h r : 𝒩 .fst) →
      ((((t + h) · r) + (- (t · r))) + (- (r · h))) ≡ 0r
    linear-remainder _ _ _ =
      solve! 𝒩

    scaled-reciprocal-product :
      (c u p r : 𝒩 .fst) →
      (c · (1r + u)) · (p · r) ≡
      ((1r + u) · p) · (c · r)
    scaled-reciprocal-product _ _ _ _ =
      solve! 𝒩

    reciprocal-products-one :
      1r · 1r ≡ 1r
    reciprocal-products-one =
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

    difference-at-zero :
      (value : 𝒩 .fst) →
      value + (- 0r) ≡ value
    difference-at-zero _ =
      solve! 𝒩

  rational-difference-path :
    (a b : ℚ⁺) →
    (b<a : radius b ℚOrder.< radius a) →
    rational (radius (a ⊖ b [ b<a ])) ≡
    rational (radius a) +ᶜ (-ᶜ rational (radius b))
  rational-difference-path a b b<a =
    add-rational (radius a) (ℚ.- radius b) ∙
    cong (rational (radius a) +ᶜ_) (sym (neg-rational (radius b)))


private
  module LocalData
    (c : ℝᶜ)
    (c-domain : PositiveBoundedDomainᶜ c)
    (ρ : ℚ⁺)
    (ρ<cLower : radius ρ ℚOrder.< radius (lower c-domain))
    where

    cLower : ℚ⁺
    cLower =
      lower c-domain

    cUpper : ℚ⁺
    cUpper =
      upper c-domain

    c-lower : BoundedAwayPositiveᶜ cLower c
    c-lower =
      lowerBound c-domain

    c-upper : BoundedByᶜ cUpper c
    c-upper =
      upperBound c-domain

    localRadius : ℚ⁺
    localRadius =
      divideByPositiveStrictSubunitRadius ρ cLower

    localRadius<1 : radius localRadius ℚOrder.< Rational.1ℚ
    localRadius<1 =
      divideByPositiveStrictSubunitRadius<1 ρ cLower ρ<cLower

    shiftedLower : ℚ⁺
    shiftedLower =
      cLower ⊖ ρ [ ρ<cLower ]

    shiftedUpper : ℚ⁺
    shiftedUpper =
      cUpper +⁺ ρ

    ShiftDomain : ℝᶜ → Type₀
    ShiftDomain =
      BoundedByᶜ ρ

    shiftWindow :
      (t : ℝᶜ) →
      ShiftDomain t →
      PositiveWindowᶜ shiftedLower shiftedUpper (c +ᶜ t)
    shiftWindow t t-bound =
      shifted-lower , shifted-upper
      where
      shifted-lower : BoundedAwayPositiveᶜ shiftedLower (c +ᶜ t)
      shifted-lower =
        bounded-away-positiveᶜ
          (subst
            (λ z → z ≤ᶜ c +ᶜ t)
            (rational-difference-path cLower ρ ρ<cLower)
            (≤ᶜ-add
              {a = rational (radius cLower)}
              {b = c}
              {c = -ᶜ rational (radius ρ)}
              {d = t}
              (c-lower .BoundedAwayPositiveᶜ.lowerᶜ)
              (subst
                ((-ᶜ rational (radius ρ)) ≤ᶜ_)
                (neg-involutive t)
                (negᶜ-pres≤ᶜ (lowerᶜ t-bound)))))

      shifted-upper : BoundedByᶜ shiftedUpper (c +ᶜ t)
      shifted-upper =
        bounded-byᶜ-add cUpper ρ c t c-upper t-bound

    Affine :
      (t : ℝᶜ) →
      ShiftDomain t →
      ℝᶜ
    Affine t _ =
      c +ᶜ t

    affineIndependent :
      DomainValueIndependent Affine
    affineIndependent _ _ _ =
      refl

    affineDomain :
      (t : ℝᶜ) →
      (t-bound : ShiftDomain t) →
      PositiveWindowᶜ shiftedLower shiftedUpper (Affine t t-bound)
    affineDomain =
      shiftWindow

    exactLinearModulus : PrecisionModulus
    exactLinearModulus _ =
      1⁺

    affineDerivative :
      (t : ℝᶜ) →
      (t-bound : ShiftDomain t) →
      HasDerivativeWithinDomainAtWith
        Affine
        t
        t-bound
        1ᶜ
        exactLinearModulus
    affineDerivative t t-bound ε η η≤1 h h-bound forward-bound =
      subst
        (BoundedByᶜ (ε *⁺ η))
        (sym (SolverHelpers.affine-remainder CauchyRealsCommRing c t h))
        (bounded-byᶜ-zero (ε *⁺ η))

    ShiftedLog :
      (t : ℝᶜ) →
      ShiftDomain t →
      ℝᶜ
    ShiftedLog t t-bound =
      logᶜ-positive-window
        shiftedLower
        shiftedUpper
        (Affine t t-bound)
        (affineDomain t t-bound)

    shiftedLogDerivativeModulus : PrecisionModulus
    shiftedLogDerivativeModulus =
      domainChainDerivativeModulus
        1⁺
        (posInv⁺ shiftedLower)
        exactLinearModulus
        (logᶜ-positive-windowDerivativeModulus
          shiftedLower shiftedUpper)

    shiftedLogDerivative :
      (t : ℝᶜ) →
      (t-bound : ShiftDomain t) →
      HasDerivativeWithinDomainAtWith
        ShiftedLog
        t
        t-bound
        (reciprocalPositiveᶜ
          shiftedLower
          (c +ᶜ t)
          (shiftWindow t t-bound .fst))
        shiftedLogDerivativeModulus
    shiftedLogDerivative t t-bound =
      subst
        (λ d →
          HasDerivativeWithinDomainAtWith
            ShiftedLog
            t
            t-bound
            d
            shiftedLogDerivativeModulus)
        (mulᶜ-one-right reciprocal)
        (derivativeWithinDomainChainAtWith
          (logᶜ-positive-window-data-independent shiftedLower shiftedUpper)
          affineDomain
          1⁺
          (posInv⁺ shiftedLower)
          oneBoundedᶜ
          (reciprocalPositiveᶜ-posInv-bound
            shiftedLower
            (c +ᶜ t)
            (shiftWindow t t-bound .fst))
          (affineDerivative t t-bound)
          (logᶜ-positive-windowHasDerivativeWithinDomainAtWith
            shiftedLower
            shiftedUpper
            (c +ᶜ t)
            (shiftWindow t t-bound)))
      where
      reciprocal =
        reciprocalPositiveᶜ
          shiftedLower
          (c +ᶜ t)
          (shiftWindow t t-bound .fst)

    Quotient :
      (t : ℝᶜ) →
      ShiftDomain t →
      ℝᶜ
    Quotient t _ =
      divideByPositiveᶜ t cLower c c-lower

    quotientIndependent :
      DomainValueIndependent Quotient
    quotientIndependent _ _ _ =
      refl

    quotientDomain :
      (t : ℝᶜ) →
      (t-bound : ShiftDomain t) →
      BoundedByᶜ localRadius (Quotient t t-bound)
    quotientDomain t t-bound =
      divideByPositiveᶜ-strictSubunitBound
        ρ cLower ρ<cLower t c t-bound c-lower

    quotientDerivative :
      (t : ℝᶜ) →
      (t-bound : ShiftDomain t) →
      HasDerivativeWithinDomainAtWith
        Quotient
        t
        t-bound
        (reciprocalPositiveᶜ cLower c c-lower)
        exactLinearModulus
    quotientDerivative t t-bound ε η η≤1 h h-bound forward-bound =
      subst
        (BoundedByᶜ (ε *⁺ η))
        (sym (SolverHelpers.linear-remainder CauchyRealsCommRing t h r))
        (bounded-byᶜ-zero (ε *⁺ η))
      where
      r =
        reciprocalPositiveᶜ cLower c c-lower

    LocalBase :
      (u : ℝᶜ) →
      BoundedByᶜ localRadius u →
      ℝᶜ
    LocalBase u u-bound =
      logOnePlusᶜWithinSubunitBall
        localRadius
        localRadius<1
        u
        (inPowerSeriesBallAtZeroFromBound u-bound)

    localBaseIndependent :
      DomainValueIndependent LocalBase
    localBaseIndependent u left right =
      cong (LocalBase u) (isPropBoundedByᶜ localRadius u left right)

    localBaseDerivativeValue :
      (u : ℝᶜ) →
      (u-bound : BoundedByᶜ localRadius u) →
      ℝᶜ
    localBaseDerivativeValue u u-bound =
      reciprocalPositiveᶜ
        (lower domain)
        (1ᶜ +ᶜ u)
        (lowerBound domain)
      where
      domain =
        onePlusStrictSubunitDomain localRadius localRadius<1 u u-bound

    localBaseDerivative :
      (u : ℝᶜ) →
      (u-bound : BoundedByᶜ localRadius u) →
      HasDerivativeWithinDomainAtWith
        LocalBase
        u
        u-bound
        (localBaseDerivativeValue u u-bound)
        (logOnePlusWithinDerivativeModulus localRadius localRadius<1)
    localBaseDerivative u u-bound =
      subst
        (λ d →
          HasDerivativeWithinDomainAtWith
            LocalBase
            u
            u-bound
            d
            (logOnePlusWithinDerivativeModulus localRadius localRadius<1))
        derivative-value-path
        (logOnePlusᶜWithinSubunitBallHasDerivativeWithinDomainAtWith
          localRadius localRadius<1 u u-bound)
      where
      domain =
        onePlusStrictSubunitDomain localRadius localRadius<1 u u-bound

      derivative-value-path =
        logOnePlusDerivativePowerSeriesReciprocalOnBall
          localRadius
          localRadius<1
          u
          u-bound
          (lower domain)
          (upper domain)
          (lowerBound domain)
          (upperBound domain)

    LocalScaled :
      (t : ℝᶜ) →
      ShiftDomain t →
      ℝᶜ
    LocalScaled t t-bound =
      LocalBase (Quotient t t-bound) (quotientDomain t t-bound)

    localScaledDerivativeModulus : PrecisionModulus
    localScaledDerivativeModulus =
      domainChainDerivativeModulus
        (posInv⁺ cLower)
        (posInv⁺ factorLower)
        exactLinearModulus
        (logOnePlusWithinDerivativeModulus localRadius localRadius<1)
      where
      factorLower =
        1⁺ ⊖ localRadius [ localRadius<1 ]

    localScaledRawDerivativeValue :
      (t : ℝᶜ) →
      (t-bound : ShiftDomain t) →
      ℝᶜ
    localScaledRawDerivativeValue t t-bound =
      localBaseDerivativeValue quotient quotient-bound ·ᶜ r
      where
      quotient =
        Quotient t t-bound

      quotient-bound =
        quotientDomain t t-bound

      r =
        reciprocalPositiveᶜ cLower c c-lower

    localScaledRawDerivative :
      (t : ℝᶜ) →
      (t-bound : ShiftDomain t) →
      HasDerivativeWithinDomainAtWith
        LocalScaled
        t
        t-bound
        (localScaledRawDerivativeValue t t-bound)
        localScaledDerivativeModulus
    localScaledRawDerivative t t-bound =
      derivativeWithinDomainChainAtWith
        localBaseIndependent
        quotientDomain
        (posInv⁺ cLower)
        (posInv⁺ factorLower)
        r-bound
        p-bound
        (quotientDerivative t t-bound)
        (localBaseDerivative quotient quotient-bound)
      where
      quotient =
        Quotient t t-bound

      quotient-bound =
        quotientDomain t t-bound

      factorDomain =
        onePlusStrictSubunitDomain
          localRadius localRadius<1 quotient quotient-bound

      factorLower =
        lower factorDomain

      factor =
        1ᶜ +ᶜ quotient

      factor-away =
        lowerBound factorDomain

      p =
        reciprocalPositiveᶜ factorLower factor factor-away

      p-bound : BoundedByᶜ (posInv⁺ factorLower) p
      p-bound =
        reciprocalPositiveᶜ-posInv-bound factorLower factor factor-away

      r =
        reciprocalPositiveᶜ cLower c c-lower

      r-bound : BoundedByᶜ (posInv⁺ cLower) r
      r-bound =
        reciprocalPositiveᶜ-posInv-bound cLower c c-lower

    localScaledRawDerivativeRightInverse :
      (t : ℝᶜ) →
      (t-bound : ShiftDomain t) →
      (c +ᶜ t) ·ᶜ localScaledRawDerivativeValue t t-bound ≡ 1ᶜ
    localScaledRawDerivativeRightInverse t t-bound =
      cong (_·ᶜ (p ·ᶜ r))
        (sym (positiveDivision-denominatorMulOnePlus-path
          cLower c t c-lower)) ∙
      SolverHelpers.scaled-reciprocal-product CauchyRealsCommRing c quotient p r ∙
      cong₂
        _·ᶜ_
        (reciprocalPositiveᶜ-right factorLower factor factor-away)
        (reciprocalPositiveᶜ-right cLower c c-lower) ∙
      SolverHelpers.reciprocal-products-one CauchyRealsCommRing
      where
      quotient =
        Quotient t t-bound

      quotient-bound =
        quotientDomain t t-bound

      factorDomain =
        onePlusStrictSubunitDomain
          localRadius localRadius<1 quotient quotient-bound

      factorLower =
        lower factorDomain

      factor =
        1ᶜ +ᶜ quotient

      factor-away =
        lowerBound factorDomain

      p =
        reciprocalPositiveᶜ factorLower factor factor-away

      r =
        reciprocalPositiveᶜ cLower c c-lower

    localScaledDerivativeValuePath :
      (t : ℝᶜ) →
      (t-bound : ShiftDomain t) →
      localScaledRawDerivativeValue t t-bound ≡
      reciprocalPositiveᶜ
        shiftedLower
        (c +ᶜ t)
        (shiftWindow t t-bound .fst)
    localScaledDerivativeValuePath t t-bound =
      right-inverse-uniqueᶜ
        (localScaledRawDerivativeRightInverse t t-bound)
        (reciprocalPositiveᶜ-right
          shiftedLower
          (c +ᶜ t)
          (shiftWindow t t-bound .fst))

    localScaledDerivative :
      (t : ℝᶜ) →
      (t-bound : ShiftDomain t) →
      HasDerivativeWithinDomainAtWith
        LocalScaled
        t
        t-bound
        (reciprocalPositiveᶜ
          shiftedLower
          (c +ᶜ t)
          (shiftWindow t t-bound .fst))
        localScaledDerivativeModulus
    localScaledDerivative t t-bound =
      subst
        (λ d →
          HasDerivativeWithinDomainAtWith
            LocalScaled
            t
            t-bound
            d
            localScaledDerivativeModulus)
        (localScaledDerivativeValuePath t t-bound)
        (localScaledRawDerivative t t-bound)

    Difference :
      (t : ℝᶜ) →
      ShiftDomain t →
      ℝᶜ
    Difference t t-bound =
      ShiftedLog t t-bound +ᶜ (-ᶜ LocalScaled t t-bound)

    differenceIndependent :
      DomainValueIndependent Difference
    differenceIndependent t left right =
      cong (Difference t) (isPropBoundedByᶜ ρ t left right)

    differenceDerivativeModulus : PrecisionModulus
    differenceDerivativeModulus ε =
      min⁺
        (shiftedLogDerivativeModulus (half⁺ ε))
        (localScaledDerivativeModulus (half⁺ ε))

    differenceDerivative :
      (t : ℝᶜ) →
      (t-bound : ShiftDomain t) →
      HasDerivativeWithinDomainAtWith
        Difference
        t
        t-bound
        0ᶜ
        differenceDerivativeModulus
    differenceDerivative t t-bound =
      subst
        (λ d →
          HasDerivativeWithinDomainAtWith
            Difference
            t
            t-bound
            d
            differenceDerivativeModulus)
        (SolverHelpers.derivative-cancel CauchyRealsCommRing reciprocal)
        (derivativeWithinDomainAddAtWith
          (shiftedLogDerivative t t-bound)
          (derivativeWithinDomainNegAtWith
            (localScaledDerivative t t-bound)))
      where
      reciprocal =
        reciprocalPositiveᶜ
          shiftedLower
          (c +ᶜ t)
          (shiftWindow t t-bound .fst)

    shiftedLogZero :
      (zero-bound : ShiftDomain 0ᶜ) →
      ShiftedLog 0ᶜ zero-bound ≡
      logᶜ-positive-bounded c c-domain
    shiftedLogZero zero-bound =
      domainValueAlongPath
        logᶜ-positive-bounded-data-independent
        (add-zero-right c)
        (positiveWindowDomain
          shiftedLower shiftedUpper (c +ᶜ 0ᶜ)
          (shiftWindow 0ᶜ zero-bound))
        c-domain

    localScaledZero :
      (zero-bound : ShiftDomain 0ᶜ) →
      LocalScaled 0ᶜ zero-bound ≡ 0ᶜ
    localScaledZero zero-bound =
      centeredPowerSeriesSumOnBallAtZero-path
        convergence
        quotient
        quotient-bound ∙
      powerSeriesSumOnBall-center-path
        convergence
        quotient-zero
        quotient-bound
        (bounded-byᶜ-zero localRadius) ∙
      powerSeriesSumOnBall-zero
        convergence
        (bounded-byᶜ-zero localRadius) ∙
      logOnePlusPowerSeriesCoefficient-zero
      where
      convergence =
        logOnePlusPowerSeriesOnSubunitBallWith localRadius localRadius<1

      quotient =
        Quotient 0ᶜ zero-bound

      quotient-bound =
        quotientDomain 0ᶜ zero-bound

      quotient-zero : quotient ≡ 0ᶜ
      quotient-zero =
        mulᶜ-zero-left
          (reciprocalPositiveᶜ cLower c c-lower)

    differenceZero :
      (zero-bound : ShiftDomain 0ᶜ) →
      Difference 0ᶜ zero-bound ≡
      logᶜ-positive-bounded c c-domain
    differenceZero zero-bound =
      cong₂
        (λ global local → global +ᶜ (-ᶜ local))
        (shiftedLogZero zero-bound)
        (localScaledZero zero-bound) ∙
      SolverHelpers.difference-at-zero
        CauchyRealsCommRing
        (logᶜ-positive-bounded c c-domain)

    differenceAt :
      (h : ℝᶜ) →
      (h-bound : ShiftDomain h) →
      Difference h h-bound ≡
      logᶜ-positive-bounded c c-domain
    differenceAt h h-bound =
      sym endpoint-path ∙
      segment-path ∙
      differenceZero zero-bound
      where
      zero-bound : ShiftDomain 0ᶜ
      zero-bound =
        bounded-byᶜ-zero ρ

      forward-bound : ShiftDomain (0ᶜ +ᶜ h)
      forward-bound =
        subst (BoundedByᶜ ρ) (sym (add-zero-left h)) h-bound

      segment-domain :
        (q : ℚ) →
        Rational.0ℚ ℚOrder.≤ q →
        q ℚOrder.≤ Rational.1ℚ →
        ShiftDomain (segmentPoint 0ᶜ h q)
      segment-domain q 0≤q q≤1 =
        subst
          (BoundedByᶜ ρ)
          (sym (add-zero-left (scalarMulᶜ q h)))
          (bounded-byᶜ-scale-unitInterval q 0≤q q≤1 h-bound)

      endpoint-path :
        Difference (0ᶜ +ᶜ h) forward-bound ≡
        Difference h h-bound
      endpoint-path =
        domainValueAlongPath
          differenceIndependent
          (add-zero-left h)
          forward-bound
          h-bound

      segment-path :
        Difference (0ᶜ +ᶜ h) forward-bound ≡
        Difference 0ᶜ zero-bound
      segment-path =
        zeroDerivativeWithinDomainSegment
          differenceIndependent
          differenceDerivative
          0ᶜ
          h
          zero-bound
          forward-bound
          ρ
          h-bound
          segment-domain

    shiftedLogIdentity :
      (h : ℝᶜ) →
      (h-bound : ShiftDomain h) →
      ShiftedLog h h-bound ≡
      logᶜ-positive-bounded c c-domain +ᶜ LocalScaled h h-bound
    shiftedLogIdentity h h-bound =
      SolverHelpers.zero-difference CauchyRealsCommRing global local ∙
      cong (_+ᶜ local) (differenceAt h h-bound)
      where
      global =
        ShiftedLog h h-bound

      local =
        LocalScaled h h-bound


logᶜ-positive-bounded-add-local :
  (c h : ℝᶜ) →
  (c-domain : PositiveBoundedDomainᶜ c) →
  (ch-domain : PositiveBoundedDomainᶜ (c +ᶜ h)) →
  (ρ : ℚ⁺) →
  (h-bound : BoundedByᶜ ρ h) →
  (ρ<cLower : radius ρ ℚOrder.< radius (lower c-domain)) →
  logᶜ-positive-bounded (c +ᶜ h) ch-domain ≡
  logᶜ-positive-bounded c c-domain +ᶜ
  logOnePlusᶜWithinSubunitBall
    (divideByPositiveStrictSubunitRadius ρ (lower c-domain))
    (divideByPositiveStrictSubunitRadius<1
      ρ (lower c-domain) ρ<cLower)
    (divideByPositiveᶜ h (lower c-domain) c (lowerBound c-domain))
    (inPowerSeriesBallAtZeroFromBound
      (divideByPositiveᶜ-strictSubunitBound
        ρ
        (lower c-domain)
        ρ<cLower
        h
        c
        h-bound
        (lowerBound c-domain)))
logᶜ-positive-bounded-add-local
    c h c-domain ch-domain ρ h-bound ρ<cLower =
  logᶜ-positive-bounded-data-independent
    (c +ᶜ h)
    ch-domain
    (positiveWindowDomain
      shiftedLower
      shiftedUpper
      (c +ᶜ h)
      (LocalData.shiftWindow c c-domain ρ ρ<cLower h h-bound)) ∙
  LocalData.shiftedLogIdentity
    c c-domain ρ ρ<cLower h h-bound
  where
  shiftedLower =
    lower c-domain ⊖ ρ [ ρ<cLower ]

  shiftedUpper =
    upper c-domain +⁺ ρ
