{-

Finite-radius termwise derivatives for domain-indexed power-series sums

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Within where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Nat using (ℕ ; suc)
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.Derivative.Domain
open import Constructive.Analysis.Reals.Calculus.Derivative.BoundedSegment.Margin
  using (boundedSecondDerivativeMarginModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.CommRing
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using (derivativePowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals

open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Index
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Internal
  using (four-quarters≡ ; n≤sucn ; quarter-product≡)
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.PartialSums
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.UniformPartialSums
  using
    ( PowerSeriesSecondDerivativePartialSumsBoundOnBallWith
    ; partialSumsDerivativeTargetModulus
    ; powerSeriesFormalPartialDerivativeRemainderBoundFromUniformPartialSumsDerivative
    )
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Within.PartialSums


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    linear-remainder-decomposition :
      (Fh Fx Ph Px d p' h : 𝓡 .fst) →
      (Fh + (- Fx)) + (- (d · h)) ≡
      ((((Fh + (- Ph)) + ((Ph + (- Px)) + (- (p' · h)))) +
        (Px + (- Fx))) +
        (- ((d + (- p')) · h)))
    linear-remainder-decomposition _ _ _ _ _ _ _ =
      solve! 𝓡

  withinDomainTermwiseRemainderDecomposition :
    {ℓ : Level} →
    {D : ℝᶜ → Type ℓ} →
    (f : (y : ℝᶜ) → D y → ℝᶜ) →
    (a da : PowerSeries) →
    (x : ℝᶜ) →
    (x-domain : D x) →
    (d : ℝᶜ) →
    (χ : TermwiseDerivativeIndex) →
    (ε η : ℚ⁺) →
    (h : ℝᶜ) →
    (forward-domain : D (x +ᶜ h)) →
    withinDomainLinearRemainder f x x-domain d h forward-domain ≡
    ((((f (x +ᶜ h) forward-domain +ᶜ
        (-ᶜ powerSeriesPartialSum a (x +ᶜ h) (suc (χ ε η)))) +ᶜ
        powerSeriesTermwisePartialRemainder a da x χ ε η h) +ᶜ
        (powerSeriesPartialSum a x (suc (χ ε η)) +ᶜ
          (-ᶜ f x x-domain))) +ᶜ
        powerSeriesTermwiseDerivativeLinearError da x d χ ε η h)
  withinDomainTermwiseRemainderDecomposition
    f a da x x-domain d χ ε η h forward-domain =
    SolverHelpers.linear-remainder-decomposition
      CauchyRealsCommRing
      (f (x +ᶜ h) forward-domain)
      (f x x-domain)
      (powerSeriesPartialSum a (x +ᶜ h) (suc n))
      (powerSeriesPartialSum a x (suc n))
      d
      (powerSeriesPartialSum da x n)
      h
    where
    n : ℕ
    n =
      χ ε η


powerSeriesSumWithinDomainFormalDerivativeAtWithFromSecondDerivativeBound :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (y : ℝᶜ) → D y → ℝᶜ} →
  {a : PowerSeries} →
  {x : ℝᶜ} →
  {x-domain : D x} →
  {ρ σ ζ Γ : ℚ⁺} →
  {ν τ : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a ρ ν) →
  (derivativeConvergence :
    HasPowerSeriesOnBallWith (derivativePowerSeries a) ρ τ) →
  (domainBound : (y : ℝᶜ) → D y → BoundedByᶜ ρ y) →
  ((y : ℝᶜ) →
    (y-domain : D y) →
    f y y-domain ≡
    powerSeriesSumOnBall
      a
      ρ
      ν
      convergence
      y
      (domainBound y y-domain)) →
  BoundedByᶜ σ x →
  PowerSeriesSecondDerivativePartialSumsBoundOnBallWith a (σ +⁺ ζ) Γ →
  HasDerivativeWithinDomainAtWith
    f
    x
    x-domain
    (powerSeriesSumOnBall
      (derivativePowerSeries a)
      ρ
      τ
      derivativeConvergence
      x
      (domainBound x x-domain))
    (partialSumsDerivativeTargetModulus
      (boundedSecondDerivativeMarginModulus ζ Γ))
powerSeriesSumWithinDomainFormalDerivativeAtWithFromSecondDerivativeBound
  {D = D}
  {f = f}
  {a = a}
  {x = x}
  {x-domain = x-domain}
  {ρ = ρ}
  {σ = σ}
  {ζ = ζ}
  {Γ = Γ}
  {ν = ν}
  {τ = τ}
  convergence
  derivativeConvergence
  domainBound
  expansion
  x-small-bound
  secondBound
  ε
  η
  η≤target
  h
  h-bound
  forward-domain =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (sym
      (withinDomainTermwiseRemainderDecomposition
        f
        a
        (derivativePowerSeries a)
        x
        x-domain
        derivativeValue
        χ
        ε
        η
        h
        forward-domain))
    (subst
      (λ κ → BoundedByᶜ κ decomposedRemainder)
      (four-quarters≡ (ε *⁺ η))
      combinedBound)
  where
  targetModulus : PrecisionModulus
  targetModulus =
    partialSumsDerivativeTargetModulus
      (boundedSecondDerivativeMarginModulus ζ Γ)

  χ : TermwiseDerivativeIndex
  χ =
    termwiseConvergenceIndex ν τ

  x-bound : BoundedByᶜ ρ x
  x-bound =
    domainBound x x-domain

  derivativeValue : ℝᶜ
  derivativeValue =
    powerSeriesSumOnBall
      (derivativePowerSeries a)
      ρ
      τ
      derivativeConvergence
      x
      (domainBound x x-domain)

  partialDerivative =
    powerSeriesFormalPartialSumsHaveDerivativeWithFromSecondDerivativeBoundOnMargin
      σ
      ζ
      Γ
      x-small-bound
      secondBound

  partialBound =
    powerSeriesFormalPartialDerivativeRemainderBoundFromUniformPartialSumsDerivative
      {a = a}
      {x = x}
      {χ = χ}
      {μ = boundedSecondDerivativeMarginModulus ζ Γ}
      partialDerivative

  n : ℕ
  n =
    χ ε η

  piecePrecision : ℚ⁺
  piecePrecision =
    quarter⁺ (ε *⁺ η)

  forward-point-bound : BoundedByᶜ ρ (x +ᶜ h)
  forward-point-bound =
    domainBound (x +ᶜ h) forward-domain

  forwardError : ℝᶜ
  forwardError =
    f (x +ᶜ h) forward-domain +ᶜ
    (-ᶜ powerSeriesPartialSum a (x +ᶜ h) (suc n))

  forwardBound : BoundedByᶜ piecePrecision forwardError
  forwardBound =
    subst
      (λ z →
        BoundedByᶜ
          piecePrecision
          (z +ᶜ (-ᶜ powerSeriesPartialSum a (x +ᶜ h) (suc n))))
      (sym (expansion (x +ᶜ h) forward-domain))
      (powerSeriesApproximationForwardErrorBoundFromConvergence
        convergence
        piecePrecision
        (x +ᶜ h)
        forward-point-bound
        (suc n)
        (NatOrder.≤-trans
          (termwiseConvergenceIndex-sumLarge {ν = ν} {τ = τ} ε η)
          (n≤sucn n)))

  partialError : ℝᶜ
  partialError =
    powerSeriesTermwisePartialRemainder
      a
      (derivativePowerSeries a)
      x
      χ
      ε
      η
      h

  partialErrorBound : BoundedByᶜ piecePrecision partialError
  partialErrorBound =
    partialBound ε η η≤target h h-bound

  centerError : ℝᶜ
  centerError =
    powerSeriesPartialSum a x (suc n) +ᶜ (-ᶜ f x x-domain)

  centerBound : BoundedByᶜ piecePrecision centerError
  centerBound =
    subst
      (λ z →
        BoundedByᶜ
          piecePrecision
          (powerSeriesPartialSum a x (suc n) +ᶜ (-ᶜ z)))
      (sym (expansion x x-domain))
      (powerSeriesApproximationReverseErrorBoundFromConvergence
        convergence
        piecePrecision
        x
        x-bound
        (suc n)
        (NatOrder.≤-trans
          (termwiseConvergenceIndex-sumLarge {ν = ν} {τ = τ} ε η)
          (n≤sucn n)))

  derivativeError : ℝᶜ
  derivativeError =
    derivativeValue +ᶜ
    (-ᶜ powerSeriesPartialSum (derivativePowerSeries a) x n)

  derivativeErrorBound : BoundedByᶜ (quarter⁺ ε) derivativeError
  derivativeErrorBound =
    powerSeriesApproximationForwardErrorBoundFromConvergence
      derivativeConvergence
      (quarter⁺ ε)
      x
      x-bound
      n
      (termwiseConvergenceIndex-derivativeValueLarge
        {ν = ν}
        {τ = τ}
        ε
        η)

  derivativeLinearError : ℝᶜ
  derivativeLinearError =
    -ᶜ (derivativeError ·ᶜ h)

  derivativeLinearBound :
    BoundedByᶜ piecePrecision derivativeLinearError
  derivativeLinearBound =
    subst
      (λ κ → BoundedByᶜ κ derivativeLinearError)
      (quarter-product≡ ε η)
      (bounded-byᶜ-neg
        (quarter⁺ ε *⁺ η)
        (derivativeError ·ᶜ h)
        (bounded-byᶜ-mul
          (quarter⁺ ε)
          η
          derivativeError
          h
          derivativeErrorBound
          h-bound))

  firstTwoBound =
    bounded-byᶜ-add
      piecePrecision
      piecePrecision
      forwardError
      partialError
      forwardBound
      partialErrorBound

  firstThreeBound =
    bounded-byᶜ-add
      (piecePrecision +⁺ piecePrecision)
      piecePrecision
      (forwardError +ᶜ partialError)
      centerError
      firstTwoBound
      centerBound

  decomposedRemainder : ℝᶜ
  decomposedRemainder =
    ((forwardError +ᶜ partialError) +ᶜ centerError) +ᶜ
    derivativeLinearError

  combinedBound =
    bounded-byᶜ-add
      ((piecePrecision +⁺ piecePrecision) +⁺ piecePrecision)
      piecePrecision
      ((forwardError +ᶜ partialError) +ᶜ centerError)
      derivativeLinearError
      firstThreeBound
      derivativeLinearBound
