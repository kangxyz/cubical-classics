{-

Part of Constructive.Analysis.Reals.PowerSeries.Instances.Trigonometric

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Trigonometric.Majorants where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
  using (_+ᶜ_ ; add-inverse-right ; add-zero-left)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
  using (-ᶜ_ ; neg-involutive)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (≤ᶜ-refl)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.Derivative.Base
  using (HasDerivativeAtWith)
open import Constructive.Analysis.Reals.Calculus.Derivative.Rules
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.GeometricDecay using (positivePower)
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower ; realPowerBoundsFromBound)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( centeredPowerSeriesSumEverywhere-center
    ; centeredPowerSeriesSumEverywhere-neg
    ; constantPowerSeries
    ; constantPowerSeriesInfiniteRadius
    ; negPowerSeries
    ; negPowerSeriesInfiniteRadius
    ; subPowerSeries
    ; subPowerSeriesInfiniteRadius
    )
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using
    ( derivativePowerSeries
    ; inverseSucReal
    ; naturalReal
    ; naturalTimesInverseSucReal-cancel
    ; primitivePowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative
  using
    ( PowerSeriesIteratedFormalPartialDerivativeBounds
    ; PowerSeriesPartialSumsDerivativeModulusLarge
    ; centeredPowerSeriesHasDerivativeFromIteratedBounds
    ; hasDerivativeAtWith-congDerivative
    ; positivePartialSum
    ; powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
    ; powerSeriesFormalPartialSumsDerivativeModulus
    ; termwiseConvergenceIndex
    )
open import Constructive.Analysis.Reals.PowerSeries.Instances.Exponential
  using
    ( reciprocalFactorial⁺
    ; expPositiveMajorantRadius
    ; expPositiveMajorantTerm
    ; expPositiveMajorantTerm-nonnegative
    ; expPositiveMajorantFactorialModulus
    ; expPositiveMajorantFactorialTailBound
    ; expPositiveMajorantFactorialModulusAntitone
    )
open import Constructive.Data.PositiveRationals
  using
    ( ℚ⁺
    ; 1⁺
    ; _+⁺_
    ; _*⁺_
    ; *⁺-comm
    ; *⁺-identity-left
    ; ℚ⁺Path
    ; radius
    ; scalar-bound
    )
import Constructive.Data.Rationals.Archimedean as Rational
import Constructive.Data.Rationals.Base as RationalBase
import Constructive.Data.Rationals.Factorial as Factorial

open import Constructive.Analysis.Reals.PowerSeries.Instances.Trigonometric.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Instances.Trigonometric.Bounds

sinPowerSeriesTermBoundByExpMajorant :
  (ρ : ℚ⁺) →
  (h : ℝᶜ) →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower h n) →
  BoundedByᶜ (expPositiveMajorantRadius ρ n)
    (powerSeriesTerm sinPowerSeries h n)
sinPowerSeriesTermBoundByExpMajorant ρ h n powerBound =
  subst
    (λ κ → BoundedByᶜ κ (powerSeriesTerm sinPowerSeries h n))
    (*⁺-comm (reciprocalFactorial⁺ n) (positivePower ρ n))
    (bounded-byᶜ-mul
      (reciprocalFactorial⁺ n)
      (positivePower ρ n)
      (sinPowerSeries n)
      (realPower h n)
      (sinPowerSeriesCoefficientBoundFactorial n)
      powerBound)


cosPowerSeriesTermBoundByExpMajorant :
  (ρ : ℚ⁺) →
  (h : ℝᶜ) →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower h n) →
  BoundedByᶜ (expPositiveMajorantRadius ρ n)
    (powerSeriesTerm cosPowerSeries h n)
cosPowerSeriesTermBoundByExpMajorant ρ h n powerBound =
  subst
    (λ κ → BoundedByᶜ κ (powerSeriesTerm cosPowerSeries h n))
    (*⁺-comm (reciprocalFactorial⁺ n) (positivePower ρ n))
    (bounded-byᶜ-mul
      (reciprocalFactorial⁺ n)
      (positivePower ρ n)
      (cosPowerSeries n)
      (realPower h n)
      (cosPowerSeriesCoefficientBoundFactorial n)
      powerBound)


sinPowerSeriesFactorialMajorized :
  (ρ : ℚ⁺) →
  PowerSeriesMajorizedOnBall
    sinPowerSeries
    ρ
    (expPositiveMajorantTerm ρ)
    (expPositiveMajorantFactorialModulus ρ)
sinPowerSeriesFactorialMajorized ρ =
  powerSeriesMajorizedOnBallFromBoundedTerms
    {a = sinPowerSeries}
    {ρ = ρ}
    {κ = expPositiveMajorantRadius ρ}
    {v = expPositiveMajorantTerm ρ}
    (λ h h-bound n →
      sinPowerSeriesTermBoundByExpMajorant
        ρ
        h
        n
        (realPowerBoundsFromBound ρ h h-bound n))
    (λ n → ≤ᶜ-refl (expPositiveMajorantTerm ρ n))
    (expPositiveMajorantTerm-nonnegative ρ)
    (expPositiveMajorantFactorialTailBound ρ)
    (λ {ε} {δ} ε≤δ →
      expPositiveMajorantFactorialModulusAntitone
        ρ
        {ε = ε}
        {δ = δ}
        ε≤δ)


cosPowerSeriesFactorialMajorized :
  (ρ : ℚ⁺) →
  PowerSeriesMajorizedOnBall
    cosPowerSeries
    ρ
    (expPositiveMajorantTerm ρ)
    (expPositiveMajorantFactorialModulus ρ)
cosPowerSeriesFactorialMajorized ρ =
  powerSeriesMajorizedOnBallFromBoundedTerms
    {a = cosPowerSeries}
    {ρ = ρ}
    {κ = expPositiveMajorantRadius ρ}
    {v = expPositiveMajorantTerm ρ}
    (λ h h-bound n →
      cosPowerSeriesTermBoundByExpMajorant
        ρ
        h
        n
        (realPowerBoundsFromBound ρ h h-bound n))
    (λ n → ≤ᶜ-refl (expPositiveMajorantTerm ρ n))
    (expPositiveMajorantTerm-nonnegative ρ)
    (expPositiveMajorantFactorialTailBound ρ)
    (λ {ε} {δ} ε≤δ →
      expPositiveMajorantFactorialModulusAntitone
        ρ
        {ε = ε}
        {δ = δ}
        ε≤δ)
