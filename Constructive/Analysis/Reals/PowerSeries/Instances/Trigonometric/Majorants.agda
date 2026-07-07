{-

Part of Constructive.Analysis.Reals.PowerSeries.Instances.Trigonometric

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Trigonometric.Majorants where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
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
open import Constructive.Analysis.Reals.Calculus.Derivative
  using (HasDerivativeAtWith)
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
  using
    ( positiveGeometricPowerModulus
    ; positiveGeometricPowerModulus-antitone
    ; positiveGeometricFiniteTailBoundFromRatio
    ; positiveGeometricTerm
    ; positiveGeometricTerm-nonnegative
    ; positivePower
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using
    ( RealGeometricBound
    ; RealGeometricPowerBounds
    ; realGeometricPowerBoundsFromBound
    ; realPowerBoundsFromBound
    ; realPower
    )
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
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence
  using
    ( derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    ; primitivePowerSeriesInfiniteRadiusFromCoefficientPath
    )
open import Constructive.Analysis.Reals.PowerSeries.Analytic
  using
    ( AnalyticAt
    ; HasPowerSeriesAt
    ; HasPowerSeriesAtOnBall
    ; HasPowerSeriesAtWith
    ; centeredPowerSeriesSumEverywhereAnalyticAt
    ; centeredPowerSeriesSumEverywhereHasPowerSeriesAt
    ; centeredPowerSeriesSumEverywhereHasPowerSeriesAtOnBall
    ; centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative
  using
    ( PowerSeriesIteratedFormalPartialDerivativeBounds
    ; PowerSeriesPartialSumsDerivativeModulusLarge
    ; centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
    ; hasDerivativeAtWith-derivative-path
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

open import Constructive.Analysis.Reals.PowerSeries.Instances.Trigonometric.Internal
open import Constructive.Analysis.Reals.PowerSeries.Instances.Trigonometric.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Instances.Trigonometric.Bounds

sinPowerSeriesTermBoundFromPowerBound :
  (ρ : ℚ⁺) →
  (h : ℝᶜ) →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower h n) →
  BoundedByᶜ (positivePower ρ n) (powerSeriesTerm sinPowerSeries h n)
sinPowerSeriesTermBoundFromPowerBound ρ h n powerBound =
  subst
    (λ κ → BoundedByᶜ κ (powerSeriesTerm sinPowerSeries h n))
    (*⁺-identity-left (positivePower ρ n))
    (bounded-byᶜ-mul
      1⁺
      (positivePower ρ n)
      (sinPowerSeries n)
      (realPower h n)
      (sinPowerSeriesCoefficientBoundOne n)
      powerBound)


cosPowerSeriesTermBoundFromPowerBound :
  (ρ : ℚ⁺) →
  (h : ℝᶜ) →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower h n) →
  BoundedByᶜ (positivePower ρ n) (powerSeriesTerm cosPowerSeries h n)
cosPowerSeriesTermBoundFromPowerBound ρ h n powerBound =
  subst
    (λ κ → BoundedByᶜ κ (powerSeriesTerm cosPowerSeries h n))
    (*⁺-identity-left (positivePower ρ n))
    (bounded-byᶜ-mul
      1⁺
      (positivePower ρ n)
      (cosPowerSeries n)
      (realPower h n)
      (cosPowerSeriesCoefficientBoundOne n)
      powerBound)


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


SinPowerSeriesMajorizedOnBall :
  ℚ⁺ →
  (ℕ → ℝᶜ) →
  (ℚ⁺ → ℕ) →
  Type₀
SinPowerSeriesMajorizedOnBall ρ v μ =
  PowerSeriesMajorizedOnBall sinPowerSeries ρ v μ


CosPowerSeriesMajorizedOnBall :
  ℚ⁺ →
  (ℕ → ℝᶜ) →
  (ℚ⁺ → ℕ) →
  Type₀
CosPowerSeriesMajorizedOnBall ρ v μ =
  PowerSeriesMajorizedOnBall cosPowerSeries ρ v μ


TrigPowerSeriesPowerBoundsOnBall :
  ℚ⁺ →
  Type₀
TrigPowerSeriesPowerBoundsOnBall ρ =
  (h : ℝᶜ) →
  BoundedByᶜ ρ h →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower h n)


trigPowerSeriesPowerBoundsFromBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  TrigPowerSeriesPowerBoundsOnBall ρ
trigPowerSeriesPowerBoundsFromBall ρ ρ<1 h h-bound n =
  RealGeometricPowerBounds.powerBound
    (realGeometricPowerBoundsFromBound h bound)
    n
  where
  bound : RealGeometricBound h
  bound =
    record
      { ratioBound = ρ
      ; ratioBound<1 = ρ<1
      ; termBound = h-bound
      }


trigPowerSeriesPowerBoundsOnAnyBall :
  (ρ : ℚ⁺) →
  TrigPowerSeriesPowerBoundsOnBall ρ
trigPowerSeriesPowerBoundsOnAnyBall ρ h h-bound n =
  realPowerBoundsFromBound ρ h h-bound n


sinPowerSeriesFactorialMajorizedFromPowerBounds :
  (ρ : ℚ⁺) →
  TrigPowerSeriesPowerBoundsOnBall ρ →
  SinPowerSeriesMajorizedOnBall
    ρ
    (expPositiveMajorantTerm ρ)
    (expPositiveMajorantFactorialModulus ρ)
sinPowerSeriesFactorialMajorizedFromPowerBounds ρ powerBounds =
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
        (powerBounds h h-bound n))
    (λ n → ≤ᶜ-refl (expPositiveMajorantTerm ρ n))
    (expPositiveMajorantTerm-nonnegative ρ)
    (expPositiveMajorantFactorialTailBound ρ)
    (λ {ε} {δ} ε≤δ →
      expPositiveMajorantFactorialModulusAntitone
        ρ
        {ε = ε}
        {δ = δ}
        ε≤δ)


cosPowerSeriesFactorialMajorizedFromPowerBounds :
  (ρ : ℚ⁺) →
  TrigPowerSeriesPowerBoundsOnBall ρ →
  CosPowerSeriesMajorizedOnBall
    ρ
    (expPositiveMajorantTerm ρ)
    (expPositiveMajorantFactorialModulus ρ)
cosPowerSeriesFactorialMajorizedFromPowerBounds ρ powerBounds =
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
        (powerBounds h h-bound n))
    (λ n → ≤ᶜ-refl (expPositiveMajorantTerm ρ n))
    (expPositiveMajorantTerm-nonnegative ρ)
    (expPositiveMajorantFactorialTailBound ρ)
    (λ {ε} {δ} ε≤δ →
      expPositiveMajorantFactorialModulusAntitone
        ρ
        {ε = ε}
        {δ = δ}
        ε≤δ)


sinPowerSeriesFactorialMajorized :
  (ρ : ℚ⁺) →
  SinPowerSeriesMajorizedOnBall
    ρ
    (expPositiveMajorantTerm ρ)
    (expPositiveMajorantFactorialModulus ρ)
sinPowerSeriesFactorialMajorized ρ =
  sinPowerSeriesFactorialMajorizedFromPowerBounds
    ρ
    (trigPowerSeriesPowerBoundsOnAnyBall ρ)


cosPowerSeriesFactorialMajorized :
  (ρ : ℚ⁺) →
  CosPowerSeriesMajorizedOnBall
    ρ
    (expPositiveMajorantTerm ρ)
    (expPositiveMajorantFactorialModulus ρ)
cosPowerSeriesFactorialMajorized ρ =
  cosPowerSeriesFactorialMajorizedFromPowerBounds
    ρ
    (trigPowerSeriesPowerBoundsOnAnyBall ρ)


sinPowerSeriesSubunitMajorizedFromPowerBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  TrigPowerSeriesPowerBoundsOnBall ρ →
  SinPowerSeriesMajorizedOnBall
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
sinPowerSeriesSubunitMajorizedFromPowerBounds ρ ρ<1 powerBounds =
  powerSeriesMajorizedOnBallFromBoundedTerms
    {a = sinPowerSeries}
    {ρ = ρ}
    {κ = positivePower ρ}
    {v = positiveGeometricTerm ρ}
    (λ h h-bound n →
      sinPowerSeriesTermBoundFromPowerBound
        ρ
        h
        n
        (powerBounds h h-bound n))
    (λ n → ≤ᶜ-refl (positiveGeometricTerm ρ n))
    (positiveGeometricTerm-nonnegative ρ)
    (λ ε m k μ≤m →
      positiveGeometricFiniteTailBoundFromRatio ρ ρ<1 ε m k μ≤m)
    (λ {ε} {δ} ε≤δ →
      positiveGeometricPowerModulus-antitone
        ρ
        ρ<1
        {ε = ε}
        {δ = δ}
        ε≤δ)


cosPowerSeriesSubunitMajorizedFromPowerBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  TrigPowerSeriesPowerBoundsOnBall ρ →
  CosPowerSeriesMajorizedOnBall
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
cosPowerSeriesSubunitMajorizedFromPowerBounds ρ ρ<1 powerBounds =
  powerSeriesMajorizedOnBallFromBoundedTerms
    {a = cosPowerSeries}
    {ρ = ρ}
    {κ = positivePower ρ}
    {v = positiveGeometricTerm ρ}
    (λ h h-bound n →
      cosPowerSeriesTermBoundFromPowerBound
        ρ
        h
        n
        (powerBounds h h-bound n))
    (λ n → ≤ᶜ-refl (positiveGeometricTerm ρ n))
    (positiveGeometricTerm-nonnegative ρ)
    (λ ε m k μ≤m →
      positiveGeometricFiniteTailBoundFromRatio ρ ρ<1 ε m k μ≤m)
    (λ {ε} {δ} ε≤δ →
      positiveGeometricPowerModulus-antitone
        ρ
        ρ<1
        {ε = ε}
        {δ = δ}
        ε≤δ)


sinPowerSeriesSubunitMajorized :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  SinPowerSeriesMajorizedOnBall
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
sinPowerSeriesSubunitMajorized ρ ρ<1 =
  sinPowerSeriesSubunitMajorizedFromPowerBounds
    ρ
    ρ<1
    (trigPowerSeriesPowerBoundsFromBall ρ ρ<1)


cosPowerSeriesSubunitMajorized :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  CosPowerSeriesMajorizedOnBall
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
cosPowerSeriesSubunitMajorized ρ ρ<1 =
  cosPowerSeriesSubunitMajorizedFromPowerBounds
    ρ
    ρ<1
    (trigPowerSeriesPowerBoundsFromBall ρ ρ<1)
