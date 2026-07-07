{-

Part of Constructive.Analysis.Reals.PowerSeries.Instances.Exponential

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Exponential.Convergence where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (scalarMulᶜ-nonnegative ; scalarMulᶜ-pres≤ᶜ-scalar)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_ ; ≤ᶜ-refl)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.Derivative
  using (HasDerivativeAtWith)
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Majorant
  using
    ( bounded-byᶜ-abs
    ; bounded-byᶜ-scale-rational-closed-bound
    )
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
    ; constantPowerSeries
    ; constantPowerSeriesInfiniteRadius
    ; rationalScaleModulus
    ; rationalScaleModulus-antitone
    ; rationalScalePrecision
    ; rationalScalePrecision-mono
    ; rationalScaleTailBound
    ; subPowerSeries
    ; subPowerSeriesInfiniteRadius
    )
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using
    ( derivativePowerSeries
    ; inverseSucReal
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
    ; HasPowerSeriesAtContinuousAt
    ; HasPowerSeriesAtOnBall
    ; HasPowerSeriesAtUniformlyContinuousOnBall
    ; HasPowerSeriesAtWith
    ; HasPowerSeriesAtWithBounds
    ; HasPowerSeriesAtMerelyContinuousAt
    ; HasPowerSeriesAtMerelyUniformlyContinuousOnBall
    ; centeredPowerSeriesSumEverywhereAnalyticAt
    ; centeredPowerSeriesSumEverywhereHasPowerSeriesAt
    ; centeredPowerSeriesSumEverywhereHasPowerSeriesAtOnBall
    ; centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
    ; hasPowerSeriesAtWithBounds→continuousAt
    ; hasPowerSeriesAtWithBounds→merelyContinuousAt
    ; hasPowerSeriesAtWithBounds→merelyUniformlyContinuousOnBall
    ; hasPowerSeriesAtWithBounds→uniformlyContinuousOnBall
    )
open import Constructive.Analysis.Reals.PowerSeries.Continuity
  using (PowerSeriesCoefficientBounds)
open import Constructive.Analysis.Reals.PowerSeries.Majorant
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative
  using
    ( PowerSeriesIteratedFormalPartialDerivativeBounds
    ; PowerSeriesPartialSumsDerivativeModulusLarge
    ; centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
    ; positivePartialSum
    ; powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
    ; powerSeriesFormalPartialSumsDerivativeModulus
    ; termwiseConvergenceIndex
    )
open import Constructive.Data.PositiveRationals
  using
    ( ℚ⁺
    ; 1⁺
    ; _+⁺_
    ; _*⁺_
    ; *⁺-comm
    ; *⁺-identity-left
    ; half⁺
    ; half<
    ; radius
    ; scalar-bound
    )
import Constructive.Data.Rationals.Base as RationalBase
import Constructive.Data.Rationals.Archimedean as Rational
import Constructive.Data.Rationals.Factorial as Factorial
import Constructive.Data.Rationals.Multiplication as RationalMul

open import Constructive.Analysis.Reals.PowerSeries.Instances.Exponential.Internal
open import Constructive.Analysis.Reals.PowerSeries.Instances.Exponential.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Instances.Exponential.Majorant
open import Constructive.Analysis.Reals.PowerSeries.Instances.Exponential.Tail

derivativePowerSeries-exp :
  (n : ℕ) →
  derivativePowerSeries expPowerSeries n ≡ expPowerSeries n
derivativePowerSeries-exp n =
  naturalTimesInverseSucReal-cancel n (expPowerSeries n)


primitivePowerSeries-exp-zero :
  primitivePowerSeries expPowerSeries zero ≡ 0ᶜ
primitivePowerSeries-exp-zero =
  refl


primitivePowerSeries-exp-suc :
  (n : ℕ) →
  primitivePowerSeries expPowerSeries (suc n) ≡
  expPowerSeries (suc n)
primitivePowerSeries-exp-suc n =
  refl


primitivePowerSeries-exp :
  (n : ℕ) →
  primitivePowerSeries expPowerSeries n ≡
  subPowerSeries expPowerSeries (constantPowerSeries 1ᶜ) n
primitivePowerSeries-exp zero =
  sym (add-inverse-right 1ᶜ)
primitivePowerSeries-exp (suc n) =
  sym (add-zero-right (expPowerSeries (suc n)))


ExpPowerSeriesMajorizedOnBall :
  ℚ⁺ →
  (ℕ → ℝᶜ) →
  (ℚ⁺ → ℕ) →
  Type₀
ExpPowerSeriesMajorizedOnBall ρ v μ =
  PowerSeriesMajorizedOnBall expPowerSeries ρ v μ


ExpPowerSeriesPowerBoundsOnBall :
  ℚ⁺ →
  Type₀
ExpPowerSeriesPowerBoundsOnBall ρ =
  (h : ℝᶜ) →
  BoundedByᶜ ρ h →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower h n)


ExpPositiveMajorantTailBound :
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type₀
ExpPositiveMajorantTailBound ρ μ =
  TailBound (expPositiveMajorantTerm ρ) μ


ExpPositiveMajorantDoubledUpper :
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type₀
ExpPositiveMajorantDoubledUpper ρ μ =
  (ε : ℚ⁺) →
  (m : ℕ) →
  NatOrder._≤_ (μ ε) m →
  expPositiveMajorantTerm ρ m +ᶜ expPositiveMajorantTerm ρ m
    ≤ᶜ rational (radius ε)


expPositiveMajorantTailBoundFromDoubledUpper :
  (ρ : ℚ⁺) →
  (cutoff : ExpMajorantRatioCutoff ρ) →
  {μ : ℚ⁺ → ℕ} →
  ((ε : ℚ⁺) → NatOrder._≤_ (cutoff .fst) (μ ε)) →
  ExpPositiveMajorantDoubledUpper ρ μ →
  ExpPositiveMajorantTailBound ρ μ
expPositiveMajorantTailBoundFromDoubledUpper ρ cutoff cutoff≤μ doubledUpper =
  eventual-ratio-half-tailBound
    (expPositiveMajorantTerm-nonnegative ρ)
    (cutoff .fst)
    (expPositiveMajorantTerm-eventual-ratio-half ρ cutoff)
    cutoff≤μ
    doubledUpper


expPowerSeriesFactorialMajorizedFromPowerBounds :
  (ρ : ℚ⁺) →
  {μ : ℚ⁺ → ℕ} →
  ExpPowerSeriesPowerBoundsOnBall ρ →
  ExpPositiveMajorantTailBound ρ μ →
  AntitoneTailModulus μ →
  ExpPowerSeriesMajorizedOnBall ρ (expPositiveMajorantTerm ρ) μ
expPowerSeriesFactorialMajorizedFromPowerBounds ρ powerBounds tailBound antitone =
  powerSeriesMajorizedOnBallFromBoundedTerms
    {a = expPowerSeries}
    {ρ = ρ}
    {κ = expPositiveMajorantRadius ρ}
    {v = expPositiveMajorantTerm ρ}
    (λ h h-bound n →
      expPowerSeriesTermBoundByPositiveMajorant
        ρ
        h
        n
        (powerBounds h h-bound n))
    (λ n → ≤ᶜ-refl (expPositiveMajorantTerm ρ n))
    (expPositiveMajorantTerm-nonnegative ρ)
    tailBound
    antitone


expPowerSeriesSubunitMajorizedFromPowerBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : ℚOrder._<_ (Constructive.Data.PositiveRationals.radius ρ) RationalBase.1ℚ) →
  ExpPowerSeriesPowerBoundsOnBall ρ →
  ExpPowerSeriesMajorizedOnBall
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
expPowerSeriesSubunitMajorizedFromPowerBounds ρ ρ<1 powerBounds =
  powerSeriesMajorizedOnBallFromBoundedTerms
    {a = expPowerSeries}
    {ρ = ρ}
    {κ = positivePower ρ}
    {v = positiveGeometricTerm ρ}
    (λ h h-bound n →
      expPowerSeriesTermBoundFromPowerBound
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


expPowerSeriesPowerBoundsFromBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  ExpPowerSeriesPowerBoundsOnBall ρ
expPowerSeriesPowerBoundsFromBall ρ ρ<1 h h-bound n =
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


expPowerSeriesPowerBoundsOnAnyBall :
  (ρ : ℚ⁺) →
  ExpPowerSeriesPowerBoundsOnBall ρ
expPowerSeriesPowerBoundsOnAnyBall ρ h h-bound n =
  realPowerBoundsFromBound ρ h h-bound n


expPowerSeriesFactorialMajorized :
  (ρ : ℚ⁺) →
  ExpPowerSeriesMajorizedOnBall
    ρ
    (expPositiveMajorantTerm ρ)
    (expPositiveMajorantFactorialModulus ρ)
expPowerSeriesFactorialMajorized ρ =
  expPowerSeriesFactorialMajorizedFromPowerBounds
    ρ
    (expPowerSeriesPowerBoundsOnAnyBall ρ)
    (expPositiveMajorantFactorialTailBound ρ)
    (λ {ε} {δ} ε≤δ →
      expPositiveMajorantFactorialModulusAntitone
        ρ
        {ε = ε}
        {δ = δ}
        ε≤δ)


expPowerSeriesSubunitMajorized :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  ExpPowerSeriesMajorizedOnBall
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
expPowerSeriesSubunitMajorized ρ ρ<1 =
  expPowerSeriesSubunitMajorizedFromPowerBounds
    ρ
    ρ<1
    (expPowerSeriesPowerBoundsFromBall ρ ρ<1)


expPowerSeriesOnSubunitBallWithFromPowerBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : ℚOrder._<_ (Constructive.Data.PositiveRationals.radius ρ) RationalBase.1ℚ) →
  ExpPowerSeriesPowerBoundsOnBall ρ →
  HasPowerSeriesOnBallWith
    expPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
expPowerSeriesOnSubunitBallWithFromPowerBounds ρ ρ<1 powerBounds =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (expPowerSeriesSubunitMajorizedFromPowerBounds ρ ρ<1 powerBounds)


expPowerSeriesOnSubunitBallWith :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  HasPowerSeriesOnBallWith
    expPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
expPowerSeriesOnSubunitBallWith ρ ρ<1 =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (expPowerSeriesSubunitMajorized ρ ρ<1)


expPowerSeriesOnSubunitBallFromPowerBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : ℚOrder._<_ (Constructive.Data.PositiveRationals.radius ρ) RationalBase.1ℚ) →
  ExpPowerSeriesPowerBoundsOnBall ρ →
  HasPowerSeriesOnBall expPowerSeries ρ
expPowerSeriesOnSubunitBallFromPowerBounds ρ ρ<1 powerBounds =
  positiveGeometricPowerModulus ρ ρ<1 ,
  expPowerSeriesOnSubunitBallWithFromPowerBounds ρ ρ<1 powerBounds


expPowerSeriesOnSubunitBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  HasPowerSeriesOnBall expPowerSeries ρ
expPowerSeriesOnSubunitBall ρ ρ<1 =
  positiveGeometricPowerModulus ρ ρ<1 ,
  expPowerSeriesOnSubunitBallWith ρ ρ<1


expPowerSeriesOnBallWith :
  (ρ : ℚ⁺) →
  HasPowerSeriesOnBallWith
    expPowerSeries
    ρ
    (expPositiveMajorantFactorialModulus ρ)
expPowerSeriesOnBallWith ρ =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (expPowerSeriesFactorialMajorized ρ)


expPowerSeriesOnBall :
  (ρ : ℚ⁺) →
  HasPowerSeriesOnBall expPowerSeries ρ
expPowerSeriesOnBall ρ =
  expPositiveMajorantFactorialModulus ρ ,
  expPowerSeriesOnBallWith ρ


expPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius expPowerSeries
expPowerSeriesInfiniteRadius =
  expPowerSeriesOnBall


expᶜ :
  ℝᶜ →
  ℝᶜ
expᶜ =
  centeredPowerSeriesSumEverywhere
    expPowerSeries
    0ᶜ
    expPowerSeriesInfiniteRadius


expᶜ-zero :
  expᶜ 0ᶜ ≡ 1ᶜ
expᶜ-zero =
  centeredPowerSeriesSumEverywhere-center
    expPowerSeriesInfiniteRadius
    0ᶜ


expPowerSeriesCoefficientBounds :
  PowerSeriesCoefficientBounds expPowerSeries
expPowerSeriesCoefficientBounds =
  (λ _ → 1⁺) ,
  expPowerSeriesCoefficientBoundOne


expᶜHasPowerSeriesAtWithZero :
  (ρ : ℚ⁺) →
  HasPowerSeriesAtWith
    expᶜ
    0ᶜ
    expPowerSeries
    ρ
    (expPowerSeriesInfiniteRadius ρ .fst)
expᶜHasPowerSeriesAtWithZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
    expPowerSeriesInfiniteRadius


expᶜHasPowerSeriesAtWithBoundsZero :
  (ρ : ℚ⁺) →
  HasPowerSeriesAtWithBounds
    expᶜ
    0ᶜ
    expPowerSeries
    ρ
    (expPowerSeriesInfiniteRadius ρ .fst)
expᶜHasPowerSeriesAtWithBoundsZero ρ =
  expᶜHasPowerSeriesAtWithZero ρ ,
  expPowerSeriesCoefficientBounds


expᶜUniformlyContinuousOnBallFromCoefficientBounds :
  (ρ : ℚ⁺) →
  HasPowerSeriesAtUniformlyContinuousOnBall expᶜ 0ᶜ ρ
expᶜUniformlyContinuousOnBallFromCoefficientBounds ρ =
  hasPowerSeriesAtWithBounds→uniformlyContinuousOnBall
    (expᶜHasPowerSeriesAtWithBoundsZero ρ)


expᶜMerelyUniformlyContinuousOnBallFromBounds :
  (ρ : ℚ⁺) →
  HasPowerSeriesAtMerelyUniformlyContinuousOnBall expᶜ 0ᶜ ρ
expᶜMerelyUniformlyContinuousOnBallFromBounds ρ =
  hasPowerSeriesAtWithBounds→merelyUniformlyContinuousOnBall
    (expᶜHasPowerSeriesAtWithBoundsZero ρ)


expᶜContinuousAtFromCoefficientBounds :
  (ρ : ℚ⁺) →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall 0ᶜ ρ x) →
  HasPowerSeriesAtContinuousAt expᶜ 0ᶜ ρ x x-inBall
expᶜContinuousAtFromCoefficientBounds ρ x x-inBall =
  hasPowerSeriesAtWithBounds→continuousAt
    (expᶜHasPowerSeriesAtWithBoundsZero ρ)
    x
    x-inBall


expᶜMerelyContinuousAtFromBounds :
  (ρ : ℚ⁺) →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall 0ᶜ ρ x) →
  HasPowerSeriesAtMerelyContinuousAt expᶜ 0ᶜ ρ x x-inBall
expᶜMerelyContinuousAtFromBounds ρ x x-inBall =
  hasPowerSeriesAtWithBounds→merelyContinuousAt
    (expᶜHasPowerSeriesAtWithBoundsZero ρ)
    x
    x-inBall


expᶜHasPowerSeriesAtOnBallZero :
  (ρ : ℚ⁺) →
  HasPowerSeriesAtOnBall expᶜ 0ᶜ expPowerSeries ρ
expᶜHasPowerSeriesAtOnBallZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAtOnBall
    expPowerSeriesInfiniteRadius


expᶜHasPowerSeriesAtZero :
  HasPowerSeriesAt expᶜ 0ᶜ expPowerSeries
expᶜHasPowerSeriesAtZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAt
    expPowerSeriesInfiniteRadius


expᶜAnalyticAtZero :
  AnalyticAt expᶜ 0ᶜ
expᶜAnalyticAtZero =
  centeredPowerSeriesSumEverywhereAnalyticAt
    expPowerSeries
    0ᶜ
    expPowerSeriesInfiniteRadius
