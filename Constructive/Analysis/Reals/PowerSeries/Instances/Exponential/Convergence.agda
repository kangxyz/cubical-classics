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
open import Cubical.Data.Rationals as ℚ using (ℚ)
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
open import Constructive.Analysis.Reals.Calculus.Derivative.Rules
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPowerBoundsFromBound)
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
open import Constructive.Analysis.Reals.PowerSeries.Bounds
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


primitivePowerSeries-exp :
  (n : ℕ) →
  primitivePowerSeries expPowerSeries n ≡
  subPowerSeries expPowerSeries (constantPowerSeries 1ᶜ) n
primitivePowerSeries-exp zero =
  sym (add-inverse-right 1ᶜ)
primitivePowerSeries-exp (suc n) =
  sym (add-zero-right (expPowerSeries (suc n)))


expPowerSeriesFactorialMajorized :
  (ρ : ℚ⁺) →
  PowerSeriesMajorizedOnBall
    expPowerSeries
    ρ
    (expPositiveMajorantTerm ρ)
    (expPositiveMajorantFactorialModulus ρ)
expPowerSeriesFactorialMajorized ρ =
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
