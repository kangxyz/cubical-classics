{-

Part of Constructive.Analysis.Reals.PowerSeries.Instances.Trigonometric

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Trigonometric.Convergence where

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
open import Constructive.Analysis.Reals.PowerSeries.Instances.Trigonometric.Majorants

sinPowerSeriesOnBallWithFromMajorant :
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  SinPowerSeriesMajorizedOnBall ρ v μ →
  HasPowerSeriesOnBallWith sinPowerSeries ρ μ
sinPowerSeriesOnBallWithFromMajorant =
  majorizedOnBall→hasPowerSeriesOnBallWith


cosPowerSeriesOnBallWithFromMajorant :
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  CosPowerSeriesMajorizedOnBall ρ v μ →
  HasPowerSeriesOnBallWith cosPowerSeries ρ μ
cosPowerSeriesOnBallWithFromMajorant =
  majorizedOnBall→hasPowerSeriesOnBallWith


sinPowerSeriesOnSubunitBallWith :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  HasPowerSeriesOnBallWith
    sinPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
sinPowerSeriesOnSubunitBallWith ρ ρ<1 =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (sinPowerSeriesSubunitMajorized ρ ρ<1)


cosPowerSeriesOnSubunitBallWith :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  HasPowerSeriesOnBallWith
    cosPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
cosPowerSeriesOnSubunitBallWith ρ ρ<1 =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (cosPowerSeriesSubunitMajorized ρ ρ<1)


sinPowerSeriesOnBallFromMajorant :
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  SinPowerSeriesMajorizedOnBall ρ v μ →
  HasPowerSeriesOnBall sinPowerSeries ρ
sinPowerSeriesOnBallFromMajorant =
  majorizedOnBall→hasPowerSeriesOnBall


cosPowerSeriesOnBallFromMajorant :
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  CosPowerSeriesMajorizedOnBall ρ v μ →
  HasPowerSeriesOnBall cosPowerSeries ρ
cosPowerSeriesOnBallFromMajorant =
  majorizedOnBall→hasPowerSeriesOnBall


sinPowerSeriesOnSubunitBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  HasPowerSeriesOnBall sinPowerSeries ρ
sinPowerSeriesOnSubunitBall ρ ρ<1 =
  positiveGeometricPowerModulus ρ ρ<1 ,
  sinPowerSeriesOnSubunitBallWith ρ ρ<1


cosPowerSeriesOnSubunitBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  HasPowerSeriesOnBall cosPowerSeries ρ
cosPowerSeriesOnSubunitBall ρ ρ<1 =
  positiveGeometricPowerModulus ρ ρ<1 ,
  cosPowerSeriesOnSubunitBallWith ρ ρ<1


sinPowerSeriesOnBallWith :
  (ρ : ℚ⁺) →
  HasPowerSeriesOnBallWith
    sinPowerSeries
    ρ
    (expPositiveMajorantFactorialModulus ρ)
sinPowerSeriesOnBallWith ρ =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (sinPowerSeriesFactorialMajorized ρ)


cosPowerSeriesOnBallWith :
  (ρ : ℚ⁺) →
  HasPowerSeriesOnBallWith
    cosPowerSeries
    ρ
    (expPositiveMajorantFactorialModulus ρ)
cosPowerSeriesOnBallWith ρ =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (cosPowerSeriesFactorialMajorized ρ)


sinPowerSeriesOnBall :
  (ρ : ℚ⁺) →
  HasPowerSeriesOnBall sinPowerSeries ρ
sinPowerSeriesOnBall ρ =
  expPositiveMajorantFactorialModulus ρ ,
  sinPowerSeriesOnBallWith ρ


cosPowerSeriesOnBall :
  (ρ : ℚ⁺) →
  HasPowerSeriesOnBall cosPowerSeries ρ
cosPowerSeriesOnBall ρ =
  expPositiveMajorantFactorialModulus ρ ,
  cosPowerSeriesOnBallWith ρ


sinPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius sinPowerSeries
sinPowerSeriesInfiniteRadius =
  sinPowerSeriesOnBall


cosPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius cosPowerSeries
cosPowerSeriesInfiniteRadius =
  cosPowerSeriesOnBall


sinᶜ :
  ℝᶜ →
  ℝᶜ
sinᶜ =
  centeredPowerSeriesSumEverywhere
    sinPowerSeries
    0ᶜ
    sinPowerSeriesInfiniteRadius


cosᶜ :
  ℝᶜ →
  ℝᶜ
cosᶜ =
  centeredPowerSeriesSumEverywhere
    cosPowerSeries
    0ᶜ
    cosPowerSeriesInfiniteRadius


sinᶜ-zero :
  sinᶜ 0ᶜ ≡ 0ᶜ
sinᶜ-zero =
  centeredPowerSeriesSumEverywhere-center
    sinPowerSeriesInfiniteRadius
    0ᶜ


cosᶜ-zero :
  cosᶜ 0ᶜ ≡ 1ᶜ
cosᶜ-zero =
  centeredPowerSeriesSumEverywhere-center
    cosPowerSeriesInfiniteRadius
    0ᶜ


negSinᶜ :
  ℝᶜ →
  ℝᶜ
negSinᶜ =
  centeredPowerSeriesSumEverywhere
    (negPowerSeries sinPowerSeries)
    0ᶜ
    (negPowerSeriesInfiniteRadius sinPowerSeriesInfiniteRadius)


negSinᶜ-path :
  (x : ℝᶜ) →
  negSinᶜ x ≡ -ᶜ sinᶜ x
negSinᶜ-path =
  centeredPowerSeriesSumEverywhere-neg
    sinPowerSeriesInfiniteRadius
    0ᶜ


sinᶜHasPowerSeriesAtWithZero :
  (ρ : ℚ⁺) →
  HasPowerSeriesAtWith
    sinᶜ
    0ᶜ
    sinPowerSeries
    ρ
    (sinPowerSeriesInfiniteRadius ρ .fst)
sinᶜHasPowerSeriesAtWithZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
    sinPowerSeriesInfiniteRadius


cosᶜHasPowerSeriesAtWithZero :
  (ρ : ℚ⁺) →
  HasPowerSeriesAtWith
    cosᶜ
    0ᶜ
    cosPowerSeries
    ρ
    (cosPowerSeriesInfiniteRadius ρ .fst)
cosᶜHasPowerSeriesAtWithZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
    cosPowerSeriesInfiniteRadius


sinᶜHasPowerSeriesAtOnBallZero :
  (ρ : ℚ⁺) →
  HasPowerSeriesAtOnBall sinᶜ 0ᶜ sinPowerSeries ρ
sinᶜHasPowerSeriesAtOnBallZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAtOnBall
    sinPowerSeriesInfiniteRadius


cosᶜHasPowerSeriesAtOnBallZero :
  (ρ : ℚ⁺) →
  HasPowerSeriesAtOnBall cosᶜ 0ᶜ cosPowerSeries ρ
cosᶜHasPowerSeriesAtOnBallZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAtOnBall
    cosPowerSeriesInfiniteRadius


sinᶜHasPowerSeriesAtZero :
  HasPowerSeriesAt sinᶜ 0ᶜ sinPowerSeries
sinᶜHasPowerSeriesAtZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAt
    sinPowerSeriesInfiniteRadius


cosᶜHasPowerSeriesAtZero :
  HasPowerSeriesAt cosᶜ 0ᶜ cosPowerSeries
cosᶜHasPowerSeriesAtZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAt
    cosPowerSeriesInfiniteRadius


sinᶜAnalyticAtZero :
  AnalyticAt sinᶜ 0ᶜ
sinᶜAnalyticAtZero =
  centeredPowerSeriesSumEverywhereAnalyticAt
    sinPowerSeries
    0ᶜ
    sinPowerSeriesInfiniteRadius


cosᶜAnalyticAtZero :
  AnalyticAt cosᶜ 0ᶜ
cosᶜAnalyticAtZero =
  centeredPowerSeriesSumEverywhereAnalyticAt
    cosPowerSeries
    0ᶜ
    cosPowerSeriesInfiniteRadius
