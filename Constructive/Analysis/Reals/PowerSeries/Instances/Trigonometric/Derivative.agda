{-

Part of Constructive.Analysis.Reals.PowerSeries.Instances.Trigonometric

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Trigonometric.Derivative where

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
open import Constructive.Analysis.Reals.Calculus.Derivative.Base
  using (HasDerivativeAtWith)
open import Constructive.Analysis.Reals.Calculus.Derivative.Rules
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.GeometricDecay
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
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
    ; hasDerivativeAtWith-derivative-path
    ; hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientPathAndTargetRadiusAndIteratedBoundsOnSubballCanonicalIndex
    ; hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientPathAndTargetRadiusAndCoefficientBoundsOnSubballCanonicalIndex
    ; positivePartialSum
    ; powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds
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
open import Constructive.Analysis.Reals.PowerSeries.Instances.Trigonometric.Convergence

derivativeSinPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius (derivativePowerSeries sinPowerSeries)
derivativeSinPowerSeriesInfiniteRadius =
  derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = sinPowerSeries}
    {b = cosPowerSeries}
    derivativePowerSeries-sin
    cosPowerSeriesInfiniteRadius


derivativeCosPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius (derivativePowerSeries cosPowerSeries)
derivativeCosPowerSeriesInfiniteRadius =
  derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = cosPowerSeries}
    {b = negPowerSeries sinPowerSeries}
    derivativePowerSeries-cos
    (negPowerSeriesInfiniteRadius sinPowerSeriesInfiniteRadius)


sinᶜHasDerivativeAtWithFromIteratedBoundsOnSubball :
  {x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  {δ : ℕ → ℕ → ℚ⁺} →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement 0ᶜ x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    sinPowerSeries
    (centeredDisplacement 0ᶜ x)
    δ →
  PowerSeriesPartialSumsDerivativeModulusLarge
    (termwiseConvergenceIndex
      (sinPowerSeriesInfiniteRadius ρ .fst)
      (derivativeSinPowerSeriesInfiniteRadius σ .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus σ δ) →
  HasDerivativeAtWith sinᶜ x (cosᶜ x) μ
sinᶜHasDerivativeAtWithFromIteratedBoundsOnSubball
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {δ = δ}
  x-displacement-bound
  margin
  derivative-bounds
  partialModulus-large =
  hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientPathAndTargetRadiusAndIteratedBoundsOnSubballCanonicalIndex
    {a = sinPowerSeries}
    {b = cosPowerSeries}
    {c = 0ᶜ}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ = μ}
    {δ = δ}
    derivativePowerSeries-sin
    sinPowerSeriesInfiniteRadius
    cosPowerSeriesInfiniteRadius
    (sinᶜHasPowerSeriesAtWithZero ρ)
    x-displacement-bound
    margin
    derivative-bounds
    partialModulus-large


sinᶜHasDerivativeAtWithFromCoefficientBoundsOnSubball :
  {x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement 0ᶜ x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  PowerSeriesPartialSumsDerivativeModulusLarge
    (termwiseConvergenceIndex
      (sinPowerSeriesInfiniteRadius ρ .fst)
      (derivativeSinPowerSeriesInfiniteRadius σ .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus
      σ
      (powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds
        σ
        (λ _ → 1⁺))) →
  HasDerivativeAtWith sinᶜ x (cosᶜ x) μ
sinᶜHasDerivativeAtWithFromCoefficientBoundsOnSubball
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  x-displacement-bound
  margin
  partialModulus-large =
  hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientPathAndTargetRadiusAndCoefficientBoundsOnSubballCanonicalIndex
    {a = sinPowerSeries}
    {b = cosPowerSeries}
    {c = 0ᶜ}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ = μ}
    derivativePowerSeries-sin
    sinPowerSeriesInfiniteRadius
    cosPowerSeriesInfiniteRadius
    (sinᶜHasPowerSeriesAtWithZero ρ)
    x-displacement-bound
    margin
    (λ _ → 1⁺)
    sinPowerSeriesCoefficientBoundOne
    partialModulus-large


cosᶜHasDerivativeAtWithFromIteratedBoundsOnSubball :
  {x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  {δ : ℕ → ℕ → ℚ⁺} →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement 0ᶜ x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    cosPowerSeries
    (centeredDisplacement 0ᶜ x)
    δ →
  PowerSeriesPartialSumsDerivativeModulusLarge
    (termwiseConvergenceIndex
      (cosPowerSeriesInfiniteRadius ρ .fst)
      (derivativeCosPowerSeriesInfiniteRadius σ .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus σ δ) →
  HasDerivativeAtWith cosᶜ x (-ᶜ sinᶜ x) μ
cosᶜHasDerivativeAtWithFromIteratedBoundsOnSubball
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {δ = δ}
  x-displacement-bound
  margin
  derivative-bounds
  partialModulus-large =
  hasDerivativeAtWith-derivative-path
    {f = cosᶜ}
    {x = x}
    {d = negSinᶜ x}
    {e = -ᶜ sinᶜ x}
    {μ = μ}
    (negSinᶜ-path x)
    derivative
  where
  derivative :
    HasDerivativeAtWith cosᶜ x (negSinᶜ x) μ
  derivative =
    hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientPathAndTargetRadiusAndIteratedBoundsOnSubballCanonicalIndex
      {a = cosPowerSeries}
      {b = negPowerSeries sinPowerSeries}
      {c = 0ᶜ}
      {x = x}
      {ρ = ρ}
      {σ = σ}
      {μ = μ}
      {δ = δ}
      derivativePowerSeries-cos
      cosPowerSeriesInfiniteRadius
      (negPowerSeriesInfiniteRadius sinPowerSeriesInfiniteRadius)
      (cosᶜHasPowerSeriesAtWithZero ρ)
      x-displacement-bound
      margin
      derivative-bounds
      partialModulus-large


cosᶜHasDerivativeAtWithFromCoefficientBoundsOnSubball :
  {x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement 0ᶜ x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  PowerSeriesPartialSumsDerivativeModulusLarge
    (termwiseConvergenceIndex
      (cosPowerSeriesInfiniteRadius ρ .fst)
      (derivativeCosPowerSeriesInfiniteRadius σ .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus
      σ
      (powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds
        σ
        (λ _ → 1⁺))) →
  HasDerivativeAtWith cosᶜ x (-ᶜ sinᶜ x) μ
cosᶜHasDerivativeAtWithFromCoefficientBoundsOnSubball
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  x-displacement-bound
  margin
  partialModulus-large =
  hasDerivativeAtWith-derivative-path
    {f = cosᶜ}
    {x = x}
    {d = negSinᶜ x}
    {e = -ᶜ sinᶜ x}
    {μ = μ}
    (negSinᶜ-path x)
    derivative
  where
  derivative :
    HasDerivativeAtWith cosᶜ x (negSinᶜ x) μ
  derivative =
    hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientPathAndTargetRadiusAndCoefficientBoundsOnSubballCanonicalIndex
      {a = cosPowerSeries}
      {b = negPowerSeries sinPowerSeries}
      {c = 0ᶜ}
      {x = x}
      {ρ = ρ}
      {σ = σ}
      {μ = μ}
      derivativePowerSeries-cos
      cosPowerSeriesInfiniteRadius
      (negPowerSeriesInfiniteRadius sinPowerSeriesInfiniteRadius)
      (cosᶜHasPowerSeriesAtWithZero ρ)
      x-displacement-bound
      margin
      (λ _ → 1⁺)
      cosPowerSeriesCoefficientBoundOne
      partialModulus-large


primitiveCosPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius (primitivePowerSeries cosPowerSeries)
primitiveCosPowerSeriesInfiniteRadius =
  primitivePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = cosPowerSeries}
    {b = sinPowerSeries}
    primitivePowerSeries-cos
    sinPowerSeriesInfiniteRadius


primitiveSinPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius (primitivePowerSeries sinPowerSeries)
primitiveSinPowerSeriesInfiniteRadius =
  primitivePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = sinPowerSeries}
    {b = subPowerSeries (constantPowerSeries 1ᶜ) cosPowerSeries}
    primitivePowerSeries-sin
    (subPowerSeriesInfiniteRadius
      (constantPowerSeriesInfiniteRadius 1ᶜ)
      cosPowerSeriesInfiniteRadius)


SinPowerSeriesMajorants :
  Type₀
SinPowerSeriesMajorants =
  (ρ : ℚ⁺) →
  Σ[ v ∈ (ℕ → ℝᶜ) ]
  Σ[ μ ∈ (ℚ⁺ → ℕ) ]
    SinPowerSeriesMajorizedOnBall ρ v μ


CosPowerSeriesMajorants :
  Type₀
CosPowerSeriesMajorants =
  (ρ : ℚ⁺) →
  Σ[ v ∈ (ℕ → ℝᶜ) ]
  Σ[ μ ∈ (ℚ⁺ → ℕ) ]
    CosPowerSeriesMajorizedOnBall ρ v μ


sinPowerSeriesInfiniteRadiusFromMajorants :
  SinPowerSeriesMajorants →
  HasInfinitePowerSeriesRadius sinPowerSeries
sinPowerSeriesInfiniteRadiusFromMajorants majorants ρ =
  μ , sinPowerSeriesOnBallWithFromMajorant majorant
  where
  v : ℕ → ℝᶜ
  v =
    majorants ρ .fst

  μ : ℚ⁺ → ℕ
  μ =
    majorants ρ .snd .fst

  majorant : SinPowerSeriesMajorizedOnBall ρ v μ
  majorant =
    majorants ρ .snd .snd


cosPowerSeriesInfiniteRadiusFromMajorants :
  CosPowerSeriesMajorants →
  HasInfinitePowerSeriesRadius cosPowerSeries
cosPowerSeriesInfiniteRadiusFromMajorants majorants ρ =
  μ , cosPowerSeriesOnBallWithFromMajorant majorant
  where
  v : ℕ → ℝᶜ
  v =
    majorants ρ .fst

  μ : ℚ⁺ → ℕ
  μ =
    majorants ρ .snd .fst

  majorant : CosPowerSeriesMajorizedOnBall ρ v μ
  majorant =
    majorants ρ .snd .snd
