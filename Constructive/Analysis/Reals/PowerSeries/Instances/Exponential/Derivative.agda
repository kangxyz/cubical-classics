{-

Part of Constructive.Analysis.Reals.PowerSeries.Instances.Exponential

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Exponential.Derivative where

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
open import Constructive.Analysis.Reals.Calculus.Derivative.Base
  using (HasDerivativeAtWith)
open import Constructive.Analysis.Reals.Calculus.Derivative.Rules
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Majorant
  using
    ( bounded-byᶜ-abs
    ; bounded-byᶜ-scale-rational-closed-bound
    )
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
    ; hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientPathAndTargetRadiusAndIteratedBoundsOnSubballCanonicalIndex
    ; hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientPathAndTargetRadiusAndCoefficientBoundsOnSubballCanonicalIndex
    ; positivePartialSum
    ; powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds
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
open import Constructive.Analysis.Reals.PowerSeries.Instances.Exponential.Convergence

derivativeExpPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius (derivativePowerSeries expPowerSeries)
derivativeExpPowerSeriesInfiniteRadius =
  derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = expPowerSeries}
    {b = expPowerSeries}
    derivativePowerSeries-exp
    expPowerSeriesInfiniteRadius


expPowerSeriesIteratedFormalPartialDerivativeBounds :
  (σ : ℚ⁺) →
  {x : ℝᶜ} →
  BoundedByᶜ σ x →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    expPowerSeries
    x
    (λ s n →
      positivePartialSum
        (λ k →
          scalar-bound (Rational.natMul (suc k) RationalBase.1ℚ) *⁺
          1⁺ *⁺
          positivePower σ k)
        n)
expPowerSeriesIteratedFormalPartialDerivativeBounds σ x-bound =
  powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
    σ
    x-bound
    (λ _ → 1⁺)
    expPowerSeriesCoefficientBoundOne


expᶜHasDerivativeAtWithFromIteratedBoundsOnSubball :
  {x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  {δ : ℕ → ℕ → ℚ⁺} →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement 0ᶜ x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    expPowerSeries
    (centeredDisplacement 0ᶜ x)
    δ →
  PowerSeriesPartialSumsDerivativeModulusLarge
    (termwiseConvergenceIndex
      (expPowerSeriesInfiniteRadius ρ .fst)
      (derivativeExpPowerSeriesInfiniteRadius σ .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus σ δ) →
  HasDerivativeAtWith expᶜ x (expᶜ x) μ
expᶜHasDerivativeAtWithFromIteratedBoundsOnSubball
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
    {a = expPowerSeries}
    {b = expPowerSeries}
    {c = 0ᶜ}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ = μ}
    {δ = δ}
    derivativePowerSeries-exp
    expPowerSeriesInfiniteRadius
    expPowerSeriesInfiniteRadius
    (expᶜHasPowerSeriesAtWithZero ρ)
    x-displacement-bound
    margin
    derivative-bounds
    partialModulus-large


expᶜHasDerivativeAtWithFromCoefficientBoundsOnSubball :
  {x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement 0ᶜ x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  PowerSeriesPartialSumsDerivativeModulusLarge
    (termwiseConvergenceIndex
      (expPowerSeriesInfiniteRadius ρ .fst)
      (derivativeExpPowerSeriesInfiniteRadius σ .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus
      σ
      (powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds
        σ
        (λ _ → 1⁺))) →
  HasDerivativeAtWith expᶜ x (expᶜ x) μ
expᶜHasDerivativeAtWithFromCoefficientBoundsOnSubball
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  x-displacement-bound
  margin
  partialModulus-large =
  hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientPathAndTargetRadiusAndCoefficientBoundsOnSubballCanonicalIndex
    {a = expPowerSeries}
    {b = expPowerSeries}
    {c = 0ᶜ}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ = μ}
    derivativePowerSeries-exp
    expPowerSeriesInfiniteRadius
    expPowerSeriesInfiniteRadius
    (expᶜHasPowerSeriesAtWithZero ρ)
    x-displacement-bound
    margin
    (λ _ → 1⁺)
    expPowerSeriesCoefficientBoundOne
    partialModulus-large


primitiveExpPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius (primitivePowerSeries expPowerSeries)
primitiveExpPowerSeriesInfiniteRadius =
  primitivePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = expPowerSeries}
    {b = subPowerSeries expPowerSeries (constantPowerSeries 1ᶜ)}
    primitivePowerSeries-exp
    (subPowerSeriesInfiniteRadius
      expPowerSeriesInfiniteRadius
      (constantPowerSeriesInfiniteRadius 1ᶜ))


expPowerSeriesOnBallWithFromMajorant :
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  ExpPowerSeriesMajorizedOnBall ρ v μ →
  HasPowerSeriesOnBallWith expPowerSeries ρ μ
expPowerSeriesOnBallWithFromMajorant =
  majorizedOnBall→hasPowerSeriesOnBallWith


expPowerSeriesOnBallFromMajorant :
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  ExpPowerSeriesMajorizedOnBall ρ v μ →
  HasPowerSeriesOnBall expPowerSeries ρ
expPowerSeriesOnBallFromMajorant =
  majorizedOnBall→hasPowerSeriesOnBall


ExpPowerSeriesMajorants :
  Type₀
ExpPowerSeriesMajorants =
  (ρ : ℚ⁺) →
  Σ[ v ∈ (ℕ → ℝᶜ) ]
  Σ[ μ ∈ (ℚ⁺ → ℕ) ]
    ExpPowerSeriesMajorizedOnBall ρ v μ


expPowerSeriesInfiniteRadiusFromMajorants :
  ExpPowerSeriesMajorants →
  HasInfinitePowerSeriesRadius expPowerSeries
expPowerSeriesInfiniteRadiusFromMajorants majorants ρ =
  μ , expPowerSeriesOnBallWithFromMajorant majorant
  where
  v : ℕ → ℝᶜ
  v =
    majorants ρ .fst

  μ : ℚ⁺ → ℕ
  μ =
    majorants ρ .snd .fst

  majorant : ExpPowerSeriesMajorizedOnBall ρ v μ
  majorant =
    majorants ρ .snd .snd
