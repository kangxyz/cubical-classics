{-

Part of Constructive.Analysis.Reals.PowerSeries.Elementary.Exponential

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Exponential.Derivative where

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
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using (scalarMulᶜ-nonnegative ; scalarMulᶜ-pres≤ᶜ-scalar)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_ ; ≤ᶜ-refl)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.DerivativeData
  using (HasDerivativeAtWith)
open import Constructive.Analysis.Reals.Calculus.DerivativeRules
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.GeometricDecay
open import Constructive.Analysis.Reals.Series.Geometric.Positive
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Power
  using (realPower)
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
open import Constructive.Analysis.Reals.PowerSeries.FormalDerivative
  using
    ( derivativePowerSeries
    ; inverseSucReal
    ; naturalTimesInverseSucReal-cancel
    ; primitivePowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.Radius
  using
    ( derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    ; primitivePowerSeriesInfiniteRadiusFromCoefficientPath
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.Index
  using (termwiseConvergenceIndex)
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.IteratedBounds
  using
    ( powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds
    ; powerSeriesFormalPartialSumsDerivativeModulus
    )
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.Limit
  using (hasPowerSeriesDerivativeFromCoefficientBounds)
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.PartialSums
  using (PowerSeriesPartialSumsDerivativeModulusLarge)
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

open import Constructive.Analysis.Reals.PowerSeries.Elementary.Exponential.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Elementary.FactorialBounds.Majorant
open import Constructive.Analysis.Reals.PowerSeries.Elementary.FactorialBounds.Tail
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Exponential.Convergence

derivativeExpPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius (derivativePowerSeries expPowerSeries)
derivativeExpPowerSeriesInfiniteRadius =
  derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = expPowerSeries}
    {b = expPowerSeries}
    derivativePowerSeries-exp
    expPowerSeriesInfiniteRadius






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
  hasPowerSeriesDerivativeFromCoefficientBounds
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
