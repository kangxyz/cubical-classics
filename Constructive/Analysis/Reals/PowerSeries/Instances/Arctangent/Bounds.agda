{-

Coefficient and finite-derivative bounds for atanh and atan

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Bounds where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
  using (positivePower)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Continuity
  using (PowerSeriesCoefficientBounds)
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using (inverseSucReal ; primitivePowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative
  using
    ( PowerSeriesIteratedFormalPartialDerivativeBounds
    ; positivePartialSum
    ; powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
    )
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm
  using
    ( logInverseSucRealBoundOne
    ; logOneBoundOne
    ; logZeroBoundOne
    )
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


evenGeometricPowerSeriesCoefficientBoundOne :
  (n : ℕ) →
  BoundedByᶜ 1⁺ (evenGeometricPowerSeries n)
evenGeometricPowerSeriesCoefficientBoundOne zero =
  logOneBoundOne
evenGeometricPowerSeriesCoefficientBoundOne (suc zero) =
  logZeroBoundOne
evenGeometricPowerSeriesCoefficientBoundOne (suc (suc n)) =
  evenGeometricPowerSeriesCoefficientBoundOne n


alternatingEvenGeometricPowerSeriesCoefficientBoundOne :
  (n : ℕ) →
  BoundedByᶜ 1⁺ (alternatingEvenGeometricPowerSeries n)
alternatingEvenGeometricPowerSeriesCoefficientBoundOne zero =
  logOneBoundOne
alternatingEvenGeometricPowerSeriesCoefficientBoundOne (suc zero) =
  logZeroBoundOne
alternatingEvenGeometricPowerSeriesCoefficientBoundOne (suc (suc n)) =
  bounded-byᶜ-neg
    1⁺
    (alternatingEvenGeometricPowerSeries n)
    (alternatingEvenGeometricPowerSeriesCoefficientBoundOne n)


primitivePowerSeriesCoefficientBoundOne :
  (a : PowerSeries) →
  ((n : ℕ) → BoundedByᶜ 1⁺ (a n)) →
  (n : ℕ) →
  BoundedByᶜ 1⁺ (primitivePowerSeries a n)
primitivePowerSeriesCoefficientBoundOne a coefficientBound zero =
  logZeroBoundOne
primitivePowerSeriesCoefficientBoundOne a coefficientBound (suc n) =
  subst
    (λ κ → BoundedByᶜ κ (primitivePowerSeries a (suc n)))
    (*⁺-identity-left 1⁺)
    (bounded-byᶜ-mul
      1⁺
      1⁺
      (inverseSucReal n)
      (a n)
      (logInverseSucRealBoundOne n)
      (coefficientBound n))


atanhPowerSeriesCoefficientBoundOne :
  (n : ℕ) →
  BoundedByᶜ 1⁺ (atanhPowerSeries n)
atanhPowerSeriesCoefficientBoundOne =
  primitivePowerSeriesCoefficientBoundOne
    evenGeometricPowerSeries
    evenGeometricPowerSeriesCoefficientBoundOne


atanPowerSeriesCoefficientBoundOne :
  (n : ℕ) →
  BoundedByᶜ 1⁺ (atanPowerSeries n)
atanPowerSeriesCoefficientBoundOne =
  primitivePowerSeriesCoefficientBoundOne
    alternatingEvenGeometricPowerSeries
    alternatingEvenGeometricPowerSeriesCoefficientBoundOne


evenGeometricPowerSeriesCoefficientBounds :
  PowerSeriesCoefficientBounds evenGeometricPowerSeries
evenGeometricPowerSeriesCoefficientBounds =
  (λ _ → 1⁺) ,
  evenGeometricPowerSeriesCoefficientBoundOne


alternatingEvenGeometricPowerSeriesCoefficientBounds :
  PowerSeriesCoefficientBounds alternatingEvenGeometricPowerSeries
alternatingEvenGeometricPowerSeriesCoefficientBounds =
  (λ _ → 1⁺) ,
  alternatingEvenGeometricPowerSeriesCoefficientBoundOne


atanhPowerSeriesCoefficientBounds :
  PowerSeriesCoefficientBounds atanhPowerSeries
atanhPowerSeriesCoefficientBounds =
  (λ _ → 1⁺) ,
  atanhPowerSeriesCoefficientBoundOne


atanPowerSeriesCoefficientBounds :
  PowerSeriesCoefficientBounds atanPowerSeries
atanPowerSeriesCoefficientBounds =
  (λ _ → 1⁺) ,
  atanPowerSeriesCoefficientBoundOne


atanhPowerSeriesIteratedFormalPartialDerivativeBounds :
  (σ : ℚ⁺) →
  {x : ℝᶜ} →
  BoundedByᶜ σ x →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    atanhPowerSeries
    x
    (λ s n →
      positivePartialSum
        (λ k →
          scalar-bound (Rational.natMul (suc k) Rational.1ℚ) *⁺
          1⁺ *⁺
          positivePower σ k)
        n)
atanhPowerSeriesIteratedFormalPartialDerivativeBounds σ x-bound =
  powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
    σ
    x-bound
    (λ _ → 1⁺)
    atanhPowerSeriesCoefficientBoundOne


atanPowerSeriesIteratedFormalPartialDerivativeBounds :
  (σ : ℚ⁺) →
  {x : ℝᶜ} →
  BoundedByᶜ σ x →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    atanPowerSeries
    x
    (λ s n →
      positivePartialSum
        (λ k →
          scalar-bound (Rational.natMul (suc k) Rational.1ℚ) *⁺
          1⁺ *⁺
          positivePower σ k)
        n)
atanPowerSeriesIteratedFormalPartialDerivativeBounds σ x-bound =
  powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
    σ
    x-bound
    (λ _ → 1⁺)
    atanPowerSeriesCoefficientBoundOne
