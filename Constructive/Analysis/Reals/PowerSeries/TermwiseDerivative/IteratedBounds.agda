{-

Part of Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.IteratedBounds where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; max ; suc ; zero)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.Calculus.Derivative.Base
open import Constructive.Analysis.Reals.Calculus.Derivative.Rules
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.CommRing
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base using (_≤ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.Series
  using
    ( partialSum
    ; partialSum-add
    ; seriesSumFromFiniteTailBoundConvergesAt
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower ; realPowerBoundsFromBound)
open import Constructive.Analysis.GeometricDecay
  using (positivePower)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( addPowerSeries
    ; addPowerSeriesTerm
    ; bounded-byᶜ-zero
    ; powerSeriesPartialSum-add
    ; powerSeriesPartialSum-shift
    ; shiftPowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Core
  using
    ( HasPowerSeriesAtWith
    ; centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using
    ( derivativePowerSeries
    ; derivativePrimitivePowerSeries
    ; naturalReal
    ; primitivePowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence
  using (derivativePrimitivePowerSeriesInfiniteRadius)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open ClosenessOf RationalsMetricSpace

open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Internal
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Index
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Finite
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.PartialSums

iteratedShiftPowerSeries :
  ℕ →
  PowerSeries →
  PowerSeries
iteratedShiftPowerSeries zero a =
  a
iteratedShiftPowerSeries (suc n) a =
  shiftPowerSeries (iteratedShiftPowerSeries n a)


iteratedShiftPowerSeries-index :
  (s : ℕ) →
  (a : PowerSeries) →
  (n : ℕ) →
  iteratedShiftPowerSeries s a n ≡ a (s Nat.+ n)
iteratedShiftPowerSeries-index zero a n =
  refl
iteratedShiftPowerSeries-index (suc s) a n =
  iteratedShiftPowerSeries-index s a (suc n) ∙
  cong a (Nat.+-suc s n)


iteratedShiftPowerSeriesCoefficientBounds :
  {a : PowerSeries} →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  (s n : ℕ) →
  BoundedByᶜ
    (κ (s Nat.+ n))
    (iteratedShiftPowerSeries s a n)
iteratedShiftPowerSeriesCoefficientBounds {a = a} κ coefficientBounds s n =
  subst
    (BoundedByᶜ (κ (s Nat.+ n)))
    (sym (iteratedShiftPowerSeries-index s a n))
    (coefficientBounds (s Nat.+ n))


naturalRealBound :
  (n : ℕ) →
  BoundedByᶜ
    (scalar-bound (Rational.natMul n Rational.1ℚ))
    (naturalReal n)
naturalRealBound n =
  rational-bound→boundedᶜ
    (scalar-bound natural)
    natural
    (scalar-bound-rational-boundᶜ natural)
  where
  natural : ℚ
  natural =
    Rational.natMul n Rational.1ℚ


iteratedShiftDerivativePowerSeriesCoefficientBounds :
  {a : PowerSeries} →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  (s n : ℕ) →
  BoundedByᶜ
    (scalar-bound (Rational.natMul (suc n) Rational.1ℚ) *⁺
      κ (s Nat.+ suc n))
    (derivativePowerSeries (iteratedShiftPowerSeries s a) n)
iteratedShiftDerivativePowerSeriesCoefficientBounds {a = a}
    κ coefficientBounds s n =
  bounded-byᶜ-mul
    (scalar-bound natural)
    (κ (s Nat.+ suc n))
    (naturalReal (suc n))
    (iteratedShiftPowerSeries s a (suc n))
    (naturalRealBound (suc n))
    (iteratedShiftPowerSeriesCoefficientBounds κ coefficientBounds s (suc n))
  where
  natural : ℚ
  natural =
    Rational.natMul (suc n) Rational.1ℚ


PowerSeriesIteratedFormalPartialDerivativeBounds :
  PowerSeries →
  ℝᶜ →
  (ℕ → ℕ → ℚ⁺) →
  Type₀
PowerSeriesIteratedFormalPartialDerivativeBounds a x δ =
  (s n : ℕ) →
  BoundedByᶜ
    (δ s n)
    (powerSeriesPartialSum
      (derivativePowerSeries (iteratedShiftPowerSeries s a))
      x
      n)


positivePartialSum :
  (ℕ → ℚ⁺) →
  ℕ →
  ℚ⁺
positivePartialSum κ zero =
  1⁺
positivePartialSum κ (suc n) =
  κ zero +⁺ positivePartialSum (λ k → κ (suc k)) n


partialSumBoundFromTermBounds :
  (u : ℕ → ℝᶜ) →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (u n)) →
  (n : ℕ) →
  BoundedByᶜ (positivePartialSum κ n) (partialSum u n)
partialSumBoundFromTermBounds u κ termBounds zero =
  bounded-byᶜ-zero 1⁺
partialSumBoundFromTermBounds u κ termBounds (suc n) =
  bounded-byᶜ-add
    (κ zero)
    (positivePartialSum (λ k → κ (suc k)) n)
    (u zero)
    (partialSum (λ k → u (suc k)) n)
    (termBounds zero)
    (partialSumBoundFromTermBounds
      (λ k → u (suc k))
      (λ k → κ (suc k))
      (λ k → termBounds (suc k))
      n)


powerSeriesPartialSumBoundFromTermBounds :
  (a : PowerSeries) →
  (x : ℝᶜ) →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (powerSeriesTerm a x n)) →
  (n : ℕ) →
  BoundedByᶜ
    (positivePartialSum κ n)
    (powerSeriesPartialSum a x n)
powerSeriesPartialSumBoundFromTermBounds a x κ termBounds =
  partialSumBoundFromTermBounds (powerSeriesTerm a x) κ termBounds


powerSeriesIteratedFormalPartialDerivativeBoundsFromTermBounds :
  {a : PowerSeries} →
  {x : ℝᶜ} →
  (κ : ℕ → ℕ → ℚ⁺) →
  ((s n : ℕ) →
    BoundedByᶜ
      (κ s n)
      (powerSeriesTerm
        (derivativePowerSeries (iteratedShiftPowerSeries s a))
        x
        n)) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    a
    x
    (λ s n → positivePartialSum (κ s) n)
powerSeriesIteratedFormalPartialDerivativeBoundsFromTermBounds
  {a = a}
  {x = x}
  κ
  termBounds
  s =
  powerSeriesPartialSumBoundFromTermBounds
    (derivativePowerSeries (iteratedShiftPowerSeries s a))
    x
    (κ s)
    (termBounds s)


powerSeriesIteratedFormalPartialDerivativeBoundsFromCoefficientBounds :
  (σ : ℚ⁺) →
  {a : PowerSeries} →
  {x : ℝᶜ} →
  BoundedByᶜ σ x →
  (κ : ℕ → ℕ → ℚ⁺) →
  ((s n : ℕ) →
    BoundedByᶜ
      (κ s n)
      (derivativePowerSeries (iteratedShiftPowerSeries s a) n)) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    a
    x
    (λ s n → positivePartialSum (λ k → κ s k *⁺ positivePower σ k) n)
powerSeriesIteratedFormalPartialDerivativeBoundsFromCoefficientBounds
  σ
  {a = a}
  {x = x}
  x-bound
  κ
  coefficientBounds =
  powerSeriesIteratedFormalPartialDerivativeBoundsFromTermBounds
    (λ s n → κ s n *⁺ positivePower σ n)
    termBounds
  where
  termBounds :
    (s n : ℕ) →
    BoundedByᶜ
      (κ s n *⁺ positivePower σ n)
      (powerSeriesTerm
        (derivativePowerSeries (iteratedShiftPowerSeries s a))
        x
        n)
  termBounds s n =
    bounded-byᶜ-mul
      (κ s n)
      (positivePower σ n)
      (derivativePowerSeries (iteratedShiftPowerSeries s a) n)
      (realPower x n)
      (coefficientBounds s n)
      (realPowerBoundsFromBound σ x x-bound n)


powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds :
  (σ : ℚ⁺) →
  (κ : ℕ → ℚ⁺) →
  ℕ →
  ℕ →
  ℚ⁺
powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds σ κ s n =
  positivePartialSum
    (λ k →
      scalar-bound (Rational.natMul (suc k) Rational.1ℚ) *⁺
      κ (s Nat.+ suc k) *⁺
      positivePower σ k)
    n


powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds :
  (σ : ℚ⁺) →
  {a : PowerSeries} →
  {x : ℝᶜ} →
  BoundedByᶜ σ x →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    a
    x
    (powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds σ κ)
powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
  σ
  {a = a}
  {x = x}
  x-bound
  κ
  coefficientBounds =
  powerSeriesIteratedFormalPartialDerivativeBoundsFromCoefficientBounds
    σ
    x-bound
    (λ s n →
      scalar-bound (Rational.natMul (suc n) Rational.1ℚ) *⁺
      κ (s Nat.+ suc n))
    (iteratedShiftDerivativePowerSeriesCoefficientBounds κ coefficientBounds)


powerSeriesIteratedFormalPartialSumsDerivativeModulus :
  ℚ⁺ →
  (ℕ → ℕ → ℚ⁺) →
  ℕ →
  ℕ →
  PrecisionModulus
powerSeriesIteratedFormalPartialSumsDerivativeModulus σ δ zero s =
  λ _ → 1⁺
powerSeriesIteratedFormalPartialSumsDerivativeModulus σ δ (suc n) s =
  powerSeriesPartialSumShiftDerivativeStepModulus
    σ
    (δ (suc s) n)
    (powerSeriesIteratedFormalPartialSumsDerivativeModulus σ δ n (suc s))


powerSeriesFormalPartialSumsDerivativeModulus :
  ℚ⁺ →
  (ℕ → ℕ → ℚ⁺) →
  ℕ →
  PrecisionModulus
powerSeriesFormalPartialSumsDerivativeModulus σ δ n =
  powerSeriesIteratedFormalPartialSumsDerivativeModulus σ δ n zero


powerSeriesIteratedFormalPartialSumsHaveDerivativeWithFromBounds :
  (σ : ℚ⁺) →
  {a : PowerSeries} →
  {x : ℝᶜ} →
  {δ : ℕ → ℕ → ℚ⁺} →
  BoundedByᶜ σ x →
  PowerSeriesIteratedFormalPartialDerivativeBounds a x δ →
  (n s : ℕ) →
  HasDerivativeAtWith
    (λ y →
      powerSeriesPartialSum (iteratedShiftPowerSeries s a) y (suc n))
    x
    (powerSeriesPartialSum
      (derivativePowerSeries (iteratedShiftPowerSeries s a))
      x
      n)
    (powerSeriesIteratedFormalPartialSumsDerivativeModulus σ δ n s)
powerSeriesIteratedFormalPartialSumsHaveDerivativeWithFromBounds
  σ
  {a = a}
  {x = x}
  {δ = δ}
  x-bound
  derivative-bounds
  zero
  s =
  powerSeriesConstantPartialSumHasDerivativeAtWith
powerSeriesIteratedFormalPartialSumsHaveDerivativeWithFromBounds
  σ
  {a = a}
  {x = x}
  {δ = δ}
  x-bound
  derivative-bounds
  (suc n)
  s =
  powerSeriesPartialSumShiftDerivativeStepAtWith
    σ
    (δ (suc s) n)
    x-bound
    (derivative-bounds (suc s) n)
    (powerSeriesIteratedFormalPartialSumsHaveDerivativeWithFromBounds
      σ
      x-bound
      derivative-bounds
      n
      (suc s))
    (powerSeriesFormalDerivativePartialSum-step-value
      (iteratedShiftPowerSeries s a)
      x
      n)


powerSeriesFormalPartialSumsHaveDerivativeWithFromIteratedBounds :
  (σ : ℚ⁺) →
  {a : PowerSeries} →
  {x : ℝᶜ} →
  {δ : ℕ → ℕ → ℚ⁺} →
  BoundedByᶜ σ x →
  PowerSeriesIteratedFormalPartialDerivativeBounds a x δ →
  PowerSeriesFormalPartialSumsHaveDerivativeWith
    a
    x
    (powerSeriesFormalPartialSumsDerivativeModulus σ δ)
powerSeriesFormalPartialSumsHaveDerivativeWithFromIteratedBounds
  σ
  x-bound
  derivative-bounds
  n =
  powerSeriesIteratedFormalPartialSumsHaveDerivativeWithFromBounds
    σ
    x-bound
    derivative-bounds
    n
    zero


powerSeriesPartialDerivativeRemainderBoundFromPartialSumsDerivative :
  {a da : PowerSeries} →
  {x : ℝᶜ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  {ω : ℕ → PrecisionModulus} →
  PowerSeriesPartialSumsHaveDerivativeWith a da x ω →
  PowerSeriesPartialSumsDerivativeModulusLarge χ μ ω →
  PowerSeriesPartialDerivativeRemainderBoundWith a da x χ μ
powerSeriesPartialDerivativeRemainderBoundFromPartialSumsDerivative
  {a = a}
  {da = da}
  {x = x}
  {χ = χ}
  {ω = ω}
  partialDerivative
  modulus-large
  ε
  η
  η≤με
  h
  h-bound =
  subst
    (λ κ →
      BoundedByᶜ
        κ
        (powerSeriesTermwisePartialRemainder a da x χ ε η h))
    (quarter-product≡ ε η)
    (partialDerivative n (quarter⁺ ε) η η≤ω h h-bound)
  where
  n : ℕ
  n =
    χ ε η

  η≤ω : radius η ℚOrder.≤ radius ((ω n) (quarter⁺ ε))
  η≤ω =
    modulus-large ε η η≤με


powerSeriesFormalPartialDerivativeRemainderBoundFromPartialSumsDerivative :
  {a : PowerSeries} →
  {x : ℝᶜ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  {ω : ℕ → PrecisionModulus} →
  PowerSeriesFormalPartialSumsHaveDerivativeWith a x ω →
  PowerSeriesPartialSumsDerivativeModulusLarge χ μ ω →
  PowerSeriesPartialDerivativeRemainderBoundWith
    a
    (derivativePowerSeries a)
    x
    χ
    μ
powerSeriesFormalPartialDerivativeRemainderBoundFromPartialSumsDerivative =
  powerSeriesPartialDerivativeRemainderBoundFromPartialSumsDerivative


powerSeriesFormalPartialDerivativeRemainderBoundFromIteratedBounds :
  (σ : ℚ⁺) →
  {a : PowerSeries} →
  {x : ℝᶜ} →
  {δ : ℕ → ℕ → ℚ⁺} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  BoundedByᶜ σ x →
  PowerSeriesIteratedFormalPartialDerivativeBounds a x δ →
  PowerSeriesPartialSumsDerivativeModulusLarge
    χ
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus σ δ) →
  PowerSeriesPartialDerivativeRemainderBoundWith
    a
    (derivativePowerSeries a)
    x
    χ
    μ
powerSeriesFormalPartialDerivativeRemainderBoundFromIteratedBounds
  σ
  x-bound
  derivative-bounds
  partialModulus-large =
  powerSeriesFormalPartialDerivativeRemainderBoundFromPartialSumsDerivative
    (powerSeriesFormalPartialSumsHaveDerivativeWithFromIteratedBounds
      σ
      x-bound
      derivative-bounds)
    partialModulus-large
