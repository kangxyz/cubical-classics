{-

Part of Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.PartialSums where

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
open import Constructive.Analysis.Reals.Calculus.Derivative
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
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
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
open import Constructive.Analysis.Reals.PowerSeries.Analytic
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
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Rules

powerSeriesPartialSumShiftDerivativeStepModulus :
  ℚ⁺ →
  ℚ⁺ →
  PrecisionModulus →
  PrecisionModulus
powerSeriesPartialSumShiftDerivativeStepModulus σ δ μ ε =
  min⁺
    (identityProductDerivativeModulus σ δ μ (half⁺ ε))
    (identityProductDerivativeModulus σ δ μ (half⁺ ε))


powerSeriesPartialSumShiftDerivativeStepAtWith :
  (σ δ : ℚ⁺) →
  {a da : PowerSeries} →
  {x d : ℝᶜ} →
  {n : ℕ} →
  {μ : PrecisionModulus} →
  BoundedByᶜ σ x →
  BoundedByᶜ δ d →
  HasDerivativeAtWith
    (λ y → powerSeriesPartialSum (shiftPowerSeries a) y n)
    x
    d
    μ →
  powerSeriesPartialSum da x n ≡
  powerSeriesPartialSum (shiftPowerSeries a) x n +ᶜ x ·ᶜ d →
  HasDerivativeAtWith
    (λ y → powerSeriesPartialSum a y (suc n))
    x
    (powerSeriesPartialSum da x n)
    (powerSeriesPartialSumShiftDerivativeStepModulus σ δ μ)
powerSeriesPartialSumShiftDerivativeStepAtWith
  σ
  δ
  {a = a}
  {da = da}
  {x = x}
  {d = d}
  {n = n}
  {μ = μ}
  x-bound
  d-bound
  shiftedDerivative
  derivativeValuePath =
  hasDerivativeAtWith-cong
    (λ y → sym (powerSeriesPartialSum-shift a y n))
    derivative-path
    sumDerivative
  where
  shiftedPartialSum : ℝᶜ → ℝᶜ
  shiftedPartialSum y =
    powerSeriesPartialSum (shiftPowerSeries a) y n

  productDerivativeValue : ℝᶜ
  productDerivativeValue =
    shiftedPartialSum x +ᶜ x ·ᶜ d

  productDerivative :
    HasDerivativeAtWith
      (λ y → y ·ᶜ shiftedPartialSum y)
      x
      productDerivativeValue
      (identityProductDerivativeModulus σ δ μ)
  productDerivative =
    derivativeIdentityMulAtWith
      σ
      δ
      x-bound
      d-bound
      shiftedDerivative

  constantDerivative :
    HasDerivativeAtWith
      (λ _ → a zero)
      x
      0ᶜ
      (identityProductDerivativeModulus σ δ μ)
  constantDerivative =
    derivativeConstantAtWith

  sumDerivative :
    HasDerivativeAtWith
      (λ y → a zero +ᶜ y ·ᶜ shiftedPartialSum y)
      x
      (0ᶜ +ᶜ productDerivativeValue)
      (powerSeriesPartialSumShiftDerivativeStepModulus σ δ μ)
  sumDerivative =
    derivativeAddAtWith constantDerivative productDerivative

  derivative-path :
    0ᶜ +ᶜ productDerivativeValue ≡
    powerSeriesPartialSum da x n
  derivative-path =
    add-zero-left productDerivativeValue ∙
    sym derivativeValuePath


powerSeriesTermwiseDecomposedRemainder :
  (ℝᶜ → ℝᶜ) →
  PowerSeries →
  PowerSeries →
  ℝᶜ →
  ℝᶜ →
  TermwiseDerivativeIndex →
  ℚ⁺ →
  ℚ⁺ →
  ℝᶜ →
  ℝᶜ
powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h =
  ((((f (x +ᶜ h) +ᶜ
      (-ᶜ powerSeriesPartialSum a (x +ᶜ h) (suc n))) +ᶜ
      linearRemainder
        (λ y → powerSeriesPartialSum a y (suc n))
        x
        (powerSeriesPartialSum da x n)
        h) +ᶜ
      (powerSeriesPartialSum a x (suc n) +ᶜ (-ᶜ f x))) +ᶜ
      (-ᶜ
        ((d +ᶜ (-ᶜ powerSeriesPartialSum da x n)) ·ᶜ h)))
  where
  n : ℕ
  n =
    χ ε η


powerSeriesTermwiseRemainderDecomposition :
  (f : ℝᶜ → ℝᶜ) →
  (a da : PowerSeries) →
  (x d : ℝᶜ) →
  (χ : TermwiseDerivativeIndex) →
  (ε η : ℚ⁺) →
  (h : ℝᶜ) →
  linearRemainder f x d h ≡
  powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h
powerSeriesTermwiseRemainderDecomposition f a da x d χ ε η h =
  SolverHelpers.linear-remainder-decomposition
    CauchyRealsCommRing
    (f (x +ᶜ h))
    (f x)
    (powerSeriesPartialSum a (x +ᶜ h) (suc n))
    (powerSeriesPartialSum a x (suc n))
    d
    (powerSeriesPartialSum da x n)
    h
  where
  n : ℕ
  n =
    χ ε η


powerSeriesTermwiseForwardError :
  (ℝᶜ → ℝᶜ) →
  PowerSeries →
  ℝᶜ →
  TermwiseDerivativeIndex →
  ℚ⁺ →
  ℚ⁺ →
  ℝᶜ →
  ℝᶜ
powerSeriesTermwiseForwardError f a x χ ε η h =
  f (x +ᶜ h) +ᶜ
  (-ᶜ powerSeriesPartialSum a (x +ᶜ h) (suc (χ ε η)))


powerSeriesTermwisePartialRemainder :
  PowerSeries →
  PowerSeries →
  ℝᶜ →
  TermwiseDerivativeIndex →
  ℚ⁺ →
  ℚ⁺ →
  ℝᶜ →
  ℝᶜ
powerSeriesTermwisePartialRemainder a da x χ ε η h =
  linearRemainder
    (λ y → powerSeriesPartialSum a y (suc (χ ε η)))
    x
    (powerSeriesPartialSum da x (χ ε η))
    h


powerSeriesTermwiseCenterError :
  (ℝᶜ → ℝᶜ) →
  PowerSeries →
  ℝᶜ →
  TermwiseDerivativeIndex →
  ℚ⁺ →
  ℚ⁺ →
  ℝᶜ
powerSeriesTermwiseCenterError f a x χ ε η =
  powerSeriesPartialSum a x (suc (χ ε η)) +ᶜ (-ᶜ f x)


powerSeriesTermwiseDerivativeLinearError :
  PowerSeries →
  ℝᶜ →
  ℝᶜ →
  TermwiseDerivativeIndex →
  ℚ⁺ →
  ℚ⁺ →
  ℝᶜ →
  ℝᶜ
powerSeriesTermwiseDerivativeLinearError da x d χ ε η h =
  -ᶜ ((d +ᶜ (-ᶜ powerSeriesPartialSum da x (χ ε η))) ·ᶜ h)


PowerSeriesTermwiseDerivativeAtWith :
  (f : ℝᶜ → ℝᶜ) →
  PowerSeries →
  PowerSeries →
  (x d : ℝᶜ) →
  TermwiseDerivativeIndex →
  PrecisionModulus →
  Type₀
PowerSeriesTermwiseDerivativeAtWith f a da x d χ μ =
  Σ[ remainderDecomposition ∈
      ((ε η : ℚ⁺) →
      radius η ℚOrder.≤ radius (μ ε) →
      (h : ℝᶜ) →
      BoundedByᶜ η h →
      linearRemainder f x d h ≡
      powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h) ]
    ((ε η : ℚ⁺) →
      radius η ℚOrder.≤ radius (μ ε) →
      (h : ℝᶜ) →
      BoundedByᶜ η h →
      BoundedByᶜ
        (ε *⁺ η)
        (powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h))


module PowerSeriesTermwiseDerivativeAtWith where
  remainderDecomposition :
    {f : ℝᶜ → ℝᶜ} →
    {a : PowerSeries} →
    {da : PowerSeries} →
    {x d : ℝᶜ} →
    {χ : TermwiseDerivativeIndex} →
    {μ : PrecisionModulus} →
    PowerSeriesTermwiseDerivativeAtWith f a da x d χ μ →
    (ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (μ ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    linearRemainder f x d h ≡
    powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h
  remainderDecomposition derivativeData =
    derivativeData .fst

  decomposedRemainderBound :
    {f : ℝᶜ → ℝᶜ} →
    {a : PowerSeries} →
    {da : PowerSeries} →
    {x d : ℝᶜ} →
    {χ : TermwiseDerivativeIndex} →
    {μ : PrecisionModulus} →
    PowerSeriesTermwiseDerivativeAtWith f a da x d χ μ →
    (ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (μ ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    BoundedByᶜ
      (ε *⁺ η)
      (powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h)
  decomposedRemainderBound derivativeData =
    derivativeData .snd


PowerSeriesTermwiseForwardErrorBoundWith :
  (ℝᶜ → ℝᶜ) →
  PowerSeries →
  ℝᶜ →
  TermwiseDerivativeIndex →
  PrecisionModulus →
  Type₀
PowerSeriesTermwiseForwardErrorBoundWith f a x χ μ =
  (ε η : ℚ⁺) →
  radius η ℚOrder.≤ radius (μ ε) →
  (h : ℝᶜ) →
  BoundedByᶜ η h →
  BoundedByᶜ
    (quarter⁺ (ε *⁺ η))
    (powerSeriesTermwiseForwardError f a x χ ε η h)


PowerSeriesPartialDerivativeRemainderBoundWith :
  PowerSeries →
  PowerSeries →
  ℝᶜ →
  TermwiseDerivativeIndex →
  PrecisionModulus →
  Type₀
PowerSeriesPartialDerivativeRemainderBoundWith a da x χ μ =
  (ε η : ℚ⁺) →
  radius η ℚOrder.≤ radius (μ ε) →
  (h : ℝᶜ) →
  BoundedByᶜ η h →
  BoundedByᶜ
    (quarter⁺ (ε *⁺ η))
    (powerSeriesTermwisePartialRemainder a da x χ ε η h)


PowerSeriesPartialSumsDerivativeModulusLarge :
  TermwiseDerivativeIndex →
  PrecisionModulus →
  (ℕ → PrecisionModulus) →
  Type₀
PowerSeriesPartialSumsDerivativeModulusLarge χ μ ω =
  (ε η : ℚ⁺) →
  radius η ℚOrder.≤ radius (μ ε) →
  radius η ℚOrder.≤ radius (ω (χ ε η) (quarter⁺ ε))


PowerSeriesPartialSumsHaveDerivativeWith :
  PowerSeries →
  PowerSeries →
  ℝᶜ →
  (ℕ → PrecisionModulus) →
  Type₀
PowerSeriesPartialSumsHaveDerivativeWith a da x ω =
  (n : ℕ) →
  HasDerivativeAtWith
    (λ y → powerSeriesPartialSum a y (suc n))
    x
    (powerSeriesPartialSum da x n)
    (ω n)


PowerSeriesFormalPartialSumsHaveDerivativeWith :
  PowerSeries →
  ℝᶜ →
  (ℕ → PrecisionModulus) →
  Type₀
PowerSeriesFormalPartialSumsHaveDerivativeWith a =
  PowerSeriesPartialSumsHaveDerivativeWith a (derivativePowerSeries a)
