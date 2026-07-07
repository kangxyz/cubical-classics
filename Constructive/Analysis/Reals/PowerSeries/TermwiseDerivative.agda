{-

Termwise derivative criterion for power-series sums

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)

open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.Derivative
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Data.PositiveRationals


private
  four-quarter-sum≡ :
    (ε : ℚ⁺) →
    (quarter⁺ ε +⁺ quarter⁺ ε) +⁺
      (quarter⁺ ε +⁺ quarter⁺ ε)
    ≡ ε
  four-quarter-sum≡ ε =
    cong₂
      _+⁺_
      (ℚ⁺Path (quarter-sum≡half ε))
      (ℚ⁺Path (quarter-sum≡half ε)) ∙
    half⁺+half⁺≡ ε

  four-quarters≡ :
    (ε : ℚ⁺) →
    ((quarter⁺ ε +⁺ quarter⁺ ε) +⁺ quarter⁺ ε) +⁺ quarter⁺ ε
    ≡ ε
  four-quarters≡ ε =
    +⁺-assoc
      (quarter⁺ ε +⁺ quarter⁺ ε)
      (quarter⁺ ε)
      (quarter⁺ ε) ∙
    four-quarter-sum≡ ε


TermwiseDerivativeIndex : Type₀
TermwiseDerivativeIndex =
  ℚ⁺ → ℚ⁺ → ℕ


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
      (-ᶜ powerSeriesPartialSum a (x +ᶜ h) n)) +ᶜ
      linearRemainder
        (λ y → powerSeriesPartialSum a y n)
        x
        (powerSeriesPartialSum da x n)
        h) +ᶜ
      (powerSeriesPartialSum a x n +ᶜ (-ᶜ f x))) +ᶜ
      (-ᶜ
        ((d +ᶜ (-ᶜ powerSeriesPartialSum da x n)) ·ᶜ h)))
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
  (-ᶜ powerSeriesPartialSum a (x +ᶜ h) (χ ε η))


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
    (λ y → powerSeriesPartialSum a y (χ ε η))
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
  powerSeriesPartialSum a x (χ ε η) +ᶜ (-ᶜ f x)


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


record PowerSeriesTermwiseDerivativePiecesAtWith
    (f : ℝᶜ → ℝᶜ)
    (a da : PowerSeries)
    (x d : ℝᶜ)
    (χ : TermwiseDerivativeIndex)
    (μ : PrecisionModulus) :
    Type₀ where
  no-eta-equality

  field
    remainderDecomposition :
      (ε η : ℚ⁺) →
      radius η ℚOrder.≤ radius (μ ε) →
      (h : ℝᶜ) →
      BoundedByᶜ η h →
      linearRemainder f x d h ≡
      powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h

    forwardSumError :
      (ε η : ℚ⁺) →
      radius η ℚOrder.≤ radius (μ ε) →
      (h : ℝᶜ) →
      BoundedByᶜ η h →
      BoundedByᶜ
        (quarter⁺ (ε *⁺ η))
        (powerSeriesTermwiseForwardError f a x χ ε η h)

    partialDerivativeRemainder :
      (ε η : ℚ⁺) →
      radius η ℚOrder.≤ radius (μ ε) →
      (h : ℝᶜ) →
      BoundedByᶜ η h →
      BoundedByᶜ
        (quarter⁺ (ε *⁺ η))
        (powerSeriesTermwisePartialRemainder a da x χ ε η h)

    centerSumError :
      (ε η : ℚ⁺) →
      radius η ℚOrder.≤ radius (μ ε) →
      (h : ℝᶜ) →
      BoundedByᶜ η h →
      BoundedByᶜ
        (quarter⁺ (ε *⁺ η))
        (powerSeriesTermwiseCenterError f a x χ ε η)

    derivativeLinearError :
      (ε η : ℚ⁺) →
      radius η ℚOrder.≤ radius (μ ε) →
      (h : ℝᶜ) →
      BoundedByᶜ η h →
      BoundedByᶜ
        (quarter⁺ (ε *⁺ η))
        (powerSeriesTermwiseDerivativeLinearError da x d χ ε η h)


powerSeriesTermwiseDerivativeAtWith→hasDerivativeAtWith :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {da : PowerSeries} →
  {x d : ℝᶜ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  PowerSeriesTermwiseDerivativeAtWith f a da x d χ μ →
  HasDerivativeAtWith f x d μ
powerSeriesTermwiseDerivativeAtWith→hasDerivativeAtWith
  {f = f}
  {a = a}
  {x = x}
  {d = d}
  {χ = χ}
  derivativeData
  ε
  η
  η≤με
  h
  h-bound =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (sym
      (PowerSeriesTermwiseDerivativeAtWith.remainderDecomposition
        derivativeData
        ε
        η
        η≤με
        h
        h-bound))
    (PowerSeriesTermwiseDerivativeAtWith.decomposedRemainderBound
      derivativeData
      ε
      η
      η≤με
      h
      h-bound)


PowerSeriesTermwiseDerivativeAt :
  (ℝᶜ → ℝᶜ) →
  PowerSeries →
  PowerSeries →
  ℝᶜ →
  ℝᶜ →
  Type₀
PowerSeriesTermwiseDerivativeAt f a da x d =
  Σ[ χ ∈ TermwiseDerivativeIndex ]
    Σ[ μ ∈ PrecisionModulus ]
      PowerSeriesTermwiseDerivativeAtWith f a da x d χ μ


powerSeriesTermwiseDerivativeAt→hasDerivativeAt :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {da : PowerSeries} →
  {x d : ℝᶜ} →
  PowerSeriesTermwiseDerivativeAt f a da x d →
  HasDerivativeAt f x d
powerSeriesTermwiseDerivativeAt→hasDerivativeAt (χ , μ , derivativeData) =
  μ ,
  powerSeriesTermwiseDerivativeAtWith→hasDerivativeAtWith
    {χ = χ}
    derivativeData
