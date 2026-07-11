{-

One-dimensional derivative data for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Calculus.DerivativeData where

open import Cubical.Foundations.Prelude

import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.CauchyReals.Metric
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.Interval.Base
open import Constructive.Data.PositiveRationals


linearRemainder :
  (f : ℝᶜ → ℝᶜ) →
  (x d h : ℝᶜ) →
  ℝᶜ
linearRemainder f x d h =
  (f (x +ᶜ h) +ᶜ (-ᶜ f x)) +ᶜ (-ᶜ (d ·ᶜ h))


HasDerivativeAtWith :
  (f : ℝᶜ → ℝᶜ) →
  (x d : ℝᶜ) →
  PrecisionModulus →
  Type₀
HasDerivativeAtWith f x d μ =
  (ε η : ℚ⁺) →
  radius η ℚOrder.≤ radius (μ ε) →
  (h : ℝᶜ) →
  BoundedByᶜ η h →
  BoundedByᶜ (ε *⁺ η) (linearRemainder f x d h)


module HasDerivativeAtWith where
  remainderBound :
    {f : ℝᶜ → ℝᶜ} {x d : ℝᶜ} {μ : PrecisionModulus} →
    HasDerivativeAtWith f x d μ →
    (ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (μ ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    BoundedByᶜ (ε *⁺ η) (linearRemainder f x d h)
  remainderBound derivative =
    derivative


private
  linearRemainder-local-path :
    {f g : ℝᶜ → ℝᶜ} →
    {x d h : ℝᶜ} →
    f x ≡ g x →
    f (x +ᶜ h) ≡ g (x +ᶜ h) →
    linearRemainder f x d h ≡ linearRemainder g x d h
  linearRemainder-local-path {d = d} {h = h} basePath forwardPath =
    cong₂
      (λ forward base → (forward +ᶜ (-ᶜ base)) +ᶜ (-ᶜ (d ·ᶜ h)))
      forwardPath
      basePath


hasDerivativeAtWith-local-cong :
  {f g : ℝᶜ → ℝᶜ} →
  {x d : ℝᶜ} →
  {μ : PrecisionModulus} →
  f x ≡ g x →
  ((ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (μ ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    f (x +ᶜ h) ≡ g (x +ᶜ h)) →
  HasDerivativeAtWith g x d μ →
  HasDerivativeAtWith f x d μ
hasDerivativeAtWith-local-cong
  {f = f}
  {g = g}
  {x = x}
  {d = d}
  basePath
  forwardPath
  derivative
  ε
  η
  η≤με
  h
  h-bound =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (sym
      (linearRemainder-local-path
        {f = f}
        {g = g}
        {x = x}
        {d = d}
        {h = h}
        basePath
        (forwardPath ε η η≤με h h-bound)))
    (derivative ε η η≤με h h-bound)


HasDerivativeAt :
  (ℝᶜ → ℝᶜ) →
  ℝᶜ →
  ℝᶜ →
  Type₀
HasDerivativeAt f x d =
  Σ[ μ ∈ PrecisionModulus ] HasDerivativeAtWith f x d μ


DifferentiableAt :
  (ℝᶜ → ℝᶜ) →
  ℝᶜ →
  Type₀
DifferentiableAt f x =
  Σ[ d ∈ ℝᶜ ] HasDerivativeAt f x d
