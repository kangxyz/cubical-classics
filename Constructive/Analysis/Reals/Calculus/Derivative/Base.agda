{-

One-dimensional derivative data for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Calculus.Derivative.Base where

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
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
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


intervalIncrement :
  (a b : ℝᶜ) →
  [ a , b ]ᶜ →
  [ a , b ]ᶜ →
  ℝᶜ
intervalIncrement a b x y =
  pointᶜ {a = a} {b = b} y +ᶜ
  (-ᶜ pointᶜ {a = a} {b = b} x)


intervalLinearRemainder :
  (a b : ℝᶜ) →
  (f : [ a , b ]ᶜ → ℝᶜ) →
  (x y : [ a , b ]ᶜ) →
  (d : ℝᶜ) →
  ℝᶜ
intervalLinearRemainder a b f x y d =
  (f y +ᶜ (-ᶜ f x)) +ᶜ
  (-ᶜ (d ·ᶜ intervalIncrement a b x y))


HasDerivativeWithinAtWith :
  (a b : ℝᶜ) →
  ([ a , b ]ᶜ → ℝᶜ) →
  [ a , b ]ᶜ →
  ℝᶜ →
  PrecisionModulus →
  Type₀
HasDerivativeWithinAtWith a b f x d μ =
  (ε η : ℚ⁺) →
  radius η ℚOrder.≤ radius (μ ε) →
  (y : [ a , b ]ᶜ) →
  MetricSpace.Close (IntervalMetric a b) x η y →
  BoundedByᶜ (ε *⁺ η) (intervalLinearRemainder a b f x y d)


module HasDerivativeWithinAtWith where
  remainderBound :
    {a b : ℝᶜ} {f : [ a , b ]ᶜ → ℝᶜ}
    {x : [ a , b ]ᶜ} {d : ℝᶜ} {μ : PrecisionModulus} →
    HasDerivativeWithinAtWith a b f x d μ →
    (ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (μ ε) →
    (y : [ a , b ]ᶜ) →
    MetricSpace.Close (IntervalMetric a b) x η y →
    BoundedByᶜ (ε *⁺ η) (intervalLinearRemainder a b f x y d)
  remainderBound derivative =
    derivative


HasDerivativeWithinAt :
  {a b : ℝᶜ} →
  ([ a , b ]ᶜ → ℝᶜ) →
  [ a , b ]ᶜ →
  ℝᶜ →
  Type₀
HasDerivativeWithinAt {a = a} {b = b} f x d =
  Σ[ μ ∈ PrecisionModulus ]
    HasDerivativeWithinAtWith a b f x d μ


DifferentiableWithinAt :
  {a b : ℝᶜ} →
  ([ a , b ]ᶜ → ℝᶜ) →
  [ a , b ]ᶜ →
  Type₀
DifferentiableWithinAt {a = a} {b = b} f x =
  Σ[ d ∈ ℝᶜ ] HasDerivativeWithinAt {a = a} {b = b} f x d


HasDerivativeOnIntervalWith :
  {a b : ℝᶜ} →
  (f f' : [ a , b ]ᶜ → ℝᶜ) →
  PrecisionModulus →
  Type₀
HasDerivativeOnIntervalWith {a = a} {b = b} f f' μ =
  (x : [ a , b ]ᶜ) →
  HasDerivativeWithinAtWith a b f x (f' x) μ


HasDerivativeOnInterval :
  {a b : ℝᶜ} →
  (f f' : [ a , b ]ᶜ → ℝᶜ) →
  Type₀
HasDerivativeOnInterval {a = a} {b = b} f f' =
  Σ[ μ ∈ PrecisionModulus ]
    HasDerivativeOnIntervalWith {a = a} {b = b} f f' μ


DifferentiableOnInterval :
  {a b : ℝᶜ} →
  ([ a , b ]ᶜ → ℝᶜ) →
  Type₀
DifferentiableOnInterval {a = a} {b = b} f =
  Σ[ f' ∈ ([ a , b ]ᶜ → ℝᶜ) ]
    HasDerivativeOnInterval {a = a} {b = b} f f'
