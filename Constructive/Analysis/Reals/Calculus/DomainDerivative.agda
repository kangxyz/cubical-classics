{-

Derivatives of functions carrying explicit domain evidence

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Calculus.DomainDerivative where

open import Cubical.Foundations.Prelude

import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax)

open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Data.PositiveRationals


DomainValueIndependent :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  Type ℓ
DomainValueIndependent {D = D} f =
  (x : ℝᶜ) →
  (left right : D x) →
  f x left ≡ f x right


domainValueAlongPath :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  DomainValueIndependent f →
  {x y : ℝᶜ} →
  (x≡y : x ≡ y) →
  (x-domain : D x) →
  (y-domain : D y) →
  f x x-domain ≡ f y y-domain
domainValueAlongPath
  {D = D}
  {f = f}
  independent
  {x = x}
  {y = y}
  x≡y
  x-domain
  y-domain =
  subst
    (λ z → (z-domain : D z) → f x x-domain ≡ f z z-domain)
    x≡y
    (λ z-domain → independent x x-domain z-domain)
    y-domain


withinDomainLinearRemainder :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  (x : ℝᶜ) →
  D x →
  (d h : ℝᶜ) →
  D (x +ᶜ h) →
  ℝᶜ
withinDomainLinearRemainder f x x-domain d h forward-domain =
  (f (x +ᶜ h) forward-domain +ᶜ (-ᶜ f x x-domain)) +ᶜ
  (-ᶜ (d ·ᶜ h))


HasDerivativeWithinDomainAtWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  (x : ℝᶜ) →
  D x →
  ℝᶜ →
  PrecisionModulus →
  Type ℓ
HasDerivativeWithinDomainAtWith {D = D} f x x-domain d μ =
  (ε η : ℚ⁺) →
  radius η ℚOrder.≤ radius (μ ε) →
  (h : ℝᶜ) →
  BoundedByᶜ η h →
  (forward-domain : D (x +ᶜ h)) →
  BoundedByᶜ
    (ε *⁺ η)
    (withinDomainLinearRemainder
      f
      x
      x-domain
      d
      h
      forward-domain)


HasDerivativeWithinDomainAt :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  (x : ℝᶜ) →
  D x →
  ℝᶜ →
  Type ℓ
HasDerivativeWithinDomainAt f x x-domain d =
  Σ[ μ ∈ PrecisionModulus ]
    HasDerivativeWithinDomainAtWith f x x-domain d μ


hasDerivativeWithinDomainAtWith-submodulus :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {x d : ℝᶜ} →
  {x-domain : D x} →
  {μ ν : PrecisionModulus} →
  ((ε : ℚ⁺) → radius (ν ε) ℚOrder.≤ radius (μ ε)) →
  HasDerivativeWithinDomainAtWith f x x-domain d μ →
  HasDerivativeWithinDomainAtWith f x x-domain d ν
hasDerivativeWithinDomainAtWith-submodulus
  {μ = μ}
  {ν = ν}
  ν≤μ
  derivative
  ε
  η
  η≤νε
  h
  h-bound
  forward-domain =
  derivative
    ε
    η
    (ℚOrder.isTrans≤
      (radius η)
      (radius (ν ε))
      (radius (μ ε))
      η≤νε
      (ν≤μ ε))
    h
    h-bound
    forward-domain
