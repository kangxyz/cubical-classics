{-

Strict-subball bookkeeping for re-centered power series.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Recenter.StrictSubball where

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using (BoundedByᶜ ; bounded-byᶜ-add ; bounded-byᶜ-monotone)
open import Constructive.Data.PositiveRationals
  using (ℚ⁺ ; radius ; _+⁺_)


recenterStrictSubballModulus :
  ℚ⁺ →
  ℚ⁺ →
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  ℚ⁺ →
  ℕ
recenterStrictSubballModulus δ τ σ ν =
  ν


recenterShiftedDisplacementBound :
  {δ τ σ : ℚ⁺} →
  {d h : ℝᶜ} →
  BoundedByᶜ δ d →
  BoundedByᶜ τ h →
  radius (δ +⁺ τ) ℚOrder.< radius σ →
  BoundedByᶜ σ (d +ᶜ h)
recenterShiftedDisplacementBound {δ = δ} {τ = τ} {σ = σ}
    {d = d} {h = h} d-bound h-bound margin =
  bounded-byᶜ-monotone
    (ℚOrder.<Weaken≤ (radius (δ +⁺ τ)) (radius σ) margin)
    (bounded-byᶜ-add δ τ d h d-bound h-bound)
