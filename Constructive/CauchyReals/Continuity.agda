{-

Continuity predicates for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Continuity where

open import Cubical.Foundations.Prelude

open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Closeness.ReflexiveSymmetric
open import Constructive.CauchyReals.Lipschitz.Base


IsNonexpanding : (ℝᶜ → ℝᶜ) → Type₀
IsNonexpanding f =
  {x y : ℝᶜ} {ε : ℚ⁺} →
  x ∼[ ε ] y →
  f x ∼[ ε ] f y


IsContinuous : (ℝᶜ → ℝᶜ) → Type₀
IsContinuous f =
  (ε : ℚ⁺) → Σ[ δ ∈ ℚ⁺ ]
    ({x y : ℝᶜ} → x ∼[ δ ] y → f x ∼[ ε ] f y)


id-nonexpanding : IsNonexpanding (λ x → x)
id-nonexpanding x∼y = x∼y


comp-nonexpanding :
  {f g : ℝᶜ → ℝᶜ} →
  IsNonexpanding f →
  IsNonexpanding g →
  IsNonexpanding (λ x → f (g x))
comp-nonexpanding f-ne g-ne x∼y =
  f-ne (g-ne x∼y)


constant-nonexpanding :
  (c : ℝᶜ) →
  IsNonexpanding (λ _ → c)
constant-nonexpanding c {ε = ε} _ =
  close-refl c ε


constant-continuous :
  (c : ℝᶜ) →
  IsContinuous (λ _ → c)
constant-continuous c ε =
  ε , λ _ → close-refl c ε


nonexpanding→continuous :
  {f : ℝᶜ → ℝᶜ} →
  IsNonexpanding f →
  IsContinuous f
nonexpanding→continuous f-ne ε =
  ε , f-ne


comp-continuous :
  {f g : ℝᶜ → ℝᶜ} →
  IsContinuous f →
  IsContinuous g →
  IsContinuous (λ x → f (g x))
comp-continuous {f = f} {g = g} f-cont g-cont ε =
  δ , λ x∼y → f-close (g-close x∼y)
  where
  μ : ℚ⁺
  μ = fst (f-cont ε)

  f-close : {x y : ℝᶜ} → x ∼[ μ ] y → f x ∼[ ε ] f y
  f-close = snd (f-cont ε)

  δ : ℚ⁺
  δ = fst (g-cont μ)

  g-close : {x y : ℝᶜ} → x ∼[ δ ] y → g x ∼[ μ ] g y
  g-close = snd (g-cont μ)


lipschitz→continuous :
  {f : ℝᶜ → ℝᶜ} →
  IsLipschitz f →
  IsContinuous f
lipschitz→continuous (μ , f-lip) ε =
  μ ε , f-lip ε
