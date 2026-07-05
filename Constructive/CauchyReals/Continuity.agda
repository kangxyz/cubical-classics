{-

Continuity predicates for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Continuity where

open import Cubical.Foundations.Prelude

open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Lipschitz.Base


IsNonexpanding : (ℝᴴ → ℝᴴ) → Type₀
IsNonexpanding f =
  {x y : ℝᴴ} {ε : ℚ⁺} →
  x ∼[ ε ] y →
  f x ∼[ ε ] f y


IsContinuous : (ℝᴴ → ℝᴴ) → Type₀
IsContinuous f =
  (ε : ℚ⁺) → Σ[ δ ∈ ℚ⁺ ]
    ({x y : ℝᴴ} → x ∼[ δ ] y → f x ∼[ ε ] f y)


id-nonexpanding : IsNonexpanding (λ x → x)
id-nonexpanding x∼y = x∼y


comp-nonexpanding :
  {f g : ℝᴴ → ℝᴴ} →
  IsNonexpanding f →
  IsNonexpanding g →
  IsNonexpanding (λ x → f (g x))
comp-nonexpanding f-ne g-ne x∼y =
  f-ne (g-ne x∼y)


nonexpanding→continuous :
  {f : ℝᴴ → ℝᴴ} →
  IsNonexpanding f →
  IsContinuous f
nonexpanding→continuous f-ne ε =
  ε , f-ne


lipschitz→continuous :
  {f : ℝᴴ → ℝᴴ} →
  IsLipschitz f →
  IsContinuous f
lipschitz→continuous (μ , f-lip) ε =
  μ ε , f-lip ε
