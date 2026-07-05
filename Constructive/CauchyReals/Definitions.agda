{-

Shared definitions for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Definitions where

open import Cubical.Foundations.Prelude

open import Constructive.CauchyReals.Base

private
  variable
    ℓ ℓ' : Level


IsCauchyApproximation : (ℚ⁺ → ℝᶜ) → Type₀
IsCauchyApproximation x =
  (ε δ : ℚ⁺) → x ε ∼[ ε +⁺ δ ] x δ


asFunction : CauchyApproximation → ℚ⁺ → ℝᶜ
asFunction = approximate


DependentCloseness :
  (A : ℝᶜ → Type ℓ) → (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
DependentCloseness A ℓ' =
  (ε : ℚ⁺) {x y : ℝᶜ} →
  x ∼[ ε ] y →
  A x → A y → Type ℓ'


IsDependentCauchyApproximation :
  {A : ℝᶜ → Type ℓ} →
  (B : DependentCloseness A ℓ') →
  (x : CauchyApproximation) →
  ((ε : ℚ⁺) → A (approximate x ε)) →
  Type ℓ'
IsDependentCauchyApproximation B x a =
  (ε δ : ℚ⁺) →
  B (ε +⁺ δ) (isRegular x ε δ) (a ε) (a δ)


TargetCloseness : (A : Type ℓ) → (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
TargetCloseness A ℓ' =
  ℚ⁺ → A → A → Type ℓ'


IsTargetCauchyApproximation :
  {A : Type ℓ} →
  TargetCloseness A ℓ' →
  (ℚ⁺ → A) →
  Type ℓ'
IsTargetCauchyApproximation B x =
  (ε δ : ℚ⁺) → B (ε +⁺ δ) (x ε) (x δ)
