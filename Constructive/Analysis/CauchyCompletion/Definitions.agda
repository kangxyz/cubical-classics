{-

Shared definitions for Cauchy completions

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.CauchyCompletion.Definitions where

open import Cubical.Foundations.Prelude

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.CauchyCompletion.Base
open import Constructive.Data.PositiveRationals

private
  variable
    ℓᵐ ℓᵐ' ℓ ℓ' : Level


module DefinitionsOf (𝓜 : MetricSpace ℓᵐ ℓᵐ') where
  open CompletionOf 𝓜

  private
    ℓᶜ : Level
    ℓᶜ = ℓ-max ℓᵐ ℓᵐ'

  IsCauchyApproximation : (ℚ⁺ → Completion) → Type ℓᶜ
  IsCauchyApproximation x =
    (ε δ : ℚ⁺) → x ε ∼[ ε +⁺ δ ] x δ


  asFunction : CauchyApproximation → ℚ⁺ → Completion
  asFunction = approximate


  DependentCloseness :
    (A : Completion → Type ℓ) → (ℓ' : Level) →
    Type (ℓ-max ℓᶜ (ℓ-max ℓ (ℓ-suc ℓ')))
  DependentCloseness A ℓ' =
    (ε : ℚ⁺) {x y : Completion} →
    x ∼[ ε ] y →
    A x → A y → Type ℓ'


  IsDependentCauchyApproximation :
    {A : Completion → Type ℓ} →
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
