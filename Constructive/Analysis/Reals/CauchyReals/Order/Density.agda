{-# OPTIONS --safe #-}

module Constructive.Analysis.Reals.CauchyReals.Order.Density where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Rationals using (ℚ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
import Constructive.Analysis.Completions.CauchyCompletion.Extension as GenericExtension
open import Constructive.Analysis.Completions.CauchyCompletion.Induction
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Extension
open import Constructive.Data.PositiveRationals
open ClosenessOf RationalsMetricSpace
open ComputedOf RationalsMetricSpace
open RoundedOf RationalsMetricSpace
open GenericExtension.UniquenessOf RationalsMetricSpace
  using (limit-close-intro)
open InductionOf RationalsMetricSpace


rational-approximation :
  (x : ℝᶜ) (ε : ℚ⁺) →
  ∥ Σ[ q ∈ ℚ ] x ∼[ ε ] rational q ∥₁
rational-approximation =
  PropInduction.ind kit
  where
  kit : PropInductionKit ℓ-zero
  kit .PropInductionKit.A x =
    (ε : ℚ⁺) → ∥ Σ[ q ∈ ℚ ] x ∼[ ε ] rational q ∥₁
  kit .PropInductionKit.isPropA x =
    isPropΠ λ ε → squash₁
  kit .PropInductionKit.point* q ε =
    ∣ q , close-refl (rational q) ε ∣₁
  kit .PropInductionKit.limit* x approx* ε =
    Prop.rec squash₁ step (approx* δ β)
    where
    α β δ : ℚ⁺
    α = half⁺ ε
    β = half⁺ ε
    δ = quarter⁺ ε

    δ<α : δ <⁺ α
    δ<α = half< α

    lim∼approx : limit x ∼[ α ] approximate x δ
    lim∼approx =
      limit-close-intro x (approximate x δ) α δ δ<α
        (close-refl (approximate x δ) (α ⊖ δ [ δ<α ]))

    step :
      Σ[ q ∈ ℚ ] approximate x δ ∼[ β ] rational q →
      ∥ Σ[ q ∈ ℚ ] limit x ∼[ ε ] rational q ∥₁
    step (q , approx∼q) =
      ∣ q ,
        subst
          (λ ρ → limit x ∼[ ρ ] rational q)
          (half⁺+half⁺≡ ε)
          (close-triangle lim∼approx approx∼q)
      ∣₁
