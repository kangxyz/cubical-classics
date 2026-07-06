{-

Roundedness of Cauchy-completion closeness

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.CauchyCompletion.Closeness.Rounded where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.CauchyCompletion.Base
open import Constructive.Data.PositiveRationals

private
  variable
    ℓ ℓ' : Level


module RoundedOf (𝓜 : MetricSpace ℓ ℓ') where
  open CompletionOf 𝓜

  close-rounded :
    {x y : Completion} {ε : ℚ⁺} →
    x ∼[ ε ] y →
    ∥ Σ[ δ ∈ ℚ⁺ ] (δ <⁺ ε) × (x ∼[ δ ] y) ∥₁
  close-rounded (point-point-close a b ε a∼b) =
    Prop.map
      (λ (δ , δ<ε , a∼bδ) →
        δ , δ<ε , point-point-close a b δ a∼bδ)
      (MetricSpace.close-rounded 𝓜 a∼b)
  close-rounded (point-limit-close a ε δ δ<ε y a∼yδ) =
    Prop.rec squash₁ rounded (close-rounded a∼yδ)
    where
    rounded :
      Σ[ κ ∈ ℚ⁺ ]
        (κ <⁺ (ε ⊖ δ [ δ<ε ])) ×
        (point a ∼[ κ ] approximate y δ) →
      ∥ Σ[ ζ ∈ ℚ⁺ ] (ζ <⁺ ε) × (point a ∼[ ζ ] limit y) ∥₁
    rounded (κ , κ<ε-δ , a∼yκ) =
      ∣ ζ , ζ<ε ,
        point-limit-close a ζ δ δ<ζ y
          (subst
            (λ θ → point a ∼[ θ ] approximate y δ)
            (sym ζ-δ≡κ)
            a∼yκ)
      ∣₁
      where
      ζ : ℚ⁺
      ζ = δ +⁺ κ

      δ<ζ : δ <⁺ ζ
      δ<ζ = summand-left<sum δ κ

      ζ<ε : ζ <⁺ ε
      ζ<ε = sum<from-difference ε δ κ δ<ε κ<ε-δ

      ζ-δ≡κ : ζ ⊖ δ [ δ<ζ ] ≡ κ
      ζ-δ≡κ = sum-difference-left δ κ δ<ζ
  close-rounded (limit-point-close x b ε δ δ<ε xδ∼b) =
    Prop.rec squash₁ rounded (close-rounded xδ∼b)
    where
    rounded :
      Σ[ κ ∈ ℚ⁺ ]
        (κ <⁺ (ε ⊖ δ [ δ<ε ])) ×
        (approximate x δ ∼[ κ ] point b) →
      ∥ Σ[ ζ ∈ ℚ⁺ ] (ζ <⁺ ε) × (limit x ∼[ ζ ] point b) ∥₁
    rounded (κ , κ<ε-δ , xκ∼b) =
      ∣ ζ , ζ<ε ,
        limit-point-close x b ζ δ δ<ζ
          (subst
            (λ θ → approximate x δ ∼[ θ ] point b)
            (sym ζ-δ≡κ)
            xκ∼b)
      ∣₁
      where
      ζ : ℚ⁺
      ζ = δ +⁺ κ

      δ<ζ : δ <⁺ ζ
      δ<ζ = summand-left<sum δ κ

      ζ<ε : ζ <⁺ ε
      ζ<ε = sum<from-difference ε δ κ δ<ε κ<ε-δ

      ζ-δ≡κ : ζ ⊖ δ [ δ<ζ ] ≡ κ
      ζ-δ≡κ = sum-difference-left δ κ δ<ζ
  close-rounded (limit-limit-close x y ε δ η δ+η<ε xδ∼yη) =
    Prop.rec squash₁ rounded (close-rounded xδ∼yη)
    where
    θ : ℚ⁺
    θ = δ +⁺ η

    rounded :
      Σ[ κ ∈ ℚ⁺ ]
        (κ <⁺ (ε ⊖ θ [ δ+η<ε ])) ×
        (approximate x δ ∼[ κ ] approximate y η) →
      ∥ Σ[ ζ ∈ ℚ⁺ ] (ζ <⁺ ε) × (limit x ∼[ ζ ] limit y) ∥₁
    rounded (κ , κ<ε-θ , xκ∼y) =
      ∣ ζ , ζ<ε ,
        limit-limit-close x y ζ δ η θ<ζ
          (subst
            (λ ρ → approximate x δ ∼[ ρ ] approximate y η)
            (sym ζ-θ≡κ)
            xκ∼y)
      ∣₁
      where
      ζ : ℚ⁺
      ζ = θ +⁺ κ

      θ<ζ : θ <⁺ ζ
      θ<ζ = summand-left<sum θ κ

      ζ<ε : ζ <⁺ ε
      ζ<ε = sum<from-difference ε θ κ δ+η<ε κ<ε-θ

      ζ-θ≡κ : ζ ⊖ θ [ θ<ζ ] ≡ κ
      ζ-θ≡κ = sum-difference-left θ κ θ<ζ
  close-rounded (squash p q i) =
    squash₁ (close-rounded p) (close-rounded q) i
