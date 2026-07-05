{-

Roundedness of HoTT Cauchy-real closeness

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Closeness.Rounded where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

open import Constructive.CauchyReals.Base


close-rounded :
  {x y : ℝᶜ} {ε : ℚ⁺} →
  x ∼[ ε ] y →
  ∥ Σ[ δ ∈ ℚ⁺ ] (δ <⁺ ε) × (x ∼[ δ ] y) ∥₁
close-rounded (rational-rational-close q r ε q∼r) =
  Prop.map
    (λ (δ , δ<ε , q∼rδ) →
      δ , δ<ε , rational-rational-close q r δ q∼rδ)
    (rational-close-rounded q r ε q∼r)
close-rounded (rational-limit-close q ε δ δ<ε y q∼yδ) =
  Prop.rec squash₁ rounded (close-rounded q∼yδ)
  where
  rounded :
    Σ[ κ ∈ ℚ⁺ ]
      (κ <⁺ (ε ⊖ δ [ δ<ε ])) ×
      (rational q ∼[ κ ] approximate y δ) →
    ∥ Σ[ ζ ∈ ℚ⁺ ] (ζ <⁺ ε) × (rational q ∼[ ζ ] limit y) ∥₁
  rounded (κ , κ<ε-δ , q∼yκ) =
    ∣ ζ , ζ<ε ,
      rational-limit-close q ζ δ δ<ζ y
        (subst
          (λ θ → rational q ∼[ θ ] approximate y δ)
          (sym ζ-δ≡κ)
          q∼yκ)
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
close-rounded (limit-rational-close x r ε δ δ<ε xδ∼r) =
  Prop.rec squash₁ rounded (close-rounded xδ∼r)
  where
  rounded :
    Σ[ κ ∈ ℚ⁺ ]
      (κ <⁺ (ε ⊖ δ [ δ<ε ])) ×
      (approximate x δ ∼[ κ ] rational r) →
    ∥ Σ[ ζ ∈ ℚ⁺ ] (ζ <⁺ ε) × (limit x ∼[ ζ ] rational r) ∥₁
  rounded (κ , κ<ε-δ , xκ∼r) =
    ∣ ζ , ζ<ε ,
      limit-rational-close x r ζ δ δ<ζ
        (subst
          (λ θ → approximate x δ ∼[ θ ] rational r)
          (sym ζ-δ≡κ)
          xκ∼r)
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
