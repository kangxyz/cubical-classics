{-

Basic symmetry facts for Cauchy-completion closeness

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.CauchyCompletion.Closeness.ReflexiveSymmetric where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Relation.Binary.Base
import Cubical.Relation.Binary.Properties as BinaryProperties

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.CauchyCompletion.Base
open import Constructive.Data.PositiveRationals

private
  variable
    ℓ ℓ' : Level


module ClosenessOf (𝓜 : MetricSpace ℓ ℓ') where
  open CompletionOf 𝓜

  private
    A : Type ℓ
    A = MetricSpace.Carrier 𝓜

    ℓᶜ : Level
    ℓᶜ = ℓ-max ℓ ℓ'

  separated : (x y : Completion) → ((ε : ℚ⁺) → x ∼[ ε ] y) → x ≡ y
  separated = path


  isPropClose : {x y : Completion} {ε : ℚ⁺} → isProp (x ∼[ ε ] y)
  isPropClose = squash


  close-refl : (x : Completion) (ε : ℚ⁺) → x ∼[ ε ] x
  close-refl (point a) ε =
    point-point-close a a ε (MetricSpace.close-refl 𝓜 a ε)
  close-refl (limit x) ε =
    limit-limit-close x x ε δ δ δ+δ<ε
      (subst
        (λ κ → approximate x δ ∼[ κ ] approximate x δ)
        (sym (quarter-sum-difference≡ ε δ+δ<ε))
        (isRegular x δ δ))
    where
    δ : ℚ⁺
    δ = quarter⁺ ε

    δ+δ<ε : δ +⁺ δ <⁺ ε
    δ+δ<ε = quarter-sum< ε
  close-refl (path x y x∼y i) ε =
    isProp→PathP
      (λ i → squash {x = path x y x∼y i} {y = path x y x∼y i} {ε = ε})
      (close-refl x ε)
      (close-refl y ε)
      i


  ArbitrarilyClose : Completion → Completion → Type ℓᶜ
  ArbitrarilyClose x y = (ε : ℚ⁺) → x ∼[ ε ] y


  isPropArbitrarilyClose : (x y : Completion) → isProp (ArbitrarilyClose x y)
  isPropArbitrarilyClose x y =
    isPropΠ λ ε → squash


  isSetCompletion : isSet Completion
  isSetCompletion =
    BinaryProperties.reflPropRelImpliesIdentity→isSet ArbitrarilyClose
      close-refl
      isPropArbitrarilyClose
      (λ {x} {y} → path x y)


  private
    sum-comm-< :
      (ε δ η : ℚ⁺) →
      δ +⁺ η <⁺ ε →
      η +⁺ δ <⁺ ε
    sum-comm-< ε δ η δ+η<ε =
      subst
        (λ q → q ℚOrder.< radius ε)
        (ℚ.+Comm (radius δ) (radius η))
        δ+η<ε

    difference-sum-comm :
      (ε δ η : ℚ⁺) →
      (δ+η<ε : δ +⁺ η <⁺ ε) →
      (η+δ<ε : η +⁺ δ <⁺ ε) →
      ε ⊖ (δ +⁺ η) [ δ+η<ε ] ≡
      ε ⊖ (η +⁺ δ) [ η+δ<ε ]
    difference-sum-comm ε δ η δ+η<ε η+δ<ε =
      ℚ⁺Path (cong (λ q → radius ε ℚ.- q) (ℚ.+Comm (radius δ) (radius η)))


  close-sym : {x y : Completion} {ε : ℚ⁺} → x ∼[ ε ] y → y ∼[ ε ] x
  close-sym (point-point-close a b ε a∼b) =
    point-point-close b a ε (MetricSpace.close-sym 𝓜 a∼b)
  close-sym (point-limit-close a ε δ δ<ε y a∼yδ) =
    limit-point-close y a ε δ δ<ε (close-sym a∼yδ)
  close-sym (limit-point-close x b ε δ δ<ε xδ∼b) =
    point-limit-close b ε δ δ<ε x (close-sym xδ∼b)
  close-sym (limit-limit-close x y ε δ η δ+η<ε xδ∼yη) =
    limit-limit-close y x ε η δ η+δ<ε
      (subst
        (λ κ → approximate y η ∼[ κ ] approximate x δ)
        (difference-sum-comm ε δ η δ+η<ε η+δ<ε)
        (close-sym xδ∼yη))
    where
    η+δ<ε : η +⁺ δ <⁺ ε
    η+δ<ε = sum-comm-< ε δ η δ+η<ε
  close-sym (squash p q i) =
    squash (close-sym p) (close-sym q) i


  close-mono :
    {x y : Completion} {ε δ : ℚ⁺} →
    ε <⁺ δ →
    x ∼[ ε ] y →
    x ∼[ δ ] y
  close-mono {δ = ζ} ε<ζ (point-point-close a b ε a∼b) =
    point-point-close a b ζ (MetricSpace.close-mono 𝓜 ε<ζ a∼b)
  close-mono {δ = ζ} ε<ζ (point-limit-close a ε δ δ<ε y a∼yδ) =
    point-limit-close a ζ δ δ<ζ y
      (close-mono
        {ε = ε ⊖ δ [ δ<ε ]}
        {δ = ζ ⊖ δ [ δ<ζ ]}
        (difference-mono-left ε ζ δ δ<ε δ<ζ ε<ζ)
        a∼yδ)
    where
    δ<ζ : δ <⁺ ζ
    δ<ζ = <⁺-trans {ε = δ} {δ = ε} {η = ζ} δ<ε ε<ζ
  close-mono {δ = ζ} ε<ζ (limit-point-close x b ε δ δ<ε xδ∼b) =
    limit-point-close x b ζ δ δ<ζ
      (close-mono
        {ε = ε ⊖ δ [ δ<ε ]}
        {δ = ζ ⊖ δ [ δ<ζ ]}
        (difference-mono-left ε ζ δ δ<ε δ<ζ ε<ζ)
        xδ∼b)
    where
    δ<ζ : δ <⁺ ζ
    δ<ζ = <⁺-trans {ε = δ} {δ = ε} {η = ζ} δ<ε ε<ζ
  close-mono {δ = ζ} ε<ζ (limit-limit-close x y ε δ η δ+η<ε xδ∼yη) =
    limit-limit-close x y ζ δ η δ+η<ζ
      (close-mono
        {ε = ε ⊖ (δ +⁺ η) [ δ+η<ε ]}
        {δ = ζ ⊖ (δ +⁺ η) [ δ+η<ζ ]}
        (difference-mono-left ε ζ (δ +⁺ η) δ+η<ε δ+η<ζ ε<ζ)
        xδ∼yη)
    where
    δ+η<ζ : δ +⁺ η <⁺ ζ
    δ+η<ζ = <⁺-trans {ε = δ +⁺ η} {δ = ε} {η = ζ} δ+η<ε ε<ζ
  close-mono ε<δ (squash p q i) =
    squash (close-mono ε<δ p) (close-mono ε<δ q) i
