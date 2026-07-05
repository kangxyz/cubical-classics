{-

Basic symmetry facts for the HoTT Cauchy-real closeness relation

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Closeness.ReflexiveSymmetric where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Relation.Binary.Base
import Cubical.Relation.Binary.Properties as BinaryProperties

open import Constructive.CauchyReals.Base


separated : (x y : ℝᴴ) → ((ε : ℚ⁺) → x ∼[ ε ] y) → x ≡ y
separated = path


isPropClose : {x y : ℝᴴ} {ε : ℚ⁺} → isProp (x ∼[ ε ] y)
isPropClose = squash


close-refl : (x : ℝᴴ) (ε : ℚ⁺) → x ∼[ ε ] x
close-refl (rational q) ε =
  rational-rational-close q q ε (rational-close-refl q ε)
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


ArbitrarilyClose : ℝᴴ → ℝᴴ → Type₀
ArbitrarilyClose x y = (ε : ℚ⁺) → x ∼[ ε ] y


isPropArbitrarilyClose : (x y : ℝᴴ) → isProp (ArbitrarilyClose x y)
isPropArbitrarilyClose x y =
  isPropΠ λ ε → squash


isSetℝᴴ : isSet ℝᴴ
isSetℝᴴ =
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


close-sym : {x y : ℝᴴ} {ε : ℚ⁺} → x ∼[ ε ] y → y ∼[ ε ] x
close-sym (rational-rational-close q r ε q∼r) =
  rational-rational-close r q ε (rational-close-sym q r ε q∼r)
close-sym (rational-limit-close q ε δ δ<ε y q∼yδ) =
  limit-rational-close y q ε δ δ<ε (close-sym q∼yδ)
close-sym (limit-rational-close x r ε δ δ<ε xδ∼r) =
  rational-limit-close r ε δ δ<ε x (close-sym xδ∼r)
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
  {x y : ℝᴴ} {ε δ : ℚ⁺} →
  ε <⁺ δ →
  x ∼[ ε ] y →
  x ∼[ δ ] y
close-mono {δ = ζ} ε<ζ (rational-rational-close q r ε q∼r) =
  rational-rational-close q r ζ (rational-close-mono q r ε ζ ε<ζ q∼r)
close-mono {δ = ζ} ε<ζ (rational-limit-close q ε δ δ<ε y q∼yδ) =
  rational-limit-close q ζ δ δ<ζ y
    (close-mono
      {ε = ε ⊖ δ [ δ<ε ]}
      {δ = ζ ⊖ δ [ δ<ζ ]}
      (difference-mono-left ε ζ δ δ<ε δ<ζ ε<ζ)
      q∼yδ)
  where
  δ<ζ : δ <⁺ ζ
  δ<ζ = <⁺-trans {ε = δ} {δ = ε} {η = ζ} δ<ε ε<ζ
close-mono {δ = ζ} ε<ζ (limit-rational-close x r ε δ δ<ε xδ∼r) =
  limit-rational-close x r ζ δ δ<ζ
    (close-mono
      {ε = ε ⊖ δ [ δ<ε ]}
      {δ = ζ ⊖ δ [ δ<ζ ]}
      (difference-mono-left ε ζ δ δ<ε δ<ζ ε<ζ)
      xδ∼r)
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
