{-

Maps between precision-indexed metric spaces

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Metric.Map where

open import Cubical.Foundations.Prelude

import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma

open import Constructive.Data.PositiveRationals
open import Constructive.Analysis.Metric.Base

private
  variable
    ℓᵃ ℓᵇ ℓᶜ ℓᵃ' ℓᵇ' ℓᶜ' : Level


PrecisionModulus : Type₀
PrecisionModulus = ℚ⁺ → ℚ⁺


IsRegularPrecisionModulus : PrecisionModulus → Type₀
IsRegularPrecisionModulus μ =
  (ε δ : ℚ⁺) →
  radius (μ ε +⁺ μ δ) ℚOrder.≤ radius (μ (ε +⁺ δ))


RegularPrecisionModulus : Type₀
RegularPrecisionModulus =
  Σ[ μ ∈ PrecisionModulus ] IsRegularPrecisionModulus μ


id-regularPrecisionModulus :
  IsRegularPrecisionModulus (λ ε → ε)
id-regularPrecisionModulus ε δ =
  ℚOrder.isRefl≤ (radius (ε +⁺ δ))


IsNonexpanding :
  (𝓧 : MetricSpace ℓᵃ ℓᵃ') →
  (𝓨 : MetricSpace ℓᵇ ℓᵇ') →
  (MetricSpace.Carrier 𝓧 → MetricSpace.Carrier 𝓨) →
  Type (ℓ-max ℓᵃ (ℓ-max ℓᵃ' ℓᵇ'))
IsNonexpanding 𝓧 𝓨 f =
  {x y : MetricSpace.Carrier 𝓧} {ε : ℚ⁺} →
  MetricSpace.Close 𝓧 x ε y →
  MetricSpace.Close 𝓨 (f x) ε (f y)


IsUniformlyContinuousWith :
  (𝓧 : MetricSpace ℓᵃ ℓᵃ') →
  (𝓨 : MetricSpace ℓᵇ ℓᵇ') →
  PrecisionModulus →
  (MetricSpace.Carrier 𝓧 → MetricSpace.Carrier 𝓨) →
  Type (ℓ-max ℓᵃ (ℓ-max ℓᵃ' ℓᵇ'))
IsUniformlyContinuousWith 𝓧 𝓨 μ f =
  (ε : ℚ⁺) →
  {x y : MetricSpace.Carrier 𝓧} →
  MetricSpace.Close 𝓧 x (μ ε) y →
  MetricSpace.Close 𝓨 (f x) ε (f y)


IsUniformlyContinuous :
  (𝓧 : MetricSpace ℓᵃ ℓᵃ') →
  (𝓨 : MetricSpace ℓᵇ ℓᵇ') →
  (MetricSpace.Carrier 𝓧 → MetricSpace.Carrier 𝓨) →
  Type (ℓ-max ℓᵃ (ℓ-max ℓᵃ' ℓᵇ'))
IsUniformlyContinuous 𝓧 𝓨 f =
  Σ[ μ ∈ PrecisionModulus ] IsUniformlyContinuousWith 𝓧 𝓨 μ f


IsLipschitzWith :
  (𝓧 : MetricSpace ℓᵃ ℓᵃ') →
  (𝓨 : MetricSpace ℓᵇ ℓᵇ') →
  ℚ⁺ →
  (MetricSpace.Carrier 𝓧 → MetricSpace.Carrier 𝓨) →
  Type (ℓ-max ℓᵃ (ℓ-max ℓᵃ' ℓᵇ'))
IsLipschitzWith 𝓧 𝓨 κ f =
  (x y : MetricSpace.Carrier 𝓧) →
  (ε : ℚ⁺) →
  MetricSpace.Close 𝓧 x ε y →
  MetricSpace.Close 𝓨 (f x) (κ *⁺ ε) (f y)


IsLipschitz :
  (𝓧 : MetricSpace ℓᵃ ℓᵃ') →
  (𝓨 : MetricSpace ℓᵇ ℓᵇ') →
  (MetricSpace.Carrier 𝓧 → MetricSpace.Carrier 𝓨) →
  Type (ℓ-max ℓᵃ (ℓ-max ℓᵃ' ℓᵇ'))
IsLipschitz 𝓧 𝓨 f =
  Σ[ κ ∈ ℚ⁺ ] IsLipschitzWith 𝓧 𝓨 κ f


nonexpanding→lipschitz :
  {𝓧 : MetricSpace ℓᵃ ℓᵃ'} →
  {𝓨 : MetricSpace ℓᵇ ℓᵇ'} →
  {f : MetricSpace.Carrier 𝓧 → MetricSpace.Carrier 𝓨} →
  IsNonexpanding 𝓧 𝓨 f →
  IsLipschitz 𝓧 𝓨 f
nonexpanding→lipschitz {𝓨 = 𝓨} {f = f} f-ne =
  1⁺ , λ x y ε x∼y →
    subst
      (λ δ → MetricSpace.Close 𝓨 (f x) δ (f y))
      (sym (*⁺-identity-left ε))
      (f-ne x∼y)


id-nonexpanding :
  (𝓧 : MetricSpace ℓᵃ ℓᵃ') →
  IsNonexpanding 𝓧 𝓧 (λ x → x)
id-nonexpanding 𝓧 x∼y =
  x∼y


id-uniformlyContinuous :
  (𝓧 : MetricSpace ℓᵃ ℓᵃ') →
  IsUniformlyContinuous 𝓧 𝓧 (λ x → x)
id-uniformlyContinuous 𝓧 =
  (λ ε → ε) , λ ε x∼y → x∼y


id-lipschitz :
  (𝓧 : MetricSpace ℓᵃ ℓᵃ') →
  IsLipschitz 𝓧 𝓧 (λ x → x)
id-lipschitz 𝓧 =
  nonexpanding→lipschitz
    {𝓧 = 𝓧} {𝓨 = 𝓧} {f = λ x → x}
    (id-nonexpanding 𝓧)


constant-nonexpanding :
  (𝓧 : MetricSpace ℓᵃ ℓᵃ') →
  (𝓨 : MetricSpace ℓᵇ ℓᵇ') →
  (c : MetricSpace.Carrier 𝓨) →
  IsNonexpanding 𝓧 𝓨 (λ _ → c)
constant-nonexpanding 𝓧 𝓨 c {ε = ε} _ =
  MetricSpace.close-refl 𝓨 c ε


constant-uniformlyContinuous :
  (𝓧 : MetricSpace ℓᵃ ℓᵃ') →
  (𝓨 : MetricSpace ℓᵇ ℓᵇ') →
  (c : MetricSpace.Carrier 𝓨) →
  IsUniformlyContinuous 𝓧 𝓨 (λ _ → c)
constant-uniformlyContinuous 𝓧 𝓨 c =
  (λ ε → ε) , λ ε _ → MetricSpace.close-refl 𝓨 c ε


constant-lipschitz :
  (𝓧 : MetricSpace ℓᵃ ℓᵃ') →
  (𝓨 : MetricSpace ℓᵇ ℓᵇ') →
  (c : MetricSpace.Carrier 𝓨) →
  IsLipschitz 𝓧 𝓨 (λ _ → c)
constant-lipschitz 𝓧 𝓨 c =
  nonexpanding→lipschitz
    {𝓧 = 𝓧} {𝓨 = 𝓨} {f = λ _ → c}
    (constant-nonexpanding 𝓧 𝓨 c)


nonexpanding→uniformlyContinuous :
  {𝓧 : MetricSpace ℓᵃ ℓᵃ'} →
  {𝓨 : MetricSpace ℓᵇ ℓᵇ'} →
  {f : MetricSpace.Carrier 𝓧 → MetricSpace.Carrier 𝓨} →
  IsNonexpanding 𝓧 𝓨 f →
  IsUniformlyContinuous 𝓧 𝓨 f
nonexpanding→uniformlyContinuous f-ne =
  (λ ε → ε) , λ ε → f-ne


lipschitz→uniformlyContinuous :
  {𝓧 : MetricSpace ℓᵃ ℓᵃ'} →
  {𝓨 : MetricSpace ℓᵇ ℓᵇ'} →
  {f : MetricSpace.Carrier 𝓧 → MetricSpace.Carrier 𝓨} →
  IsLipschitz 𝓧 𝓨 f →
  IsUniformlyContinuous 𝓧 𝓨 f
lipschitz→uniformlyContinuous
  {𝓧 = 𝓧} {𝓨 = 𝓨} {f = f} f-lip =
  (λ ε → posInv⁺ κ *⁺ ε) , λ ε {x = x} {y = y} x∼y →
    subst
      (λ δ → MetricSpace.Close 𝓨 (f x) δ (f y))
      (scale-posInv-cancel κ ε)
      (κ-lipschitz x y (posInv⁺ κ *⁺ ε) x∼y)
  where
  κ : ℚ⁺
  κ = f-lip .fst

  κ-lipschitz : IsLipschitzWith 𝓧 𝓨 κ f
  κ-lipschitz = f-lip .snd


comp-nonexpanding :
  {𝓧 : MetricSpace ℓᵃ ℓᵃ'} →
  {𝓨 : MetricSpace ℓᵇ ℓᵇ'} →
  {𝓩 : MetricSpace ℓᶜ ℓᶜ'} →
  {f : MetricSpace.Carrier 𝓨 → MetricSpace.Carrier 𝓩} →
  {g : MetricSpace.Carrier 𝓧 → MetricSpace.Carrier 𝓨} →
  IsNonexpanding 𝓨 𝓩 f →
  IsNonexpanding 𝓧 𝓨 g →
  IsNonexpanding 𝓧 𝓩 (λ x → f (g x))
comp-nonexpanding f-ne g-ne x∼y =
  f-ne (g-ne x∼y)


comp-uniformlyContinuous :
  {𝓧 : MetricSpace ℓᵃ ℓᵃ'} →
  {𝓨 : MetricSpace ℓᵇ ℓᵇ'} →
  {𝓩 : MetricSpace ℓᶜ ℓᶜ'} →
  {f : MetricSpace.Carrier 𝓨 → MetricSpace.Carrier 𝓩} →
  {g : MetricSpace.Carrier 𝓧 → MetricSpace.Carrier 𝓨} →
  IsUniformlyContinuous 𝓨 𝓩 f →
  IsUniformlyContinuous 𝓧 𝓨 g →
  IsUniformlyContinuous 𝓧 𝓩 (λ x → f (g x))
comp-uniformlyContinuous (μ , f-cont) (ν , g-cont) =
  (λ ε → ν (μ ε)) , λ ε x∼y → f-cont ε (g-cont (μ ε) x∼y)


comp-lipschitz :
  {𝓧 : MetricSpace ℓᵃ ℓᵃ'} →
  {𝓨 : MetricSpace ℓᵇ ℓᵇ'} →
  {𝓩 : MetricSpace ℓᶜ ℓᶜ'} →
  {f : MetricSpace.Carrier 𝓨 → MetricSpace.Carrier 𝓩} →
  {g : MetricSpace.Carrier 𝓧 → MetricSpace.Carrier 𝓨} →
  IsLipschitz 𝓨 𝓩 f →
  IsLipschitz 𝓧 𝓨 g →
  IsLipschitz 𝓧 𝓩 (λ x → f (g x))
comp-lipschitz {𝓩 = 𝓩} {f = f} {g = g}
  (κ , f-lip) (λκ , g-lip) =
  (κ *⁺ λκ) , λ x y ε x∼y →
    subst
      (λ δ → MetricSpace.Close 𝓩 (f (g x)) δ (f (g y)))
      (sym (*⁺-assoc κ λκ ε))
      (f-lip (g x) (g y) (λκ *⁺ ε) (g-lip x y ε x∼y))
