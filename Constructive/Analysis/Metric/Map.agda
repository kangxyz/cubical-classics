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


record PointLimitSplit
  (μ ν : PrecisionModulus)
  (ε δ θ : ℚ⁺)
  (δ<ε : δ <⁺ ε)
  : Type₀ where
  no-eta-equality

  field
    pointPrecision : ℚ⁺
    bridgePrecision : ℚ⁺
    limitPrecision : ℚ⁺
    limitIndex : ℚ⁺

    limitIndex<limitPrecision :
      limitIndex <⁺ limitPrecision
    pointSource≤ :
      radius (ε ⊖ δ [ δ<ε ]) ℚOrder.≤ radius (μ pointPrecision)
    bridgeSource≤ :
      radius (δ +⁺ ν limitIndex) ℚOrder.≤ radius (μ bridgePrecision)
    pointLimitTotal≤ :
      radius ((pointPrecision +⁺ bridgePrecision) +⁺ limitPrecision)
        ℚOrder.≤
      radius θ


record LimitLimitSplit
  (μ ν : PrecisionModulus)
  (ε δ η θ : ℚ⁺)
  (δ+η<ε : δ +⁺ η <⁺ ε)
  : Type₀ where
  no-eta-equality

  field
    leftPrecision : ℚ⁺
    leftIndex : ℚ⁺
    leftBridgePrecision : ℚ⁺
    middlePrecision : ℚ⁺
    rightBridgePrecision : ℚ⁺
    rightPrecision : ℚ⁺
    rightIndex : ℚ⁺

    leftIndex<leftPrecision :
      leftIndex <⁺ leftPrecision
    leftBridgeSource≤ :
      radius (ν leftIndex +⁺ δ) ℚOrder.≤ radius (μ leftBridgePrecision)
    middleSource≤ :
      radius (ε ⊖ (δ +⁺ η) [ δ+η<ε ]) ℚOrder.≤
      radius (μ middlePrecision)
    rightBridgeSource≤ :
      radius (η +⁺ ν rightIndex) ℚOrder.≤ radius (μ rightBridgePrecision)
    rightIndex<rightPrecision :
      rightIndex <⁺ rightPrecision
    limitLimitTotal≤ :
      radius
        (((leftPrecision +⁺ leftBridgePrecision) +⁺ middlePrecision)
          +⁺ rightBridgePrecision
          +⁺ rightPrecision)
        ℚOrder.≤
      radius θ


record CompletionPrecisionModulus (μ : PrecisionModulus) : Type₀ where
  no-eta-equality

  field
    limitPrecisionModulus : PrecisionModulus
    limitPrecisionRegular :
      (ε δ : ℚ⁺) →
      radius (limitPrecisionModulus ε +⁺ limitPrecisionModulus δ)
        ℚOrder.≤
      radius (μ (ε +⁺ δ))
    pointLimitSplit :
      (ε δ θ : ℚ⁺) →
      (δ<ε : δ <⁺ ε) →
      radius ε ℚOrder.≤ radius (μ θ) →
      PointLimitSplit μ limitPrecisionModulus ε δ θ δ<ε
    limitLimitSplit :
      (ε δ η θ : ℚ⁺) →
      (δ+η<ε : δ +⁺ η <⁺ ε) →
      radius ε ℚOrder.≤ radius (μ θ) →
      LimitLimitSplit μ limitPrecisionModulus ε δ η θ δ+η<ε


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
  PrecisionModulus →
  (MetricSpace.Carrier 𝓧 → MetricSpace.Carrier 𝓨) →
  Type (ℓ-max ℓᵃ (ℓ-max ℓᵃ' ℓᵇ'))
IsLipschitzWith =
  IsUniformlyContinuousWith


IsLipschitz :
  (𝓧 : MetricSpace ℓᵃ ℓᵃ') →
  (𝓨 : MetricSpace ℓᵇ ℓᵇ') →
  (MetricSpace.Carrier 𝓧 → MetricSpace.Carrier 𝓨) →
  Type (ℓ-max ℓᵃ (ℓ-max ℓᵃ' ℓᵇ'))
IsLipschitz 𝓧 𝓨 f =
  Σ[ μ ∈ PrecisionModulus ] IsLipschitzWith 𝓧 𝓨 μ f


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
id-lipschitz =
  id-uniformlyContinuous


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
lipschitz→uniformlyContinuous f-lip =
  f-lip


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
comp-lipschitz (μ , f-lip) (ν , g-lip) =
  (λ ε → ν (μ ε)) , λ ε x∼y → f-lip ε (g-lip (μ ε) x∼y)
