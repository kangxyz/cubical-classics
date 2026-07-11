{-

Precision splits used by uniformly continuous Cauchy extension

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Completions.CauchyCompletion.Extension.Precision where

open import Cubical.Foundations.Prelude

import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Data.PositiveRationals


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
