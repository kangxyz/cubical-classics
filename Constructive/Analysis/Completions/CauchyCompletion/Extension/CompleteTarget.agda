{-

Extension into complete metric spaces

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Completions.CauchyCompletion.Extension.CompleteTarget where

open import Cubical.Foundations.Prelude

import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Metric.Map
open import Constructive.Analysis.Completions.CauchyCompletion.Extension.Unary.Core
open import Constructive.Analysis.Completions.CauchyCompletion.MetricSpace
open import Constructive.Data.PositiveRationals

private
  variable
    ℓ ℓ' ℓᵗ ℓᵗ' : Level


module CompleteTargetExtensionOf (𝓜 : MetricSpace ℓ ℓ') where
  open ExtensionOf 𝓜
  open MetricSpaceOf 𝓜

  module UniformlyContinuousCompletionExtension
    (μ : PrecisionModulus)
    (μ-completion : CompletionPrecisionModulus μ)
    (𝓝 : MetricSpace ℓᵗ ℓᵗ')
    (complete : MetricCauchy.IsCauchyComplete 𝓝)
    (f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓝)
    (f-cont : IsUniformlyContinuousWith 𝓜 𝓝 μ f)
    where
    open ExtensionOf.UniformlyContinuousExtension
      𝓜 μ μ-completion 𝓝 complete f f-cont public

    extend-uniformlyContinuousWithModulus :
      IsUniformlyContinuousWith CauchyCompletionMetricSpace 𝓝 μ extend
    extend-uniformlyContinuousWithModulus ε x∼y =
      extend-close x∼y ε (ℚOrder.isRefl≤ (radius (μ ε)))


  module ScaledLipschitzCompletionExtension
    (κ : ℚ⁺)
    (𝓝 : MetricSpace ℓᵗ ℓᵗ')
    (complete : MetricCauchy.IsCauchyComplete 𝓝)
    (f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓝)
    (f-lip : IsScaledLipschitzWith κ 𝓝 f)
    where
    open ExtensionOf.ScaledLipschitzExtension 𝓜 κ 𝓝 complete f f-lip public

    extend-lipschitz :
      IsLipschitzWith CauchyCompletionMetricSpace 𝓝
        (λ ε → posInv⁺ κ *⁺ ε)
        extend
    extend-lipschitz ε =
      extend-lipschitzWithModulus
