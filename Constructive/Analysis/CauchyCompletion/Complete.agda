{-

Metric structure on Cauchy completions

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.CauchyCompletion.Complete where

open import Cubical.Foundations.Prelude

import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Map
import Constructive.Analysis.Metric.Cauchy as MetricComplete
open import Constructive.Analysis.CauchyCompletion.Base
open import Constructive.Analysis.CauchyCompletion.Closeness.ReflexiveSymmetric
open import Constructive.Analysis.CauchyCompletion.Closeness.Internal.Computed
open import Constructive.Analysis.CauchyCompletion.Closeness.Rounded
open import Constructive.Analysis.CauchyCompletion.Extension.Core
open import Constructive.Data.PositiveRationals

private
  variable
    ℓ ℓ' ℓᵗ ℓᵗ' : Level


module CompleteOf (𝓜 : MetricSpace ℓ ℓ') where
  open CompletionOf 𝓜
  open ClosenessOf 𝓜
  open ComputedOf 𝓜
    using (close→computed ; close-triangle)
  open RoundedOf 𝓜
  open ExtensionOf 𝓜

  CauchyCompletionMetricSpace : MetricSpace (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  CauchyCompletionMetricSpace .MetricSpace.Carrier =
    Completion
  CauchyCompletionMetricSpace .MetricSpace.isSetCarrier =
    isSetCompletion
  CauchyCompletionMetricSpace .MetricSpace.Close x ε y =
    x ∼[ ε ] y
  CauchyCompletionMetricSpace .MetricSpace.isPropClose x y ε =
    squash
  CauchyCompletionMetricSpace .MetricSpace.close-refl =
    close-refl
  CauchyCompletionMetricSpace .MetricSpace.close-sym =
    close-sym
  CauchyCompletionMetricSpace .MetricSpace.close-mono =
    close-mono
  CauchyCompletionMetricSpace .MetricSpace.close-triangle =
    close-triangle
  CauchyCompletionMetricSpace .MetricSpace.close-rounded =
    close-rounded
  CauchyCompletionMetricSpace .MetricSpace.close-separated =
    path


  pointNonexpanding :
    IsNonexpanding 𝓜 CauchyCompletionMetricSpace point
  pointNonexpanding {x = a} {y = b} {ε = ε} =
    point-point-close a b ε


  pointReflecting :
    {a b : MetricSpace.Carrier 𝓜} {ε : ℚ⁺} →
    point a ∼[ ε ] point b →
    MetricSpace.Close 𝓜 a ε b
  pointReflecting =
    close→computed


  module UniformlyContinuousCompletionExtension
    (μ : PrecisionModulus)
    (μ-completion : CompletionPrecisionModulus μ)
    (𝓝 : MetricSpace ℓᵗ ℓᵗ')
    (complete : MetricComplete.IsComplete 𝓝)
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
    (complete : MetricComplete.IsComplete 𝓝)
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


  toCauchyApproximation :
    MetricComplete.CauchyApproximation CauchyCompletionMetricSpace →
    CauchyApproximation
  toCauchyApproximation x =
    cauchy-approximation
      (MetricComplete.CauchyApproximation.approximate x)
      (MetricComplete.CauchyApproximation.isRegular x)


  isComplete :
    MetricComplete.IsComplete CauchyCompletionMetricSpace
  isComplete x =
    MetricComplete.cauchy-limit
      (limit xᶜ)
      λ ε δ δ<ε →
        limit-close-intro xᶜ (MetricComplete.CauchyApproximation.approximate x δ)
          ε δ δ<ε
          (close-refl
            (MetricComplete.CauchyApproximation.approximate x δ)
            (ε ⊖ δ [ δ<ε ]))
    where
    xᶜ : CauchyApproximation
    xᶜ = toCauchyApproximation x
