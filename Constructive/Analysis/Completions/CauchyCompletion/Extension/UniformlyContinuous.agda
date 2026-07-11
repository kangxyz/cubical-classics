{-

Uniformly continuous extension into complete metric spaces

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Completions.CauchyCompletion.Extension.UniformlyContinuous where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
  using (isPropΠ)

import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Map
import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Completions.CauchyCompletion.Base
open import Constructive.Analysis.Completions.CauchyCompletion.Closeness.ReflexiveSymmetric
open import Constructive.Analysis.Completions.CauchyCompletion.Extension.Precision
open import Constructive.Analysis.Completions.CauchyCompletion.Extension.Uniqueness
open import Constructive.Analysis.Completions.CauchyCompletion.Metric
open import Constructive.Analysis.Completions.CauchyCompletion.Recursion
open import Constructive.Data.PositiveRationals

private
  variable
    ℓ ℓ' ℓᵗ ℓᵗ' : Level


module UniformlyContinuousExtensionOf (𝓜 : MetricSpace ℓ ℓ') where
  open CompletionOf 𝓜
  open RecursionOf 𝓜
  open ClosenessOf 𝓜
  open MetricSpaceOf 𝓜
  open UniquenessOf 𝓜

  module UniformlyContinuousExtension
    (μ : PrecisionModulus)
    (μ-completion : CompletionPrecisionModulus μ)
    (𝓝 : MetricSpace ℓᵗ ℓᵗ')
    (complete : MetricCauchy.IsCauchyComplete 𝓝)
    (f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓝)
    (f-cont : IsUniformlyContinuousWith 𝓜 𝓝 μ f)
    where

    private
      ν : PrecisionModulus
      ν =
        CompletionPrecisionModulus.limitPrecisionModulus μ-completion

      ν-regular :
        (ε δ : ℚ⁺) →
        radius (ν ε +⁺ ν δ) ℚOrder.≤ radius (μ (ε +⁺ δ))
      ν-regular =
        CompletionPrecisionModulus.limitPrecisionRegular μ-completion

      pointLimitSplit :
        (ε δ θ : ℚ⁺) →
        (δ<ε : δ <⁺ ε) →
        radius ε ℚOrder.≤ radius (μ θ) →
        PointLimitSplit μ ν ε δ θ δ<ε
      pointLimitSplit =
        CompletionPrecisionModulus.pointLimitSplit μ-completion

      limitLimitSplit :
        (ε δ η θ : ℚ⁺) →
        (δ+η<ε : δ +⁺ η <⁺ ε) →
        radius ε ℚOrder.≤ radius (μ θ) →
        LimitLimitSplit μ ν ε δ η θ δ+η<ε
      limitLimitSplit =
        CompletionPrecisionModulus.limitLimitSplit μ-completion

      TargetClose :
        ℚ⁺ →
        MetricSpace.Carrier 𝓝 →
        MetricSpace.Carrier 𝓝 →
        Type ℓᵗ'
      TargetClose ε y z =
        (θ : ℚ⁺) →
        radius ε ℚOrder.≤ radius (μ θ) →
        MetricSpace.Close 𝓝 y θ z

      targetApproximation :
        (g : ℚ⁺ → MetricSpace.Carrier 𝓝) →
        ((ε δ : ℚ⁺) → TargetClose (ε +⁺ δ) (g ε) (g δ)) →
        MetricCauchy.CauchyApproximation 𝓝
      targetApproximation g gCauchy =
        MetricCauchy.cauchy-approximation
          (λ ε → g (ν ε))
          (λ ε δ → gCauchy (ν ε) (ν δ) (ε +⁺ δ) (ν-regular ε δ))

      targetLimit :
        (g : ℚ⁺ → MetricSpace.Carrier 𝓝) →
        (gCauchy : (ε δ : ℚ⁺) → TargetClose (ε +⁺ δ) (g ε) (g δ)) →
        MetricSpace.Carrier 𝓝
      targetLimit g gCauchy =
        MetricCauchy.limitPoint (complete (targetApproximation g gCauchy))

      targetConverges :
        (g : ℚ⁺ → MetricSpace.Carrier 𝓝) →
        (gCauchy : (ε δ : ℚ⁺) → TargetClose (ε +⁺ δ) (g ε) (g δ)) →
        MetricCauchy.ConvergesTo
          (targetApproximation g gCauchy)
          (targetLimit g gCauchy)
      targetConverges g gCauchy =
        MetricCauchy.converges (complete (targetApproximation g gCauchy))

      point-limit-close-target :
        (a : MetricSpace.Carrier 𝓜) (ε δ : ℚ⁺) →
        (δ<ε : δ <⁺ ε) →
        (g : ℚ⁺ → MetricSpace.Carrier 𝓝) →
        (gCauchy : (θ η : ℚ⁺) → TargetClose (θ +⁺ η) (g θ) (g η)) →
        TargetClose (ε ⊖ δ [ δ<ε ]) (f a) (g δ) →
        TargetClose ε (f a) (targetLimit g gCauchy)
      point-limit-close-target a ε δ δ<ε g gCauchy a∼gδ θ ε≤μθ =
        MetricCauchy.close-mono-≤ 𝓝
          (PointLimitSplit.pointLimitTotal≤ split)
          (MetricSpace.close-triangle 𝓝
            (MetricSpace.close-triangle 𝓝 a∼gδ' gδ∼gνι)
            gνι∼lim)
        where
        split : PointLimitSplit μ ν ε δ θ δ<ε
        split =
          pointLimitSplit ε δ θ δ<ε ε≤μθ

        ι : ℚ⁺
        ι =
          PointLimitSplit.limitIndex split

        α : ℚ⁺
        α =
          PointLimitSplit.pointPrecision split

        β : ℚ⁺
        β =
          PointLimitSplit.bridgePrecision split

        γ : ℚ⁺
        γ =
          PointLimitSplit.limitPrecision split

        a∼gδ' :
          MetricSpace.Close 𝓝 (f a) α (g δ)
        a∼gδ' =
          a∼gδ α (PointLimitSplit.pointSource≤ split)

        gδ∼gνι :
          MetricSpace.Close 𝓝 (g δ) β (g (ν ι))
        gδ∼gνι =
          gCauchy δ (ν ι) β (PointLimitSplit.bridgeSource≤ split)

        gνι∼lim :
          MetricSpace.Close 𝓝 (g (ν ι)) γ (targetLimit g gCauchy)
        gνι∼lim =
          MetricSpace.close-sym 𝓝
            (targetConverges g gCauchy
              γ
              ι
              (PointLimitSplit.limitIndex<limitPrecision split))

      limit-point-close-target :
        (g : ℚ⁺ → MetricSpace.Carrier 𝓝) →
        (gCauchy : (θ η : ℚ⁺) → TargetClose (θ +⁺ η) (g θ) (g η)) →
        (b : MetricSpace.Carrier 𝓜) (ε δ : ℚ⁺) →
        (δ<ε : δ <⁺ ε) →
        TargetClose (ε ⊖ δ [ δ<ε ]) (g δ) (f b) →
        TargetClose ε (targetLimit g gCauchy) (f b)
      limit-point-close-target g gCauchy b ε δ δ<ε gδ∼b θ ε≤μθ =
        MetricSpace.close-sym 𝓝
          (point-limit-close-target b ε δ δ<ε g gCauchy
            (λ α gap≤μα → MetricSpace.close-sym 𝓝 (gδ∼b α gap≤μα))
            θ
            ε≤μθ)

      limit-limit-close-target :
        (g h : ℚ⁺ → MetricSpace.Carrier 𝓝) →
        (gCauchy : (θ η : ℚ⁺) → TargetClose (θ +⁺ η) (g θ) (g η)) →
        (hCauchy : (θ η : ℚ⁺) → TargetClose (θ +⁺ η) (h θ) (h η)) →
        (ε δ η : ℚ⁺) →
        (δ+η<ε : δ +⁺ η <⁺ ε) →
        TargetClose (ε ⊖ (δ +⁺ η) [ δ+η<ε ]) (g δ) (h η) →
        TargetClose ε (targetLimit g gCauchy) (targetLimit h hCauchy)
      limit-limit-close-target g h gCauchy hCauchy ε δ η δ+η<ε gδ∼hη θ ε≤μθ =
        MetricCauchy.close-mono-≤ 𝓝
          (LimitLimitSplit.limitLimitTotal≤ split)
          (MetricSpace.close-triangle 𝓝
            (MetricSpace.close-triangle 𝓝
              (MetricSpace.close-triangle 𝓝
                (MetricSpace.close-triangle 𝓝 lim∼gνι gνι∼gδ)
                gδ∼hη')
              hη∼hνκ)
            hνκ∼lim)
        where
        split : LimitLimitSplit μ ν ε δ η θ δ+η<ε
        split =
          limitLimitSplit ε δ η θ δ+η<ε ε≤μθ

        ι : ℚ⁺
        ι =
          LimitLimitSplit.leftIndex split

        κ : ℚ⁺
        κ =
          LimitLimitSplit.rightIndex split

        lim∼gνι :
          MetricSpace.Close 𝓝
            (targetLimit g gCauchy)
            (LimitLimitSplit.leftPrecision split)
            (g (ν ι))
        lim∼gνι =
          targetConverges g gCauchy
            (LimitLimitSplit.leftPrecision split)
            ι
            (LimitLimitSplit.leftIndex<leftPrecision split)

        gνι∼gδ :
          MetricSpace.Close 𝓝
            (g (ν ι))
            (LimitLimitSplit.leftBridgePrecision split)
            (g δ)
        gνι∼gδ =
          gCauchy
            (ν ι)
            δ
            (LimitLimitSplit.leftBridgePrecision split)
            (LimitLimitSplit.leftBridgeSource≤ split)

        gδ∼hη' :
          MetricSpace.Close 𝓝
            (g δ)
            (LimitLimitSplit.middlePrecision split)
            (h η)
        gδ∼hη' =
          gδ∼hη
            (LimitLimitSplit.middlePrecision split)
            (LimitLimitSplit.middleSource≤ split)

        hη∼hνκ :
          MetricSpace.Close 𝓝
            (h η)
            (LimitLimitSplit.rightBridgePrecision split)
            (h (ν κ))
        hη∼hνκ =
          hCauchy
            η
            (ν κ)
            (LimitLimitSplit.rightBridgePrecision split)
            (LimitLimitSplit.rightBridgeSource≤ split)

        hνκ∼lim :
          MetricSpace.Close 𝓝
            (h (ν κ))
            (LimitLimitSplit.rightPrecision split)
            (targetLimit h hCauchy)
        hνκ∼lim =
          MetricSpace.close-sym 𝓝
            (targetConverges h hCauchy
              (LimitLimitSplit.rightPrecision split)
              κ
              (LimitLimitSplit.rightIndex<rightPrecision split))

      extensionKit : RecursionKit ℓᵗ ℓᵗ'
      extensionKit .RecursionKit.A =
        MetricSpace.Carrier 𝓝
      extensionKit .RecursionKit.B =
        TargetClose
      extensionKit .RecursionKit.isPropB ε x y =
        isPropΠ λ θ →
          isPropΠ λ _ →
            MetricSpace.isPropClose 𝓝 x y θ
      extensionKit .RecursionKit.separated x y closeAt =
        MetricSpace.close-separated 𝓝 x y λ θ →
          closeAt (μ θ) θ (ℚOrder.isRefl≤ (radius (μ θ)))
      extensionKit .RecursionKit.point* =
        f
      extensionKit .RecursionKit.limit* x g gCauchy =
        targetLimit g gCauchy
      extensionKit .RecursionKit.point-point* a b ε a∼b θ ε≤μθ =
        f-cont θ (MetricCauchy.close-mono-≤ 𝓜 ε≤μθ a∼b)
      extensionKit .RecursionKit.point-limit* a ε δ δ<ε y g gCauchy =
        point-limit-close-target a ε δ δ<ε g gCauchy
      extensionKit .RecursionKit.limit-point* x g gCauchy b ε δ δ<ε =
        limit-point-close-target g gCauchy b ε δ δ<ε
      extensionKit .RecursionKit.limit-limit* x y g h gCauchy hCauchy ε δ η δ+η<ε =
        limit-limit-close-target g h gCauchy hCauchy ε δ η δ+η<ε

      module ExtensionRecursion = Recursion extensionKit

    extend : Completion → MetricSpace.Carrier 𝓝
    extend =
      ExtensionRecursion.rec


    extend-point :
      (a : MetricSpace.Carrier 𝓜) →
      extend (point a) ≡ f a
    extend-point a =
      refl


    private
      extend-related :
        {x y : Completion} {ε : ℚ⁺} →
        x ∼[ ε ] y →
        (θ : ℚ⁺) →
        radius ε ℚOrder.≤ radius (μ θ) →
        MetricSpace.Close 𝓝 (extend x) θ (extend y)
      extend-related =
        ExtensionRecursion.rec-close

    extend-continuousWith :
      IsUniformlyContinuousWith CauchyCompletionMetricSpace 𝓝 μ extend
    extend-continuousWith ε x∼y =
      extend-related x∼y ε (ℚOrder.isRefl≤ (radius (μ ε)))


    extend-unique :
      (g : Completion → MetricSpace.Carrier 𝓝) →
      IsUniformlyContinuousWith CauchyCompletionMetricSpace 𝓝 μ g →
      ((a : MetricSpace.Carrier 𝓜) → g (point a) ≡ f a) →
      (x : Completion) →
      g x ≡ extend x
    extend-unique g g-cont point-path =
      uniformlyContinuous-equal 𝓝 g extend
        (μ , g-cont)
        (μ , extend-continuousWith)
        point-path
