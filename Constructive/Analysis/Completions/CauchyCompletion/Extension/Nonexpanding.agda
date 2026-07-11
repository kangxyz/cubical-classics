{-

Nonexpanding extension into complete metric spaces

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Completions.CauchyCompletion.Extension.Nonexpanding where

open import Cubical.Foundations.Prelude

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Map
import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Completions.CauchyCompletion.Base
open import Constructive.Analysis.Completions.CauchyCompletion.Closeness.ReflexiveSymmetric
open import Constructive.Analysis.Completions.CauchyCompletion.Extension.Target
open import Constructive.Analysis.Completions.CauchyCompletion.Extension.Uniqueness
open import Constructive.Analysis.Completions.CauchyCompletion.Metric
open import Constructive.Analysis.Completions.CauchyCompletion.Recursion
open import Constructive.Data.PositiveRationals

private
  variable
    ℓ ℓ' ℓᵗ ℓᵗ' : Level

module NonexpandingExtensionOf (𝓜 : MetricSpace ℓ ℓ') where
  open CompletionOf 𝓜
  open RecursionOf 𝓜
  open ClosenessOf 𝓜
  open MetricSpaceOf 𝓜
  open UniquenessOf 𝓜

  module NonexpandingExtension
    (𝓝 : MetricSpace ℓᵗ ℓᵗ')
    (complete : MetricCauchy.IsCauchyComplete 𝓝)
    (f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓝)
    (f-ne : IsNonexpanding 𝓜 𝓝 f)
    where
    open CompleteTargetOf 𝓝 complete

    private
      targetApproximation :
        (g : ℚ⁺ → MetricSpace.Carrier 𝓝) →
        ((ε δ : ℚ⁺) → MetricSpace.Close 𝓝 (g ε) (ε +⁺ δ) (g δ)) →
        MetricCauchy.CauchyApproximation 𝓝
      targetApproximation =
        MetricCauchy.cauchy-approximation

      extensionKit : RecursionKit ℓᵗ ℓᵗ'
      extensionKit .RecursionKit.A =
        MetricSpace.Carrier 𝓝
      extensionKit .RecursionKit.B ε x y =
        MetricSpace.Close 𝓝 x ε y
      extensionKit .RecursionKit.isPropB ε x y =
        MetricSpace.isPropClose 𝓝 x y ε
      extensionKit .RecursionKit.separated =
        MetricSpace.close-separated 𝓝
      extensionKit .RecursionKit.point* =
        f
      extensionKit .RecursionKit.limit* x g gCauchy =
        targetLimit (targetApproximation g gCauchy)
      extensionKit .RecursionKit.point-point* a b ε a∼b =
        f-ne a∼b
      extensionKit .RecursionKit.point-limit* a ε δ δ<ε y g gCauchy =
        close-limit-target
          (f a) (targetApproximation g gCauchy) ε δ δ<ε
      extensionKit .RecursionKit.limit-point* x g gCauchy b ε δ δ<ε =
        limit-close-target
          (targetApproximation g gCauchy) (f b) ε δ δ<ε
      extensionKit .RecursionKit.limit-limit* x y g h gCauchy hCauchy ε δ η δ+η<ε =
        limit-limit-target
          (targetApproximation g gCauchy)
          (targetApproximation h hCauchy)
          ε δ η δ+η<ε

      module ExtensionRecursion = Recursion extensionKit

    extend : Completion → MetricSpace.Carrier 𝓝
    extend =
      ExtensionRecursion.rec


    extend-point :
      (a : MetricSpace.Carrier 𝓜) →
      extend (point a) ≡ f a
    extend-point a =
      refl


    extend-close :
      IsNonexpanding CauchyCompletionMetricSpace 𝓝 extend
    extend-close =
      ExtensionRecursion.rec-close


    extend-unique :
      (g : Completion → MetricSpace.Carrier 𝓝) →
      IsNonexpanding CauchyCompletionMetricSpace 𝓝 g →
      ((a : MetricSpace.Carrier 𝓜) → g (point a) ≡ f a) →
      (x : Completion) →
      g x ≡ extend x
    extend-unique g g-ne point-path =
      nonexpanding-equal 𝓝 g extend g-ne extend-close point-path
