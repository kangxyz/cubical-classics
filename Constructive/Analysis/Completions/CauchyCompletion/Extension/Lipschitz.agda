{-

Lipschitz extension into complete metric spaces

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Completions.CauchyCompletion.Extension.Lipschitz where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
  using (ℚCommRing)
open import Cubical.Tactics.CommRingSolver.Reflection

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

  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    scale-diff-positive :
      (κ ε δ : 𝓡 .fst) →
      (κ · ε) - (κ · δ) ≡ κ · (ε - δ)
    scale-diff-positive _ _ _ = solve! 𝓡

    scale-diff-sum :
      (κ ε δ η : 𝓡 .fst) →
      (κ · ε) - ((κ · δ) + (κ · η)) ≡ κ · (ε - (δ + η))
    scale-diff-sum _ _ _ _ = solve! 𝓡


module LipschitzExtensionOf (𝓜 : MetricSpace ℓ ℓ') where
  open CompletionOf 𝓜
  open RecursionOf 𝓜
  open ClosenessOf 𝓜
  open MetricSpaceOf 𝓜
  open UniquenessOf 𝓜

  private
    scale-precision-sum-cancel :
      (κ ε δ : ℚ⁺) →
      κ *⁺ ((posInv⁺ κ *⁺ ε) +⁺ (posInv⁺ κ *⁺ δ)) ≡ ε +⁺ δ
    scale-precision-sum-cancel κ ε δ =
      *⁺-distrib-left κ (posInv⁺ κ *⁺ ε) (posInv⁺ κ *⁺ δ) ∙
      cong₂ _+⁺_
        (scale-posInv-cancel κ ε)
        (scale-posInv-cancel κ δ)

    scale-precision-difference :
      (κ ε δ : ℚ⁺) →
      (δ<ε : δ <⁺ ε) →
      (κδ<κε : κ *⁺ δ <⁺ κ *⁺ ε) →
      (κ *⁺ ε) ⊖ (κ *⁺ δ) [ κδ<κε ] ≡
      κ *⁺ (ε ⊖ δ [ δ<ε ])
    scale-precision-difference κ ε δ δ<ε κδ<κε =
      ℚ⁺Path
        (SolverHelpers.scale-diff-positive ℚCommRing
          (radius κ) (radius ε) (radius δ))

    scale-precision-sum< :
      (κ ε δ η : ℚ⁺) →
      δ +⁺ η <⁺ ε →
      (κ *⁺ δ) +⁺ (κ *⁺ η) <⁺ κ *⁺ ε
    scale-precision-sum< κ ε δ η δ+η<ε =
      subst
        (λ ρ → ρ <⁺ κ *⁺ ε)
        (*⁺-distrib-left κ δ η)
        (scale-mono-< κ (δ +⁺ η) ε δ+η<ε)

    scale-precision-sum-difference :
      (κ ε δ η : ℚ⁺) →
      (δ+η<ε : δ +⁺ η <⁺ ε) →
      (κδη<κε : (κ *⁺ δ) +⁺ (κ *⁺ η) <⁺ κ *⁺ ε) →
      (κ *⁺ ε) ⊖ ((κ *⁺ δ) +⁺ (κ *⁺ η)) [ κδη<κε ] ≡
      κ *⁺ (ε ⊖ (δ +⁺ η) [ δ+η<ε ])
    scale-precision-sum-difference κ ε δ η δ+η<ε κδη<κε =
      ℚ⁺Path
        (SolverHelpers.scale-diff-sum ℚCommRing
          (radius κ) (radius ε) (radius δ) (radius η))

  module LipschitzExtension
    (κ : ℚ⁺)
    (𝓝 : MetricSpace ℓᵗ ℓᵗ')
    (complete : MetricCauchy.IsCauchyComplete 𝓝)
    (f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓝)
    (f-lip : IsLipschitzWith 𝓜 𝓝 κ f)
    where
    open CompleteTargetOf 𝓝 complete

    private
      scaledTargetApproximation :
        (g : ℚ⁺ → MetricSpace.Carrier 𝓝) →
        ((ε δ : ℚ⁺) → MetricSpace.Close 𝓝 (g ε) (κ *⁺ (ε +⁺ δ)) (g δ)) →
        MetricCauchy.CauchyApproximation 𝓝
      scaledTargetApproximation g gCauchy =
        MetricCauchy.cauchy-approximation h hCauchy
        where
        h : ℚ⁺ → MetricSpace.Carrier 𝓝
        h ε =
          g (posInv⁺ κ *⁺ ε)

        hCauchy :
          (ε δ : ℚ⁺) →
          MetricSpace.Close 𝓝 (h ε) (ε +⁺ δ) (h δ)
        hCauchy ε δ =
          subst
            (λ ρ → MetricSpace.Close 𝓝 (h ε) ρ (h δ))
            (scale-precision-sum-cancel κ ε δ)
            (gCauchy (posInv⁺ κ *⁺ ε) (posInv⁺ κ *⁺ δ))

      extensionKit : RecursionKit ℓᵗ ℓᵗ'
      extensionKit .RecursionKit.A =
        MetricSpace.Carrier 𝓝
      extensionKit .RecursionKit.B ε x y =
        MetricSpace.Close 𝓝 x (κ *⁺ ε) y
      extensionKit .RecursionKit.isPropB ε x y =
        MetricSpace.isPropClose 𝓝 x y (κ *⁺ ε)
      extensionKit .RecursionKit.separated x y closeAt =
        MetricSpace.close-separated 𝓝 x y λ ε →
          subst
            (λ ρ → MetricSpace.Close 𝓝 x ρ y)
            (scale-posInv-cancel κ ε)
            (closeAt (posInv⁺ κ *⁺ ε))
      extensionKit .RecursionKit.point* =
        f
      extensionKit .RecursionKit.limit* x g gCauchy =
        targetLimit (scaledTargetApproximation g gCauchy)
      extensionKit .RecursionKit.point-point* =
        f-lip
      extensionKit .RecursionKit.point-limit* a ε δ δ<ε y g gCauchy a∼gδ =
        close-limit-target
          (f a)
          (scaledTargetApproximation g gCauchy)
          (κ *⁺ ε)
          (κ *⁺ δ)
          κδ<κε
          a∼hκδ
        where
        κδ<κε : κ *⁺ δ <⁺ κ *⁺ ε
        κδ<κε =
          scale-mono-< κ δ ε δ<ε

        precisionPath :
          (κ *⁺ ε) ⊖ (κ *⁺ δ) [ κδ<κε ] ≡
          κ *⁺ (ε ⊖ δ [ δ<ε ])
        precisionPath =
          scale-precision-difference κ ε δ δ<ε κδ<κε

        indexPath : posInv⁺ κ *⁺ (κ *⁺ δ) ≡ δ
        indexPath =
          posInv-scale-cancel κ δ

        a∼hκδ :
          MetricSpace.Close 𝓝
            (f a)
            ((κ *⁺ ε) ⊖ (κ *⁺ δ) [ κδ<κε ])
            (MetricCauchy.approximate
              (scaledTargetApproximation g gCauchy)
              (κ *⁺ δ))
        a∼hκδ =
          subst2
            (λ ρ θ → MetricSpace.Close 𝓝 (f a) ρ (g θ))
            (sym precisionPath)
            (sym indexPath)
            a∼gδ
      extensionKit .RecursionKit.limit-point* x g gCauchy b ε δ δ<ε gδ∼b =
        limit-close-target
          (scaledTargetApproximation g gCauchy)
          (f b)
          (κ *⁺ ε)
          (κ *⁺ δ)
          κδ<κε
          hκδ∼b
        where
        κδ<κε : κ *⁺ δ <⁺ κ *⁺ ε
        κδ<κε =
          scale-mono-< κ δ ε δ<ε

        precisionPath :
          (κ *⁺ ε) ⊖ (κ *⁺ δ) [ κδ<κε ] ≡
          κ *⁺ (ε ⊖ δ [ δ<ε ])
        precisionPath =
          scale-precision-difference κ ε δ δ<ε κδ<κε

        indexPath : posInv⁺ κ *⁺ (κ *⁺ δ) ≡ δ
        indexPath =
          posInv-scale-cancel κ δ

        hκδ∼b :
          MetricSpace.Close 𝓝
            (MetricCauchy.approximate
              (scaledTargetApproximation g gCauchy)
              (κ *⁺ δ))
            ((κ *⁺ ε) ⊖ (κ *⁺ δ) [ κδ<κε ])
            (f b)
        hκδ∼b =
          subst2
            (λ θ ρ → MetricSpace.Close 𝓝 (g θ) ρ (f b))
            (sym indexPath)
            (sym precisionPath)
            gδ∼b
      extensionKit .RecursionKit.limit-limit* x y g h gCauchy hCauchy ε δ η δ+η<ε gδ∼hη =
        limit-limit-target
          (scaledTargetApproximation g gCauchy)
          (scaledTargetApproximation h hCauchy)
          (κ *⁺ ε)
          (κ *⁺ δ)
          (κ *⁺ η)
          κδη<κε
          gκδ∼hκη
        where
        κδη<κε : (κ *⁺ δ) +⁺ (κ *⁺ η) <⁺ κ *⁺ ε
        κδη<κε =
          scale-precision-sum< κ ε δ η δ+η<ε

        precisionPath :
          (κ *⁺ ε) ⊖ ((κ *⁺ δ) +⁺ (κ *⁺ η)) [ κδη<κε ] ≡
          κ *⁺ (ε ⊖ (δ +⁺ η) [ δ+η<ε ])
        precisionPath =
          scale-precision-sum-difference κ ε δ η δ+η<ε κδη<κε

        δIndexPath : posInv⁺ κ *⁺ (κ *⁺ δ) ≡ δ
        δIndexPath =
          posInv-scale-cancel κ δ

        ηIndexPath : posInv⁺ κ *⁺ (κ *⁺ η) ≡ η
        ηIndexPath =
          posInv-scale-cancel κ η

        neededPrecision : ℚ⁺
        neededPrecision =
          (κ *⁺ ε) ⊖ ((κ *⁺ δ) +⁺ (κ *⁺ η)) [ κδη<κε ]

        gδ∼hη-neededPrecision :
          MetricSpace.Close 𝓝 (g δ) neededPrecision (h η)
        gδ∼hη-neededPrecision =
          subst
            (λ ρ → MetricSpace.Close 𝓝 (g δ) ρ (h η))
            (sym precisionPath)
            gδ∼hη

        gδ∼hκη :
          MetricSpace.Close 𝓝
            (g δ)
            neededPrecision
            (MetricCauchy.approximate
              (scaledTargetApproximation h hCauchy)
              (κ *⁺ η))
        gδ∼hκη =
          subst
            (λ θ → MetricSpace.Close 𝓝 (g δ) neededPrecision (h θ))
            (sym ηIndexPath)
            gδ∼hη-neededPrecision

        gκδ∼hκη :
          MetricSpace.Close 𝓝
            (MetricCauchy.approximate
              (scaledTargetApproximation g gCauchy)
              (κ *⁺ δ))
            neededPrecision
            (MetricCauchy.approximate
              (scaledTargetApproximation h hCauchy)
              (κ *⁺ η))
        gκδ∼hκη =
          subst
            (λ θ →
              MetricSpace.Close 𝓝 (g θ) neededPrecision
                (MetricCauchy.approximate
                  (scaledTargetApproximation h hCauchy)
                  (κ *⁺ η)))
            (sym δIndexPath)
            gδ∼hκη

      module ExtensionRecursion = Recursion extensionKit

    extend : Completion → MetricSpace.Carrier 𝓝
    extend =
      ExtensionRecursion.rec


    extend-point :
      (a : MetricSpace.Carrier 𝓜) →
      extend (point a) ≡ f a
    extend-point a =
      refl


    extend-lipschitz :
      IsLipschitzWith CauchyCompletionMetricSpace 𝓝 κ extend
    extend-lipschitz _ _ _ x∼y =
      ExtensionRecursion.rec-close x∼y


    extend-unique :
      (g : Completion → MetricSpace.Carrier 𝓝) →
      IsLipschitzWith CauchyCompletionMetricSpace 𝓝 κ g →
      ((a : MetricSpace.Carrier 𝓜) → g (point a) ≡ f a) →
      (x : Completion) →
      g x ≡ extend x
    extend-unique g g-lip point-path =
      lipschitz-equal 𝓝 g extend
        (κ , g-lip)
        (κ , extend-lipschitz)
        point-path
