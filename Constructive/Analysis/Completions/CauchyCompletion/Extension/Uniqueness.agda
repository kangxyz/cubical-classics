{-

Density and uniqueness for maps out of a Cauchy completion

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Completions.CauchyCompletion.Extension.Uniqueness where

open import Cubical.Foundations.Prelude

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Map
open import Constructive.Analysis.Completions.CauchyCompletion.Base
open import Constructive.Analysis.Completions.CauchyCompletion.Closeness.Computed
open import Constructive.Analysis.Completions.CauchyCompletion.Closeness.ReflexiveSymmetric
open import Constructive.Analysis.Completions.CauchyCompletion.Induction
open import Constructive.Analysis.Completions.CauchyCompletion.Metric
open import Constructive.Data.PositiveRationals

private
  variable
    ℓ ℓ' ℓᵗ ℓᵗ' : Level


module UniquenessOf (𝓜 : MetricSpace ℓ ℓ') where
  open CompletionOf 𝓜
  open ClosenessOf 𝓜
  open ComputedOf 𝓜
    using (close→computed ; computed→close ; targetLimitIntro)
  open InductionOf 𝓜
  open MetricSpaceOf 𝓜

  private
    ℓᶜ : Level
    ℓᶜ = ℓ-max ℓ ℓ'


  close-limit-intro :
    (x : Completion) (y : CauchyApproximation) (ε δ : ℚ⁺) →
    (δ<ε : δ <⁺ ε) →
    x ∼[ ε ⊖ δ [ δ<ε ] ] approximate y δ →
    x ∼[ ε ] limit y
  close-limit-intro x y ε δ δ<ε =
    λ x∼yδ →
      computed→close x (limit y) ε
        (targetLimitIntro x y ε δ δ<ε (close→computed x∼yδ))


  limit-close-intro :
    (x : CauchyApproximation) (y : Completion) (ε δ : ℚ⁺) →
    (δ<ε : δ <⁺ ε) →
    approximate x δ ∼[ ε ⊖ δ [ δ<ε ] ] y →
    limit x ∼[ ε ] y
  limit-close-intro x y ε δ δ<ε xδ∼y =
    close-sym (close-limit-intro y x ε δ δ<ε (close-sym xδ∼y))


  limit-limit-intro :
    (x y : CauchyApproximation) (ε δ η : ℚ⁺) →
    (δ+η<ε : δ +⁺ η <⁺ ε) →
    approximate x δ ∼[ ε ⊖ (δ +⁺ η) [ δ+η<ε ] ] approximate y η →
    limit x ∼[ ε ] limit y
  limit-limit-intro =
    limit-limit-close


  limit-approx-close :
    (x : CauchyApproximation) (ε : ℚ⁺) →
    limit x ∼[ ε ] approximate x (quarter⁺ ε)
  limit-approx-close x ε =
    limit-close-intro x (approximate x δ) ε δ δ<ε
      (close-refl (approximate x δ) (ε ⊖ δ [ δ<ε ]))
    where
    δ : ℚ⁺
    δ = quarter⁺ ε

    δ<ε : δ <⁺ ε
    δ<ε = quarter< ε


  uniformlyContinuous-equal :
    (𝓝 : MetricSpace ℓᵗ ℓᵗ') →
    (f g : Completion → MetricSpace.Carrier 𝓝) →
    IsUniformlyContinuous CauchyCompletionMetricSpace 𝓝 f →
    IsUniformlyContinuous CauchyCompletionMetricSpace 𝓝 g →
    ((a : MetricSpace.Carrier 𝓜) → f (point a) ≡ g (point a)) →
    (x : Completion) →
    f x ≡ g x
  uniformlyContinuous-equal {ℓᵗ = ℓᵗ} 𝓝 f g
    (μ , f-cont) (ν , g-cont) point-path =
    PropInduction.ind kit
    where
    kit : PropInductionKit ℓᵗ
    kit .PropInductionKit.A x =
      f x ≡ g x
    kit .PropInductionKit.isPropA x =
      MetricSpace.isSetCarrier 𝓝 (f x) (g x)
    kit .PropInductionKit.point* =
      point-path
    kit .PropInductionKit.limit* x pointwise =
      MetricSpace.close-separated 𝓝 (f (limit x)) (g (limit x)) closeAt
      where
      closeAt :
        (ε : ℚ⁺) →
        MetricSpace.Close 𝓝 (f (limit x)) ε (g (limit x))
      closeAt ε =
        MetricSpace.close-mono 𝓝 {ε = (α +⁺ α) +⁺ α} {δ = ε}
          (three-quarter< ε)
          (MetricSpace.close-triangle 𝓝
            (MetricSpace.close-triangle 𝓝 f-lim∼approx f-approx∼g-approx)
            g-approx∼lim)
        where
        α : ℚ⁺
        α = quarter⁺ ε

        σ : ℚ⁺
        σ = half⁺ (min⁺ (μ α) (ν α))

        δ : ℚ⁺
        δ = quarter⁺ σ

        lim∼approx :
          limit x ∼[ σ ] approximate x δ
        lim∼approx =
          limit-approx-close x σ

        lim∼approx-f :
          limit x ∼[ μ α ] approximate x δ
        lim∼approx-f =
          close-mono (half-min⁺<left (μ α) (ν α)) lim∼approx

        lim∼approx-g :
          limit x ∼[ ν α ] approximate x δ
        lim∼approx-g =
          close-mono (half-min⁺<right (μ α) (ν α)) lim∼approx

        f-lim∼approx :
          MetricSpace.Close 𝓝 (f (limit x)) α (f (approximate x δ))
        f-lim∼approx =
          f-cont α lim∼approx-f

        f-approx∼g-approx :
          MetricSpace.Close 𝓝
            (f (approximate x δ)) α (g (approximate x δ))
        f-approx∼g-approx =
          subst
            (λ y → MetricSpace.Close 𝓝 (f (approximate x δ)) α y)
            (pointwise δ)
            (MetricSpace.close-refl 𝓝 (f (approximate x δ)) α)

        g-approx∼lim :
          MetricSpace.Close 𝓝 (g (approximate x δ)) α (g (limit x))
        g-approx∼lim =
          g-cont α (close-sym lim∼approx-g)


  nonexpanding-equal :
    (𝓝 : MetricSpace ℓᵗ ℓᵗ') →
    (f g : Completion → MetricSpace.Carrier 𝓝) →
    IsNonexpanding CauchyCompletionMetricSpace 𝓝 f →
    IsNonexpanding CauchyCompletionMetricSpace 𝓝 g →
    ((a : MetricSpace.Carrier 𝓜) → f (point a) ≡ g (point a)) →
    (x : Completion) →
    f x ≡ g x
  nonexpanding-equal 𝓝 f g f-ne g-ne =
    uniformlyContinuous-equal 𝓝 f g
      (nonexpanding→uniformlyContinuous
        {𝓧 = CauchyCompletionMetricSpace} {𝓨 = 𝓝} {f = f} f-ne)
      (nonexpanding→uniformlyContinuous
        {𝓧 = CauchyCompletionMetricSpace} {𝓨 = 𝓝} {f = g} g-ne)


  lipschitz-equal :
    (𝓝 : MetricSpace ℓᵗ ℓᵗ') →
    (f g : Completion → MetricSpace.Carrier 𝓝) →
    IsLipschitz CauchyCompletionMetricSpace 𝓝 f →
    IsLipschitz CauchyCompletionMetricSpace 𝓝 g →
    ((a : MetricSpace.Carrier 𝓜) → f (point a) ≡ g (point a)) →
    (x : Completion) →
    f x ≡ g x
  lipschitz-equal 𝓝 f g f-lip g-lip =
    uniformlyContinuous-equal 𝓝 f g
      (lipschitz→uniformlyContinuous
        {𝓧 = CauchyCompletionMetricSpace} {𝓨 = 𝓝} {f = f} f-lip)
      (lipschitz→uniformlyContinuous
        {𝓧 = CauchyCompletionMetricSpace} {𝓨 = 𝓝} {f = g} g-lip)
