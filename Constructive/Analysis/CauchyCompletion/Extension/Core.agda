{-

Extension helpers for Cauchy completions

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.CauchyCompletion.Extension.Core where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
  using (isPropΠ)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
  using (ℚCommRing)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Tactics.CommRingSolver.Reflection

import Constructive.Data.Rationals as Rational
open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Map
import Constructive.Analysis.Metric.Cauchy as MetricComplete
open import Constructive.Analysis.CauchyCompletion.Base
open import Constructive.Analysis.CauchyCompletion.Closeness.ReflexiveSymmetric
open import Constructive.Analysis.CauchyCompletion.Closeness.Internal.Computed
open import Constructive.Analysis.CauchyCompletion.Closeness.Internal.Prelength
open import Constructive.Analysis.CauchyCompletion.Induction
open import Constructive.Analysis.CauchyCompletion.Recursion
open import Constructive.Data.PositiveRationals

private
  variable
    ℓ ℓ' ℓᵗ ℓᵗ' : Level

  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    point-limit-sum :
      (ε δ ζ : 𝓡 .fst) →
      ζ + (δ + ((ε - δ) - ζ)) ≡ ε
    point-limit-sum _ _ _ = solve! 𝓡

    limit-limit-rearrange :
      (δ η ζ κ : 𝓡 .fst) →
      ((δ + κ) + ζ) + (η + κ) ≡
      (δ + η) + (ζ + (κ + κ))
    limit-limit-rearrange _ _ _ _ = solve! 𝓡

    limit-limit-cancel :
      (ε δ η ζ : 𝓡 .fst) →
      (δ + η) + (ζ + ((ε - (δ + η)) - ζ)) ≡ ε
    limit-limit-cancel _ _ _ _ = solve! 𝓡

    scale-diff-positive :
      (κ ε δ : 𝓡 .fst) →
      (κ · ε) - (κ · δ) ≡ κ · (ε - δ)
    scale-diff-positive _ _ _ = solve! 𝓡

    scale-diff-sum :
      (κ ε δ η : 𝓡 .fst) →
      (κ · ε) - ((κ · δ) + (κ · η)) ≡ κ · (ε - (δ + η))
    scale-diff-sum _ _ _ _ = solve! 𝓡


module ExtensionOf (𝓜 : MetricSpace ℓ ℓ') where
  open CompletionOf 𝓜
  open InductionOf 𝓜
  open RecursionOf 𝓜
  open ClosenessOf 𝓜
  open ComputedOf 𝓜
    using (close→computed ; computed→close ; targetLimitIntro)
  open PrelengthOf 𝓜
    using (difference-from-sum<)

  private
    ℓᶜ : Level
    ℓᶜ = ℓ-max ℓ ℓ'

  close-limit-intro :
    (x : Completion) (y : CauchyApproximation) (ε δ : ℚ⁺) →
    (δ<ε : δ <⁺ ε) →
    x ∼[ ε ⊖ δ [ δ<ε ] ] approximate y δ →
    x ∼[ ε ] limit y
  close-limit-intro x y ε δ δ<ε x∼yδ =
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


  IsCompletionNonexpanding :
    (𝓝 : MetricSpace ℓᵗ ℓᵗ') →
    (Completion → MetricSpace.Carrier 𝓝) →
    Type (ℓ-max ℓᶜ ℓᵗ')
  IsCompletionNonexpanding 𝓝 f =
    {x y : Completion} {ε : ℚ⁺} →
    x ∼[ ε ] y →
    MetricSpace.Close 𝓝 (f x) ε (f y)


  IsScaledLipschitzWith :
    (κ : ℚ⁺) →
    (𝓝 : MetricSpace ℓᵗ ℓᵗ') →
    (MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓝) →
    Type (ℓ-max ℓ (ℓ-max ℓ' ℓᵗ'))
  IsScaledLipschitzWith κ 𝓝 f =
    (a b : MetricSpace.Carrier 𝓜) (ε : ℚ⁺) →
    MetricSpace.Close 𝓜 a ε b →
    MetricSpace.Close 𝓝 (f a) (κ *⁺ ε) (f b)


  IsCompletionScaledLipschitzWith :
    (κ : ℚ⁺) →
    (𝓝 : MetricSpace ℓᵗ ℓᵗ') →
    (Completion → MetricSpace.Carrier 𝓝) →
    Type (ℓ-max ℓᶜ ℓᵗ')
  IsCompletionScaledLipschitzWith κ 𝓝 f =
    {x y : Completion} {ε : ℚ⁺} →
    x ∼[ ε ] y →
    MetricSpace.Close 𝓝 (f x) (κ *⁺ ε) (f y)


  IsCompletionUniformlyContinuousWith :
    PrecisionModulus →
    (𝓝 : MetricSpace ℓᵗ ℓᵗ') →
    (Completion → MetricSpace.Carrier 𝓝) →
    Type (ℓ-max ℓᶜ ℓᵗ')
  IsCompletionUniformlyContinuousWith μ 𝓝 f =
    {x y : Completion} {ε : ℚ⁺} →
    x ∼[ ε ] y →
    (θ : ℚ⁺) →
    radius ε ℚOrder.≤ radius (μ θ) →
    MetricSpace.Close 𝓝 (f x) θ (f y)


  private
    scale-precision-cancel :
      (κ ε : ℚ⁺) →
      κ *⁺ (posInv⁺ κ *⁺ ε) ≡ ε
    scale-precision-cancel κ ε =
      sym (*⁺-assoc κ (posInv⁺ κ) ε) ∙
      cong (λ ρ → ρ *⁺ ε) (*⁺-posInv-right κ) ∙
      *⁺-identity-left ε

    scale-precision-cancel-left :
      (κ ε : ℚ⁺) →
      posInv⁺ κ *⁺ (κ *⁺ ε) ≡ ε
    scale-precision-cancel-left κ ε =
      sym (*⁺-assoc (posInv⁺ κ) κ ε) ∙
      cong (λ ρ → ρ *⁺ ε) (*⁺-posInv-left κ) ∙
      *⁺-identity-left ε

    scale-precision-sum-cancel :
      (κ ε δ : ℚ⁺) →
      κ *⁺ ((posInv⁺ κ *⁺ ε) +⁺ (posInv⁺ κ *⁺ δ)) ≡ ε +⁺ δ
    scale-precision-sum-cancel κ ε δ =
      *⁺-distrib-left κ (posInv⁺ κ *⁺ ε) (posInv⁺ κ *⁺ δ) ∙
      cong₂ _+⁺_
        (scale-precision-cancel κ ε)
        (scale-precision-cancel κ δ)

    scale-precision-mono :
      (κ ε δ : ℚ⁺) →
      ε <⁺ δ →
      κ *⁺ ε <⁺ κ *⁺ δ
    scale-precision-mono κ ε δ ε<δ =
      Rational.mul-left-positive-<
        {a = radius κ}
        {b = radius ε}
        {c = radius δ}
        (κ .snd)
        ε<δ

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
        (scale-precision-mono κ (δ +⁺ η) ε δ+η<ε)

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

    point-limit-sum :
      (ε δ ζ : ℚ⁺) →
      (δ<ε : δ <⁺ ε) →
      (ζ<ε-δ : ζ <⁺ ε ⊖ δ [ δ<ε ]) →
      ζ +⁺ (δ +⁺ ((ε ⊖ δ [ δ<ε ]) ⊖ ζ [ ζ<ε-δ ])) ≡ ε
    point-limit-sum ε δ ζ δ<ε ζ<ε-δ =
      ℚ⁺Path
        (SolverHelpers.point-limit-sum ℚCommRing
          (radius ε)
          (radius δ)
          (radius ζ))

    limit-limit-sum :
      (ε δ η ζ : ℚ⁺) →
      (δ+η<ε : δ +⁺ η <⁺ ε) →
      (ζ<ε-δη : ζ <⁺ ε ⊖ (δ +⁺ η) [ δ+η<ε ]) →
      let
        gap = (ε ⊖ (δ +⁺ η) [ δ+η<ε ]) ⊖ ζ [ ζ<ε-δη ]
        κ = half⁺ gap
      in
      (((δ +⁺ κ) +⁺ ζ) +⁺ (η +⁺ κ)) ≡ ε
    limit-limit-sum ε δ η ζ δ+η<ε ζ<ε-δη =
      ℚ⁺Path
        (SolverHelpers.limit-limit-rearrange ℚCommRing
          (radius δ)
          (radius η)
          (radius ζ)
          (radius κ) ∙
         cong
           (λ ρ → (radius δ ℚ.+ radius η) ℚ.+ (radius ζ ℚ.+ ρ))
           (cong radius (half⁺+half⁺≡ gap)) ∙
         SolverHelpers.limit-limit-cancel ℚCommRing
          (radius ε)
          (radius δ)
          (radius η)
          (radius ζ))
      where
      gap : ℚ⁺
      gap = (ε ⊖ (δ +⁺ η) [ δ+η<ε ]) ⊖ ζ [ ζ<ε-δη ]

      κ : ℚ⁺
      κ = half⁺ gap


  module NonexpandingExtension
    (𝓝 : MetricSpace ℓᵗ ℓᵗ')
    (complete : MetricComplete.IsComplete 𝓝)
    (f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓝)
    (f-ne : IsNonexpanding 𝓜 𝓝 f)
    where

    private
      targetApproximation :
        (g : ℚ⁺ → MetricSpace.Carrier 𝓝) →
        ((ε δ : ℚ⁺) → MetricSpace.Close 𝓝 (g ε) (ε +⁺ δ) (g δ)) →
        MetricComplete.CauchyApproximation 𝓝
      targetApproximation =
        MetricComplete.cauchy-approximation

      targetLimit :
        (g : ℚ⁺ → MetricSpace.Carrier 𝓝) →
        (gCauchy : (ε δ : ℚ⁺) → MetricSpace.Close 𝓝 (g ε) (ε +⁺ δ) (g δ)) →
        MetricSpace.Carrier 𝓝
      targetLimit g gCauchy =
        MetricComplete.limitPoint (complete (targetApproximation g gCauchy))

      targetConverges :
        (g : ℚ⁺ → MetricSpace.Carrier 𝓝) →
        (gCauchy : (ε δ : ℚ⁺) → MetricSpace.Close 𝓝 (g ε) (ε +⁺ δ) (g δ)) →
        MetricComplete.ConvergesTo (targetApproximation g gCauchy) (targetLimit g gCauchy)
      targetConverges g gCauchy =
        MetricComplete.converges (complete (targetApproximation g gCauchy))

      point-limit-close-target :
        (a : MetricSpace.Carrier 𝓜) (ε δ : ℚ⁺) →
        (δ<ε : δ <⁺ ε) →
        (g : ℚ⁺ → MetricSpace.Carrier 𝓝) →
        (gCauchy : (θ η : ℚ⁺) → MetricSpace.Close 𝓝 (g θ) (θ +⁺ η) (g η)) →
        MetricSpace.Close 𝓝 (f a) (ε ⊖ δ [ δ<ε ]) (g δ) →
        MetricSpace.Close 𝓝 (f a) ε (targetLimit g gCauchy)
      point-limit-close-target a ε δ δ<ε g gCauchy a∼gδ =
        Prop.rec
          (MetricSpace.isPropClose 𝓝 (f a) (targetLimit g gCauchy) ε)
          step
          (MetricSpace.close-rounded 𝓝 a∼gδ)
        where
        step :
          Σ[ ζ ∈ ℚ⁺ ]
            (ζ <⁺ ε ⊖ δ [ δ<ε ]) ×
            MetricSpace.Close 𝓝 (f a) ζ (g δ) →
          MetricSpace.Close 𝓝 (f a) ε (targetLimit g gCauchy)
        step (ζ , ζ<ε-δ , a∼gζ) =
          subst
            (λ ρ → MetricSpace.Close 𝓝 (f a) ρ (targetLimit g gCauchy))
            (point-limit-sum ε δ ζ δ<ε ζ<ε-δ)
            (MetricSpace.close-triangle 𝓝 a∼gζ gδ∼lim)
          where
          gap : ℚ⁺
          gap = (ε ⊖ δ [ δ<ε ]) ⊖ ζ [ ζ<ε-δ ]

          δ<δ+gap : δ <⁺ δ +⁺ gap
          δ<δ+gap = summand-left<sum δ gap

          gδ∼lim :
            MetricSpace.Close 𝓝 (g δ) (δ +⁺ gap) (targetLimit g gCauchy)
          gδ∼lim =
            MetricSpace.close-sym 𝓝
              (targetConverges g gCauchy (δ +⁺ gap) δ δ<δ+gap)

      limit-point-close-target :
        (g : ℚ⁺ → MetricSpace.Carrier 𝓝) →
        (gCauchy : (θ η : ℚ⁺) → MetricSpace.Close 𝓝 (g θ) (θ +⁺ η) (g η)) →
        (b : MetricSpace.Carrier 𝓜) (ε δ : ℚ⁺) →
        (δ<ε : δ <⁺ ε) →
        MetricSpace.Close 𝓝 (g δ) (ε ⊖ δ [ δ<ε ]) (f b) →
        MetricSpace.Close 𝓝 (targetLimit g gCauchy) ε (f b)
      limit-point-close-target g gCauchy b ε δ δ<ε gδ∼b =
        MetricSpace.close-sym 𝓝
          (point-limit-close-target b ε δ δ<ε g gCauchy
            (MetricSpace.close-sym 𝓝 gδ∼b))

      limit-limit-close-target :
        (g h : ℚ⁺ → MetricSpace.Carrier 𝓝) →
        (gCauchy : (θ η : ℚ⁺) → MetricSpace.Close 𝓝 (g θ) (θ +⁺ η) (g η)) →
        (hCauchy : (θ η : ℚ⁺) → MetricSpace.Close 𝓝 (h θ) (θ +⁺ η) (h η)) →
        (ε δ η : ℚ⁺) →
        (δ+η<ε : δ +⁺ η <⁺ ε) →
        MetricSpace.Close 𝓝 (g δ) (ε ⊖ (δ +⁺ η) [ δ+η<ε ]) (h η) →
        MetricSpace.Close 𝓝 (targetLimit g gCauchy) ε (targetLimit h hCauchy)
      limit-limit-close-target g h gCauchy hCauchy ε δ η δ+η<ε gδ∼hη =
        Prop.rec
          (MetricSpace.isPropClose 𝓝 (targetLimit g gCauchy) (targetLimit h hCauchy) ε)
          step
          (MetricSpace.close-rounded 𝓝 gδ∼hη)
        where
        step :
          Σ[ ζ ∈ ℚ⁺ ]
            (ζ <⁺ ε ⊖ (δ +⁺ η) [ δ+η<ε ]) ×
            MetricSpace.Close 𝓝 (g δ) ζ (h η) →
          MetricSpace.Close 𝓝 (targetLimit g gCauchy) ε (targetLimit h hCauchy)
        step (ζ , ζ<ε-δη , gδ∼hηζ) =
          subst
            (λ ρ → MetricSpace.Close 𝓝 (targetLimit g gCauchy) ρ (targetLimit h hCauchy))
            (limit-limit-sum ε δ η ζ δ+η<ε ζ<ε-δη)
            (MetricSpace.close-triangle 𝓝
              (MetricSpace.close-triangle 𝓝 lim∼gδ gδ∼hηζ)
              hη∼lim)
          where
          gap : ℚ⁺
          gap = (ε ⊖ (δ +⁺ η) [ δ+η<ε ]) ⊖ ζ [ ζ<ε-δη ]

          κ : ℚ⁺
          κ = half⁺ gap

          δ<δ+κ : δ <⁺ δ +⁺ κ
          δ<δ+κ = summand-left<sum δ κ

          η<η+κ : η <⁺ η +⁺ κ
          η<η+κ = summand-left<sum η κ

          lim∼gδ :
            MetricSpace.Close 𝓝 (targetLimit g gCauchy) (δ +⁺ κ) (g δ)
          lim∼gδ =
            targetConverges g gCauchy (δ +⁺ κ) δ δ<δ+κ

          hη∼lim :
            MetricSpace.Close 𝓝 (h η) (η +⁺ κ) (targetLimit h hCauchy)
          hη∼lim =
            MetricSpace.close-sym 𝓝
              (targetConverges h hCauchy (η +⁺ κ) η η<η+κ)

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
        targetLimit g gCauchy
      extensionKit .RecursionKit.point-point* a b ε a∼b =
        f-ne a∼b
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


    extend-close :
      IsCompletionNonexpanding 𝓝 extend
    extend-close =
      ExtensionRecursion.rec-close


    extend-nonexpanding :
      IsCompletionNonexpanding 𝓝 extend
    extend-nonexpanding =
      extend-close


    nonexpanding-equal :
      (g h : Completion → MetricSpace.Carrier 𝓝) →
      IsCompletionNonexpanding 𝓝 g →
      IsCompletionNonexpanding 𝓝 h →
      ((a : MetricSpace.Carrier 𝓜) → g (point a) ≡ h (point a)) →
      (x : Completion) →
      g x ≡ h x
    nonexpanding-equal g h g-ne h-ne point-path =
      PropInduction.ind kit
      where
      kit : PropInductionKit ℓᵗ
      kit .PropInductionKit.A x =
        g x ≡ h x
      kit .PropInductionKit.isPropA x =
        MetricSpace.isSetCarrier 𝓝 (g x) (h x)
      kit .PropInductionKit.point* =
        point-path
      kit .PropInductionKit.limit* x pointwise =
        MetricSpace.close-separated 𝓝 (g (limit x)) (h (limit x)) closeAt
        where
        closeAt : (ε : ℚ⁺) → MetricSpace.Close 𝓝 (g (limit x)) ε (h (limit x))
        closeAt ε =
          MetricSpace.close-mono 𝓝 {ε = (α +⁺ α) +⁺ α} {δ = ε}
            (three-quarter< ε)
            (MetricSpace.close-triangle 𝓝
              (MetricSpace.close-triangle 𝓝 g-lim∼approx g-approx∼h-approx)
              h-approx∼lim)
          where
          α : ℚ⁺
          α = quarter⁺ ε

          δ : ℚ⁺
          δ = quarter⁺ α

          lim∼approx : limit x ∼[ α ] approximate x δ
          lim∼approx =
            limit-approx-close x α

          g-lim∼approx :
            MetricSpace.Close 𝓝 (g (limit x)) α (g (approximate x δ))
          g-lim∼approx =
            g-ne lim∼approx

          g-approx∼h-approx :
            MetricSpace.Close 𝓝 (g (approximate x δ)) α (h (approximate x δ))
          g-approx∼h-approx =
            subst
              (λ y → MetricSpace.Close 𝓝 (g (approximate x δ)) α y)
              (pointwise δ)
              (MetricSpace.close-refl 𝓝 (g (approximate x δ)) α)

          h-approx∼lim :
            MetricSpace.Close 𝓝 (h (approximate x δ)) α (h (limit x))
          h-approx∼lim =
            h-ne (close-sym lim∼approx)


    extend-unique :
      (g : Completion → MetricSpace.Carrier 𝓝) →
      IsCompletionNonexpanding 𝓝 g →
      ((a : MetricSpace.Carrier 𝓜) → g (point a) ≡ f a) →
      (x : Completion) →
      g x ≡ extend x
    extend-unique g g-ne point-path =
      nonexpanding-equal g extend g-ne extend-nonexpanding point-path


  module UniformlyContinuousExtension
    (μ : PrecisionModulus)
    (μ-completion : CompletionPrecisionModulus μ)
    (𝓝 : MetricSpace ℓᵗ ℓᵗ')
    (complete : MetricComplete.IsComplete 𝓝)
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
        MetricComplete.CauchyApproximation 𝓝
      targetApproximation g gCauchy =
        MetricComplete.cauchy-approximation
          (λ ε → g (ν ε))
          (λ ε δ → gCauchy (ν ε) (ν δ) (ε +⁺ δ) (ν-regular ε δ))

      targetLimit :
        (g : ℚ⁺ → MetricSpace.Carrier 𝓝) →
        (gCauchy : (ε δ : ℚ⁺) → TargetClose (ε +⁺ δ) (g ε) (g δ)) →
        MetricSpace.Carrier 𝓝
      targetLimit g gCauchy =
        MetricComplete.limitPoint (complete (targetApproximation g gCauchy))

      targetConverges :
        (g : ℚ⁺ → MetricSpace.Carrier 𝓝) →
        (gCauchy : (ε δ : ℚ⁺) → TargetClose (ε +⁺ δ) (g ε) (g δ)) →
        MetricComplete.ConvergesTo
          (targetApproximation g gCauchy)
          (targetLimit g gCauchy)
      targetConverges g gCauchy =
        MetricComplete.converges (complete (targetApproximation g gCauchy))

      point-limit-close-target :
        (a : MetricSpace.Carrier 𝓜) (ε δ : ℚ⁺) →
        (δ<ε : δ <⁺ ε) →
        (g : ℚ⁺ → MetricSpace.Carrier 𝓝) →
        (gCauchy : (θ η : ℚ⁺) → TargetClose (θ +⁺ η) (g θ) (g η)) →
        TargetClose (ε ⊖ δ [ δ<ε ]) (f a) (g δ) →
        TargetClose ε (f a) (targetLimit g gCauchy)
      point-limit-close-target a ε δ δ<ε g gCauchy a∼gδ θ ε≤μθ =
        MetricComplete.close-mono-≤ 𝓝
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
        MetricComplete.close-mono-≤ 𝓝
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
        f-cont θ (MetricComplete.close-mono-≤ 𝓜 ε≤μθ a∼b)
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


    extend-close :
      IsCompletionUniformlyContinuousWith μ 𝓝 extend
    extend-close =
      ExtensionRecursion.rec-close


    extend-uniformlyContinuous :
      IsCompletionUniformlyContinuousWith μ 𝓝 extend
    extend-uniformlyContinuous =
      extend-close


    uniformlyContinuous-equal :
      (g h : Completion → MetricSpace.Carrier 𝓝) →
      IsCompletionUniformlyContinuousWith μ 𝓝 g →
      IsCompletionUniformlyContinuousWith μ 𝓝 h →
      ((a : MetricSpace.Carrier 𝓜) → g (point a) ≡ h (point a)) →
      (x : Completion) →
      g x ≡ h x
    uniformlyContinuous-equal g h g-cont h-cont point-path =
      PropInduction.ind kit
      where
      kit : PropInductionKit ℓᵗ
      kit .PropInductionKit.A x =
        g x ≡ h x
      kit .PropInductionKit.isPropA x =
        MetricSpace.isSetCarrier 𝓝 (g x) (h x)
      kit .PropInductionKit.point* =
        point-path
      kit .PropInductionKit.limit* x pointwise =
        MetricSpace.close-separated 𝓝 (g (limit x)) (h (limit x)) closeAt
        where
        closeAt : (ε : ℚ⁺) → MetricSpace.Close 𝓝 (g (limit x)) ε (h (limit x))
        closeAt ε =
          MetricSpace.close-mono 𝓝 {ε = (α +⁺ α) +⁺ α} {δ = ε}
            (three-quarter< ε)
            (MetricSpace.close-triangle 𝓝
              (MetricSpace.close-triangle 𝓝 g-lim∼approx g-approx∼h-approx)
              h-approx∼lim)
          where
          α : ℚ⁺
          α = quarter⁺ ε

          σ : ℚ⁺
          σ = μ α

          δ : ℚ⁺
          δ = quarter⁺ σ

          lim∼approx : limit x ∼[ σ ] approximate x δ
          lim∼approx =
            limit-approx-close x σ

          g-lim∼approx :
            MetricSpace.Close 𝓝 (g (limit x)) α (g (approximate x δ))
          g-lim∼approx =
            g-cont lim∼approx α (ℚOrder.isRefl≤ (radius (μ α)))

          g-approx∼h-approx :
            MetricSpace.Close 𝓝 (g (approximate x δ)) α (h (approximate x δ))
          g-approx∼h-approx =
            subst
              (λ y → MetricSpace.Close 𝓝 (g (approximate x δ)) α y)
              (pointwise δ)
              (MetricSpace.close-refl 𝓝 (g (approximate x δ)) α)

          h-approx∼lim :
            MetricSpace.Close 𝓝 (h (approximate x δ)) α (h (limit x))
          h-approx∼lim =
            h-cont (close-sym lim∼approx) α (ℚOrder.isRefl≤ (radius (μ α)))


    extend-unique :
      (g : Completion → MetricSpace.Carrier 𝓝) →
      IsCompletionUniformlyContinuousWith μ 𝓝 g →
      ((a : MetricSpace.Carrier 𝓜) → g (point a) ≡ f a) →
      (x : Completion) →
      g x ≡ extend x
    extend-unique g g-cont point-path =
      uniformlyContinuous-equal g extend g-cont extend-uniformlyContinuous point-path


  module ScaledLipschitzExtension
    (κ : ℚ⁺)
    (𝓝 : MetricSpace ℓᵗ ℓᵗ')
    (complete : MetricComplete.IsComplete 𝓝)
    (f : MetricSpace.Carrier 𝓜 → MetricSpace.Carrier 𝓝)
    (f-lip : IsScaledLipschitzWith κ 𝓝 f)
    where

    private
      targetLimit :
        MetricComplete.CauchyApproximation 𝓝 →
        MetricSpace.Carrier 𝓝
      targetLimit x =
        MetricComplete.limitPoint (complete x)

      targetConverges :
        (x : MetricComplete.CauchyApproximation 𝓝) →
        MetricComplete.ConvergesTo x (targetLimit x)
      targetConverges x =
        MetricComplete.converges (complete x)

      scaledTargetApproximation :
        (g : ℚ⁺ → MetricSpace.Carrier 𝓝) →
        ((ε δ : ℚ⁺) → MetricSpace.Close 𝓝 (g ε) (κ *⁺ (ε +⁺ δ)) (g δ)) →
        MetricComplete.CauchyApproximation 𝓝
      scaledTargetApproximation g gCauchy =
        MetricComplete.cauchy-approximation h hCauchy
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

      close-limit-target :
        (a : MetricSpace.Carrier 𝓝) →
        (x : MetricComplete.CauchyApproximation 𝓝) →
        (ε δ : ℚ⁺) →
        (δ<ε : δ <⁺ ε) →
        MetricSpace.Close 𝓝 a (ε ⊖ δ [ δ<ε ])
          (MetricComplete.approximate x δ) →
        MetricSpace.Close 𝓝 a ε (targetLimit x)
      close-limit-target a x ε δ δ<ε a∼xδ =
        Prop.rec
          (MetricSpace.isPropClose 𝓝 a (targetLimit x) ε)
          step
          (MetricSpace.close-rounded 𝓝 a∼xδ)
        where
        step :
          Σ[ ζ ∈ ℚ⁺ ]
            (ζ <⁺ ε ⊖ δ [ δ<ε ]) ×
            MetricSpace.Close 𝓝 a ζ (MetricComplete.approximate x δ) →
          MetricSpace.Close 𝓝 a ε (targetLimit x)
        step (ζ , ζ<ε-δ , a∼xζ) =
          subst
            (λ ρ → MetricSpace.Close 𝓝 a ρ (targetLimit x))
            (point-limit-sum ε δ ζ δ<ε ζ<ε-δ)
            (MetricSpace.close-triangle 𝓝 a∼xζ xδ∼lim)
          where
          gap : ℚ⁺
          gap = (ε ⊖ δ [ δ<ε ]) ⊖ ζ [ ζ<ε-δ ]

          δ<δ+gap : δ <⁺ δ +⁺ gap
          δ<δ+gap = summand-left<sum δ gap

          xδ∼lim :
            MetricSpace.Close 𝓝
              (MetricComplete.approximate x δ)
              (δ +⁺ gap)
              (targetLimit x)
          xδ∼lim =
            MetricSpace.close-sym 𝓝
              (targetConverges x (δ +⁺ gap) δ δ<δ+gap)

      limit-close-target :
        (x : MetricComplete.CauchyApproximation 𝓝) →
        (b : MetricSpace.Carrier 𝓝) →
        (ε δ : ℚ⁺) →
        (δ<ε : δ <⁺ ε) →
        MetricSpace.Close 𝓝
          (MetricComplete.approximate x δ)
          (ε ⊖ δ [ δ<ε ])
          b →
        MetricSpace.Close 𝓝 (targetLimit x) ε b
      limit-close-target x b ε δ δ<ε xδ∼b =
        MetricSpace.close-sym 𝓝
          (close-limit-target b x ε δ δ<ε
            (MetricSpace.close-sym 𝓝 xδ∼b))

      limit-limit-target :
        (x y : MetricComplete.CauchyApproximation 𝓝) →
        (ε δ η : ℚ⁺) →
        (δ+η<ε : δ +⁺ η <⁺ ε) →
        MetricSpace.Close 𝓝
          (MetricComplete.approximate x δ)
          (ε ⊖ (δ +⁺ η) [ δ+η<ε ])
          (MetricComplete.approximate y η) →
        MetricSpace.Close 𝓝 (targetLimit x) ε (targetLimit y)
      limit-limit-target x y ε δ η δ+η<ε xδ∼yη =
        Prop.rec
          (MetricSpace.isPropClose 𝓝 (targetLimit x) (targetLimit y) ε)
          step
          (MetricSpace.close-rounded 𝓝 xδ∼yη)
        where
        step :
          Σ[ ζ ∈ ℚ⁺ ]
            (ζ <⁺ ε ⊖ (δ +⁺ η) [ δ+η<ε ]) ×
            MetricSpace.Close 𝓝
              (MetricComplete.approximate x δ)
              ζ
              (MetricComplete.approximate y η) →
          MetricSpace.Close 𝓝 (targetLimit x) ε (targetLimit y)
        step (ζ , ζ<ε-δη , xδ∼yηζ) =
          subst
            (λ ρ → MetricSpace.Close 𝓝 (targetLimit x) ρ (targetLimit y))
            (limit-limit-sum ε δ η ζ δ+η<ε ζ<ε-δη)
            (MetricSpace.close-triangle 𝓝
              (MetricSpace.close-triangle 𝓝 lim∼xδ xδ∼yηζ)
              yη∼lim)
          where
          gap : ℚ⁺
          gap = (ε ⊖ (δ +⁺ η) [ δ+η<ε ]) ⊖ ζ [ ζ<ε-δη ]

          θ : ℚ⁺
          θ = half⁺ gap

          δ<δ+θ : δ <⁺ δ +⁺ θ
          δ<δ+θ = summand-left<sum δ θ

          η<η+θ : η <⁺ η +⁺ θ
          η<η+θ = summand-left<sum η θ

          lim∼xδ :
            MetricSpace.Close 𝓝 (targetLimit x) (δ +⁺ θ)
              (MetricComplete.approximate x δ)
          lim∼xδ =
            targetConverges x (δ +⁺ θ) δ δ<δ+θ

          yη∼lim :
            MetricSpace.Close 𝓝
              (MetricComplete.approximate y η)
              (η +⁺ θ)
              (targetLimit y)
          yη∼lim =
            MetricSpace.close-sym 𝓝
              (targetConverges y (η +⁺ θ) η η<η+θ)

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
            (scale-precision-cancel κ ε)
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
          scale-precision-mono κ δ ε δ<ε

        precisionPath :
          (κ *⁺ ε) ⊖ (κ *⁺ δ) [ κδ<κε ] ≡
          κ *⁺ (ε ⊖ δ [ δ<ε ])
        precisionPath =
          scale-precision-difference κ ε δ δ<ε κδ<κε

        indexPath : posInv⁺ κ *⁺ (κ *⁺ δ) ≡ δ
        indexPath =
          scale-precision-cancel-left κ δ

        a∼hκδ :
          MetricSpace.Close 𝓝
            (f a)
            ((κ *⁺ ε) ⊖ (κ *⁺ δ) [ κδ<κε ])
            (MetricComplete.approximate
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
          scale-precision-mono κ δ ε δ<ε

        precisionPath :
          (κ *⁺ ε) ⊖ (κ *⁺ δ) [ κδ<κε ] ≡
          κ *⁺ (ε ⊖ δ [ δ<ε ])
        precisionPath =
          scale-precision-difference κ ε δ δ<ε κδ<κε

        indexPath : posInv⁺ κ *⁺ (κ *⁺ δ) ≡ δ
        indexPath =
          scale-precision-cancel-left κ δ

        hκδ∼b :
          MetricSpace.Close 𝓝
            (MetricComplete.approximate
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
          scale-precision-cancel-left κ δ

        ηIndexPath : posInv⁺ κ *⁺ (κ *⁺ η) ≡ η
        ηIndexPath =
          scale-precision-cancel-left κ η

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
            (MetricComplete.approximate
              (scaledTargetApproximation h hCauchy)
              (κ *⁺ η))
        gδ∼hκη =
          subst
            (λ θ → MetricSpace.Close 𝓝 (g δ) neededPrecision (h θ))
            (sym ηIndexPath)
            gδ∼hη-neededPrecision

        gκδ∼hκη :
          MetricSpace.Close 𝓝
            (MetricComplete.approximate
              (scaledTargetApproximation g gCauchy)
              (κ *⁺ δ))
            neededPrecision
            (MetricComplete.approximate
              (scaledTargetApproximation h hCauchy)
              (κ *⁺ η))
        gκδ∼hκη =
          subst
            (λ θ →
              MetricSpace.Close 𝓝 (g θ) neededPrecision
                (MetricComplete.approximate
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


    extend-close :
      IsCompletionScaledLipschitzWith κ 𝓝 extend
    extend-close =
      ExtensionRecursion.rec-close


    extend-scaledLipschitz :
      IsCompletionScaledLipschitzWith κ 𝓝 extend
    extend-scaledLipschitz =
      extend-close


    extend-lipschitzWithModulus :
      {x y : Completion} {ε : ℚ⁺} →
      x ∼[ posInv⁺ κ *⁺ ε ] y →
      MetricSpace.Close 𝓝 (extend x) ε (extend y)
    extend-lipschitzWithModulus {x = x} {y = y} {ε = ε} x∼y =
      subst
        (λ ρ → MetricSpace.Close 𝓝 (extend x) ρ (extend y))
        (scale-precision-cancel κ ε)
        (extend-close x∼y)


    scaledLipschitz-equal :
      (g h : Completion → MetricSpace.Carrier 𝓝) →
      IsCompletionScaledLipschitzWith κ 𝓝 g →
      IsCompletionScaledLipschitzWith κ 𝓝 h →
      ((a : MetricSpace.Carrier 𝓜) → g (point a) ≡ h (point a)) →
      (x : Completion) →
      g x ≡ h x
    scaledLipschitz-equal g h g-lip h-lip point-path =
      PropInduction.ind kit
      where
      kit : PropInductionKit ℓᵗ
      kit .PropInductionKit.A x =
        g x ≡ h x
      kit .PropInductionKit.isPropA x =
        MetricSpace.isSetCarrier 𝓝 (g x) (h x)
      kit .PropInductionKit.point* =
        point-path
      kit .PropInductionKit.limit* x pointwise =
        MetricSpace.close-separated 𝓝 (g (limit x)) (h (limit x)) closeAt
        where
        closeAt : (ε : ℚ⁺) → MetricSpace.Close 𝓝 (g (limit x)) ε (h (limit x))
        closeAt ε =
          MetricSpace.close-mono 𝓝 {ε = (α +⁺ α) +⁺ α} {δ = ε}
            (three-quarter< ε)
            (MetricSpace.close-triangle 𝓝
              (MetricSpace.close-triangle 𝓝 g-lim∼approx g-approx∼h-approx)
              h-approx∼lim)
          where
          α : ℚ⁺
          α = quarter⁺ ε

          σ : ℚ⁺
          σ = posInv⁺ κ *⁺ α

          δ : ℚ⁺
          δ = quarter⁺ σ

          lim∼approx : limit x ∼[ σ ] approximate x δ
          lim∼approx =
            limit-approx-close x σ

          g-lim∼approx :
            MetricSpace.Close 𝓝 (g (limit x)) α (g (approximate x δ))
          g-lim∼approx =
            subst
              (λ ρ → MetricSpace.Close 𝓝 (g (limit x)) ρ (g (approximate x δ)))
              (scale-precision-cancel κ α)
              (g-lip lim∼approx)

          g-approx∼h-approx :
            MetricSpace.Close 𝓝 (g (approximate x δ)) α (h (approximate x δ))
          g-approx∼h-approx =
            subst
              (λ y → MetricSpace.Close 𝓝 (g (approximate x δ)) α y)
              (pointwise δ)
              (MetricSpace.close-refl 𝓝 (g (approximate x δ)) α)

          h-approx∼lim :
            MetricSpace.Close 𝓝 (h (approximate x δ)) α (h (limit x))
          h-approx∼lim =
            subst
              (λ ρ → MetricSpace.Close 𝓝 (h (approximate x δ)) ρ (h (limit x)))
              (scale-precision-cancel κ α)
              (h-lip (close-sym lim∼approx))


    extend-unique :
      (g : Completion → MetricSpace.Carrier 𝓝) →
      IsCompletionScaledLipschitzWith κ 𝓝 g →
      ((a : MetricSpace.Carrier 𝓜) → g (point a) ≡ f a) →
      (x : Completion) →
      g x ≡ extend x
    extend-unique g g-lip point-path =
      scaledLipschitz-equal g extend g-lip extend-scaledLipschitz point-path
