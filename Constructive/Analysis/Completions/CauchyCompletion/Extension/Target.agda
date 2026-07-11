{-

Limit support for extension into a complete metric space

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Completions.CauchyCompletion.Extension.Target where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
  using (ℚCommRing)
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Metric.Base
import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Data.PositiveRationals

private
  variable
    ℓ ℓ' : Level

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


module CompleteTargetOf
  (𝓝 : MetricSpace ℓ ℓ')
  (complete : MetricCauchy.IsCauchyComplete 𝓝)
  where

  private
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


  targetLimit :
    MetricCauchy.CauchyApproximation 𝓝 →
    MetricSpace.Carrier 𝓝
  targetLimit x =
    MetricCauchy.limitPoint (complete x)


  targetConverges :
    (x : MetricCauchy.CauchyApproximation 𝓝) →
    MetricCauchy.ConvergesTo x (targetLimit x)
  targetConverges x =
    MetricCauchy.converges (complete x)


  close-limit-target :
    (a : MetricSpace.Carrier 𝓝) →
    (x : MetricCauchy.CauchyApproximation 𝓝) →
    (ε δ : ℚ⁺) →
    (δ<ε : δ <⁺ ε) →
    MetricSpace.Close 𝓝 a (ε ⊖ δ [ δ<ε ])
      (MetricCauchy.approximate x δ) →
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
        MetricSpace.Close 𝓝 a ζ (MetricCauchy.approximate x δ) →
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
          (MetricCauchy.approximate x δ)
          (δ +⁺ gap)
          (targetLimit x)
      xδ∼lim =
        MetricSpace.close-sym 𝓝
          (targetConverges x (δ +⁺ gap) δ δ<δ+gap)


  limit-close-target :
    (x : MetricCauchy.CauchyApproximation 𝓝) →
    (b : MetricSpace.Carrier 𝓝) →
    (ε δ : ℚ⁺) →
    (δ<ε : δ <⁺ ε) →
    MetricSpace.Close 𝓝
      (MetricCauchy.approximate x δ)
      (ε ⊖ δ [ δ<ε ])
      b →
    MetricSpace.Close 𝓝 (targetLimit x) ε b
  limit-close-target x b ε δ δ<ε xδ∼b =
    MetricSpace.close-sym 𝓝
      (close-limit-target b x ε δ δ<ε
        (MetricSpace.close-sym 𝓝 xδ∼b))


  limit-limit-target :
    (x y : MetricCauchy.CauchyApproximation 𝓝) →
    (ε δ η : ℚ⁺) →
    (δ+η<ε : δ +⁺ η <⁺ ε) →
    MetricSpace.Close 𝓝
      (MetricCauchy.approximate x δ)
      (ε ⊖ (δ +⁺ η) [ δ+η<ε ])
      (MetricCauchy.approximate y η) →
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
          (MetricCauchy.approximate x δ)
          ζ
          (MetricCauchy.approximate y η) →
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
          (MetricCauchy.approximate x δ)
      lim∼xδ =
        targetConverges x (δ +⁺ θ) δ δ<δ+θ

      yη∼lim :
        MetricSpace.Close 𝓝
          (MetricCauchy.approximate y η)
          (η +⁺ θ)
          (targetLimit y)
      yη∼lim =
        MetricSpace.close-sym 𝓝
          (targetConverges y (η +⁺ θ) η η<η+θ)
