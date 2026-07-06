{-

Enhanced recursion for Cauchy completions

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.CauchyCompletion.Recursion where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.CauchyCompletion.Base
open import Constructive.Analysis.CauchyCompletion.Definitions
open import Constructive.Data.PositiveRationals

private
  variable
    ℓᵐ ℓᵐ' ℓ ℓ' : Level


module RecursionOf (𝓜 : MetricSpace ℓᵐ ℓᵐ') where
  open CompletionOf 𝓜
  open DefinitionsOf 𝓜

  private
    A₀ : Type ℓᵐ
    A₀ = MetricSpace.Carrier 𝓜

    ℓᶜ : Level
    ℓᶜ = ℓ-max ℓᵐ ℓᵐ'

  record RecursionKit (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓᶜ (ℓ-max ℓ ℓ'))) where
    no-eta-equality

    field
      A : Type ℓ
      B : TargetCloseness A ℓ'

      isPropB : (ε : ℚ⁺) (a b : A) → isProp (B ε a b)
      separated : (a b : A) → ((ε : ℚ⁺) → B ε a b) → a ≡ b

      point* : A₀ → A
      limit* :
        (x : CauchyApproximation) →
        (f : ℚ⁺ → A) →
        IsTargetCauchyApproximation B f →
        A

      point-point* :
        (a b : A₀) (ε : ℚ⁺) →
        MetricSpace.Close 𝓜 a ε b →
        B ε (point* a) (point* b)

      point-limit* :
        (a : A₀) (ε δ : ℚ⁺) →
        (δ<ε : δ <⁺ ε) →
        (y : CauchyApproximation) →
        (g : ℚ⁺ → A) →
        (gCauchy : IsTargetCauchyApproximation B g) →
        B (ε ⊖ δ [ δ<ε ]) (point* a) (g δ) →
        B ε (point* a) (limit* y g gCauchy)

      limit-point* :
        (x : CauchyApproximation) →
        (f : ℚ⁺ → A) →
        (fCauchy : IsTargetCauchyApproximation B f) →
        (b : A₀) (ε δ : ℚ⁺) →
        (δ<ε : δ <⁺ ε) →
        B (ε ⊖ δ [ δ<ε ]) (f δ) (point* b) →
        B ε (limit* x f fCauchy) (point* b)

      limit-limit* :
        (x y : CauchyApproximation) →
        (f g : ℚ⁺ → A) →
        (fCauchy : IsTargetCauchyApproximation B f) →
        (gCauchy : IsTargetCauchyApproximation B g) →
        (ε δ η : ℚ⁺) →
        (δ+η<ε : δ +⁺ η <⁺ ε) →
        B (ε ⊖ (δ +⁺ η) [ δ+η<ε ]) (f δ) (g η) →
        B ε (limit* x f fCauchy) (limit* y g gCauchy)


  module Recursion (kit : RecursionKit ℓ ℓ') where
    open RecursionKit kit

    mutual
      rec : Completion → A
      rec (point a) = point* a
      rec (limit x) =
        limit* x
          (λ ε → rec (approximate x ε))
          (λ ε δ → rec-close (isRegular x ε δ))
      rec (path x y x∼y i) =
        separated (rec x) (rec y) (λ ε → rec-close (x∼y ε)) i

      rec-close : {x y : Completion} {ε : ℚ⁺} → x ∼[ ε ] y → B ε (rec x) (rec y)
      rec-close (point-point-close a b ε a∼b) =
        point-point* a b ε a∼b
      rec-close (point-limit-close a ε δ δ<ε y a∼yδ) =
        point-limit* a ε δ δ<ε y
          (λ η → rec (approximate y η))
          (λ η θ → rec-close (isRegular y η θ))
          (rec-close a∼yδ)
      rec-close (limit-point-close x b ε δ δ<ε xδ∼b) =
        limit-point* x
          (λ η → rec (approximate x η))
          (λ η θ → rec-close (isRegular x η θ))
          b ε δ δ<ε
          (rec-close xδ∼b)
      rec-close (limit-limit-close x y ε δ η δ+η<ε xδ∼yη) =
        limit-limit* x y
          (λ θ → rec (approximate x θ))
          (λ θ → rec (approximate y θ))
          (λ θ κ → rec-close (isRegular x θ κ))
          (λ θ κ → rec-close (isRegular y θ κ))
          ε δ η δ+η<ε
          (rec-close xδ∼yη)
      rec-close (squash p q i) =
        isPropB _ _ _ (rec-close p) (rec-close q) i
