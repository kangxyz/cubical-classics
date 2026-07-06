{-

Induction interfaces for Cauchy completions

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Completions.CauchyCompletion.Induction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit using (Unit* ; tt* ; isPropUnit*)

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Completions.CauchyCompletion.Base
open import Constructive.Analysis.Completions.CauchyCompletion.Definitions
open import Constructive.Data.PositiveRationals

private
  variable
    ℓᵐ ℓᵐ' ℓ ℓ' : Level


module InductionOf (𝓜 : MetricSpace ℓᵐ ℓᵐ') where
  open CompletionOf 𝓜
  open DefinitionsOf 𝓜

  private
    A₀ : Type ℓᵐ
    A₀ = MetricSpace.Carrier 𝓜

    ℓᶜ : Level
    ℓᶜ = ℓ-max ℓᵐ ℓᵐ'

  record InductionKit (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓᶜ (ℓ-max ℓ ℓ'))) where
    no-eta-equality

    field
      A : Completion → Type ℓ
      B : DependentCloseness A ℓ'

      point* : (a : A₀) → A (point a)
      limit* :
        (x : CauchyApproximation) →
        (a : (ε : ℚ⁺) → A (approximate x ε)) →
        IsDependentCauchyApproximation B x a →
        A (limit x)

      path* :
        (x y : Completion) →
        (x∼y : (ε : ℚ⁺) → x ∼[ ε ] y) →
        (a : A x) →
        (b : A y) →
        ((ε : ℚ⁺) → B ε (x∼y ε) a b) →
        PathP (λ i → A (path x y x∼y i)) a b

      point-point* :
        (a b : A₀) (ε : ℚ⁺) →
        (a∼b : MetricSpace.Close 𝓜 a ε b) →
        B ε (point-point-close a b ε a∼b) (point* a) (point* b)

      point-limit* :
        (a : A₀) (ε δ : ℚ⁺) →
        (δ<ε : δ <⁺ ε) →
        (y : CauchyApproximation) →
        (b : (η : ℚ⁺) → A (approximate y η)) →
        (bCauchy : IsDependentCauchyApproximation B y b) →
        (a∼yδ : point a ∼[ ε ⊖ δ [ δ<ε ] ] approximate y δ) →
        B (ε ⊖ δ [ δ<ε ]) a∼yδ (point* a) (b δ) →
        B ε
          (point-limit-close a ε δ δ<ε y a∼yδ)
          (point* a)
          (limit* y b bCauchy)

      limit-point* :
        (x : CauchyApproximation) →
        (a : (η : ℚ⁺) → A (approximate x η)) →
        (aCauchy : IsDependentCauchyApproximation B x a) →
        (b : A₀) (ε δ : ℚ⁺) →
        (δ<ε : δ <⁺ ε) →
        (xδ∼b : approximate x δ ∼[ ε ⊖ δ [ δ<ε ] ] point b) →
        B (ε ⊖ δ [ δ<ε ]) xδ∼b (a δ) (point* b) →
        B ε
          (limit-point-close x b ε δ δ<ε xδ∼b)
          (limit* x a aCauchy)
          (point* b)

      limit-limit* :
        (x y : CauchyApproximation) →
        (a : (θ : ℚ⁺) → A (approximate x θ)) →
        (b : (θ : ℚ⁺) → A (approximate y θ)) →
        (aCauchy : IsDependentCauchyApproximation B x a) →
        (bCauchy : IsDependentCauchyApproximation B y b) →
        (ε δ η : ℚ⁺) →
        (δ+η<ε : δ +⁺ η <⁺ ε) →
        (xδ∼yη :
          approximate x δ
            ∼[ ε ⊖ (δ +⁺ η) [ δ+η<ε ] ]
            approximate y η) →
        B (ε ⊖ (δ +⁺ η) [ δ+η<ε ]) xδ∼yη (a δ) (b η) →
        B ε
          (limit-limit-close x y ε δ η δ+η<ε xδ∼yη)
          (limit* x a aCauchy)
          (limit* y b bCauchy)

      squash* :
        {x y : Completion} {ε : ℚ⁺} →
        (p : x ∼[ ε ] y) →
        (a : A x) →
        (b : A y) →
        isProp (B ε p a b)


  module Induction (kit : InductionKit ℓ ℓ') where
    open InductionKit kit

    mutual
      ind : (x : Completion) → A x
      ind (point a) = point* a
      ind (limit x) =
        limit* x
          (λ ε → ind (approximate x ε))
          (λ ε δ → ind-close (isRegular x ε δ))
      ind (path x y x∼y i) =
        path* x y x∼y (ind x) (ind y) (λ ε → ind-close (x∼y ε)) i

      ind-close :
        {x y : Completion} {ε : ℚ⁺} →
        (x∼y : x ∼[ ε ] y) →
        B ε x∼y (ind x) (ind y)
      ind-close (point-point-close a b ε a∼b) =
        point-point* a b ε a∼b
      ind-close (point-limit-close a ε δ δ<ε y a∼yδ) =
        point-limit* a ε δ δ<ε y
          (λ η → ind (approximate y η))
          (λ η θ → ind-close (isRegular y η θ))
          a∼yδ
          (ind-close a∼yδ)
      ind-close (limit-point-close x b ε δ δ<ε xδ∼b) =
        limit-point* x
          (λ η → ind (approximate x η))
          (λ η θ → ind-close (isRegular x η θ))
          b ε δ δ<ε
          xδ∼b
          (ind-close xδ∼b)
      ind-close (limit-limit-close x y ε δ η δ+η<ε xδ∼yη) =
        limit-limit* x y
          (λ θ → ind (approximate x θ))
          (λ θ → ind (approximate y θ))
          (λ θ κ → ind-close (isRegular x θ κ))
          (λ θ κ → ind-close (isRegular y θ κ))
          ε δ η δ+η<ε
          xδ∼yη
          (ind-close xδ∼yη)
      ind-close (squash p q i) =
        isProp→PathP
          (λ i → squash* (squash p q i) _ _)
          (ind-close p)
          (ind-close q)
          i


  record PropInductionKit (ℓ : Level) : Type (ℓ-suc (ℓ-max ℓᶜ ℓ)) where
    no-eta-equality

    field
      A : Completion → Type ℓ
      isPropA : (x : Completion) → isProp (A x)

      point* : (a : A₀) → A (point a)
      limit* :
        (x : CauchyApproximation) →
        ((ε : ℚ⁺) → A (approximate x ε)) →
        A (limit x)


  module PropInduction (kit : PropInductionKit ℓ) where
    open PropInductionKit kit

    private
      propKit : InductionKit ℓ ℓ-zero
      propKit .InductionKit.A = A
      propKit .InductionKit.B ε x∼y a b = Unit*
      propKit .InductionKit.point* = point*
      propKit .InductionKit.limit* x a aCauchy = limit* x a
      propKit .InductionKit.path* x y x∼y a b close* =
        isProp→PathP
          (λ i → isPropA (path x y x∼y i))
          a
          b
      propKit .InductionKit.point-point* a b ε a∼b = tt*
      propKit .InductionKit.point-limit* a ε δ δ<ε y b bCauchy a∼yδ a∼bδ = tt*
      propKit .InductionKit.limit-point* x a aCauchy b ε δ δ<ε xδ∼b aδ∼b = tt*
      propKit .InductionKit.limit-limit* x y a b aCauchy bCauchy ε δ η δ+η<ε xδ∼yη aδ∼bη = tt*
      propKit .InductionKit.squash* p a b = isPropUnit*

      module Ind = Induction propKit

    ind : (x : Completion) → A x
    ind = Ind.ind
