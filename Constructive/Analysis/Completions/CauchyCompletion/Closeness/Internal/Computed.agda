{-

Computed alternative closeness, point source case

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Completions.CauchyCompletion.Closeness.Internal.Computed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit* ; tt* ; isPropUnit*)
open import Cubical.HITs.PropositionalTruncation as Prop

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Completions.CauchyCompletion.Base
open import Constructive.Analysis.Completions.CauchyCompletion.Closeness.Internal.Prelength
open import Constructive.Analysis.Completions.CauchyCompletion.Induction
open import Constructive.Analysis.Completions.CauchyCompletion.Recursion
open import Constructive.Data.PositiveRationals


private
  variable
    ℓ ℓ' : Level


module ComputedOf (𝓜 : MetricSpace ℓ ℓ') where
  open CompletionOf 𝓜
  open PrelengthOf 𝓜
  open InductionOf 𝓜
  open RecursionOf 𝓜

  private
    A : Type ℓ
    A = MetricSpace.Carrier 𝓜

    ℓᶜ : Level
    ℓᶜ = ℓ-max ℓ ℓ'


  private
    isPropPrecisionRelation :
      (P Q : PrecisionBundle) (ε : ℚ⁺) →
      isProp (PrecisionRelation P Q ε)
    isPropPrecisionRelation P Q ε =
      isPropΠ λ η →
        isProp×
          (isProp→ (PrecisionStructure.isPropP (Q .snd) (η +⁺ ε)))
          (isProp→ (PrecisionStructure.isPropP (P .snd) (η +⁺ ε)))

    pointTargetKit : A → RecursionKit (ℓ-suc ℓ') ℓ'
    pointTargetKit a .RecursionKit.A =
      PrecisionBundle
    pointTargetKit a .RecursionKit.B =
      λ ε P Q → PrecisionRelation P Q ε
    pointTargetKit a .RecursionKit.isPropB =
      λ ε P Q → isPropPrecisionRelation P Q ε
    pointTargetKit a .RecursionKit.separated =
      precision-separated
    pointTargetKit a .RecursionKit.point* =
      pointPrecisionBundle a
    pointTargetKit a .RecursionKit.limit* y f fCauchy =
      pointLimitPrecisionBundle f
    pointTargetKit a .RecursionKit.point-point* b c ε b∼c =
      pointPrecisionRelation a b c ε b∼c
    pointTargetKit a .RecursionKit.point-limit* b ε δ δ<ε y g gCauchy b∼gδ =
      pointLimitPrecisionRelation
        (pointPrecisionBundle a b)
        g
        gCauchy
        ε δ δ<ε
        b∼gδ
    pointTargetKit a .RecursionKit.limit-point* y f fCauchy b ε δ δ<ε fδ∼b =
      limitPointPrecisionRelation
        f
        (pointPrecisionBundle a b)
        fCauchy
        ε δ δ<ε
        fδ∼b
    pointTargetKit a .RecursionKit.limit-limit* x y f g fCauchy gCauchy ε δ η δ+η<ε fδ∼gη =
      limitLimitPrecisionRelation
        f g
        fCauchy gCauchy
        ε δ η δ+η<ε
        fδ∼gη

    module PointTarget (a : A) = Recursion (pointTargetKit a)


  pointSourceBundle : A → PredicateBundle
  pointSourceBundle a .fst u ε =
    precisionPredicate (PointTarget.rec a u) ε
  pointSourceBundle a .snd .PredicateStructure.isPropP u ε =
    PrecisionStructure.isPropP (PointTarget.rec a u .snd) ε
  pointSourceBundle a .snd .PredicateStructure.rounded u ε =
    PrecisionStructure.rounded (PointTarget.rec a u .snd) ε
  pointSourceBundle a .snd .PredicateStructure.mixedRight u v ε η u∼v =
    fst (PointTarget.rec-close a u∼v η)
  pointSourceBundle a .snd .PredicateStructure.mixedLeft u v ε η u∼v =
    snd (PointTarget.rec-close a u∼v η)


  ComputedPointClose : A → Completion → ℚ⁺ → Type ℓ'
  ComputedPointClose a u ε =
    bundlePredicate (pointSourceBundle a) u ε


  computedPoint→close :
    (a : A) (u : Completion) (ε : ℚ⁺) →
    ComputedPointClose a u ε →
    point a ∼[ ε ] u
  computedPoint→close a =
    PropInduction.ind kit
    where
    kit : PropInductionKit ℓᶜ
    kit .PropInductionKit.A u =
      (ε : ℚ⁺) →
      ComputedPointClose a u ε →
      point a ∼[ ε ] u
    kit .PropInductionKit.isPropA u =
      isPropΠ2 λ ε _ → squash
    kit .PropInductionKit.point* b ε =
      point-point-close a b ε
    kit .PropInductionKit.limit* y yClose ε =
      Prop.rec squash step
      where
      step :
        Σ[ δ ∈ ℚ⁺ ]
          Σ[ δ<ε ∈ δ <⁺ ε ]
          ComputedPointClose a (approximate y δ) (ε ⊖ δ [ δ<ε ]) →
        point a ∼[ ε ] limit y
      step (δ , δ<ε , a∼yδ) =
        point-limit-close a ε δ δ<ε y
          (yClose δ (ε ⊖ δ [ δ<ε ]) a∼yδ)


  private
    isPropRelation :
      (P Q : PredicateBundle) (ε : ℚ⁺) →
      isProp (Relation P Q ε)
    isPropRelation P Q ε =
      isPropΠ2 λ u η →
        isProp×
          (isProp→ (PredicateStructure.isPropP (Q .snd) u (η +⁺ ε)))
          (isProp→ (PredicateStructure.isPropP (P .snd) u (η +⁺ ε)))


  pointSourceRelation :
    (a b : A) (ε : ℚ⁺) →
    MetricSpace.Close 𝓜 a ε b →
    Relation (pointSourceBundle a) (pointSourceBundle b) ε
  pointSourceRelation a b ε a∼b u η =
    forward , backward
    where
    forward :
      ComputedPointClose a u η →
      ComputedPointClose b u (η +⁺ ε)
    forward a∼u =
      subst
        (ComputedPointClose b u)
        (+⁺-comm ε η)
        (PredicateStructure.mixedRight (pointSourceBundle b .snd)
          (point a) u η ε
          (computedPoint→close a u η a∼u)
          (MetricSpace.close-sym 𝓜 a∼b))

    backward :
      ComputedPointClose b u η →
      ComputedPointClose a u (η +⁺ ε)
    backward b∼u =
      subst
        (ComputedPointClose a u)
        (+⁺-comm ε η)
        (PredicateStructure.mixedRight (pointSourceBundle a .snd)
          (point b) u η ε
          (computedPoint→close b u η b∼u)
          a∼b)


  private
    sourceKit : RecursionKit (ℓ-max ℓᶜ (ℓ-suc ℓ')) (ℓ-max ℓᶜ ℓ')
    sourceKit .RecursionKit.A =
      PredicateBundle
    sourceKit .RecursionKit.B =
      λ ε P Q → Relation P Q ε
    sourceKit .RecursionKit.isPropB =
      λ ε P Q → isPropRelation P Q ε
    sourceKit .RecursionKit.separated =
      bundle-separated
    sourceKit .RecursionKit.point* =
      pointSourceBundle
    sourceKit .RecursionKit.limit* x f fCauchy =
      limitSourceBundle f
    sourceKit .RecursionKit.point-point* a b ε a∼b =
      pointSourceRelation a b ε a∼b
    sourceKit .RecursionKit.point-limit* a ε δ δ<ε y g gCauchy a∼gδ =
      sourceLimitRelation
        (pointSourceBundle a)
        g
        gCauchy
        ε δ δ<ε
        a∼gδ
    sourceKit .RecursionKit.limit-point* x f fCauchy a ε δ δ<ε fδ∼a =
      limitSourceRelation
        f
        (pointSourceBundle a)
        fCauchy
        ε δ δ<ε
        fδ∼a
    sourceKit .RecursionKit.limit-limit* x y f g fCauchy gCauchy ε δ η δ+η<ε fδ∼gη =
      limitLimitSourceRelation
        f g
        fCauchy gCauchy
        ε δ η δ+η<ε
        fδ∼gη

    module Source = Recursion sourceKit


  computedBundle : Completion → PredicateBundle
  computedBundle =
    Source.rec


  ComputedClose : ℚ⁺ → Completion → Completion → Type ℓ'
  ComputedClose ε x y =
    bundlePredicate (computedBundle x) y ε


  isPropComputedClose :
    (x y : Completion) (ε : ℚ⁺) →
    isProp (ComputedClose ε x y)
  isPropComputedClose x y ε =
    PredicateStructure.isPropP (computedBundle x .snd) y ε


  computedRelation :
    {x y : Completion} {ε : ℚ⁺} →
    x ∼[ ε ] y →
    Relation (computedBundle x) (computedBundle y) ε
  computedRelation =
    Source.rec-close


  targetLimitIntro :
    (x : Completion) (y : CauchyApproximation) (ε η : ℚ⁺) →
    (η<ε : η <⁺ ε) →
    ComputedClose (ε ⊖ η [ η<ε ]) x (approximate y η) →
    ComputedClose ε x (limit y)
  targetLimitIntro =
    PropInduction.ind kit
    where
    kit : PropInductionKit ℓᶜ
    kit .PropInductionKit.A x =
      (y : CauchyApproximation) (ε η : ℚ⁺) →
      (η<ε : η <⁺ ε) →
      ComputedClose (ε ⊖ η [ η<ε ]) x (approximate y η) →
      ComputedClose ε x (limit y)
    kit .PropInductionKit.isPropA x =
      isPropΠ λ y →
      isPropΠ λ ε →
      isPropΠ λ η →
      isPropΠ λ η<ε →
      isPropΠ λ _ →
        isPropComputedClose x (limit y) ε
    kit .PropInductionKit.point* a y ε η η<ε a∼yη =
      ∣ η , η<ε , a∼yη ∣₁
    kit .PropInductionKit.limit* x xIntro y ε η η<ε =
      Prop.rec squash₁ step
      where
      step :
        Σ[ δ ∈ ℚ⁺ ]
          Σ[ δ<ε-η ∈ δ <⁺ ε ⊖ η [ η<ε ] ]
          ComputedClose
            ((ε ⊖ η [ η<ε ]) ⊖ δ [ δ<ε-η ])
            (approximate x δ)
            (approximate y η) →
        ComputedClose ε (limit x) (limit y)
      step (δ , δ<ε-η , xδ∼yη) =
        ∣ δ , δ<ε ,
            xIntro δ y (ε ⊖ δ [ δ<ε ]) η η<ε-δ
              (subst
                (λ ρ → ComputedClose ρ (approximate x δ) (approximate y η))
                (sym (difference-difference-comm ε δ η δ<ε η<ε η<ε-δ δ<ε-η))
                xδ∼yη)
        ∣₁
        where
        η+δ<ε : η +⁺ δ <⁺ ε
        η+δ<ε =
          sum<from-difference ε η δ η<ε δ<ε-η

        δ+η<ε : δ +⁺ η <⁺ ε
        δ+η<ε =
          subst (λ ρ → ρ <⁺ ε) (+⁺-comm η δ) η+δ<ε

        δ<ε : δ <⁺ ε
        δ<ε =
          <⁺-trans
            {ε = δ}
            {δ = η +⁺ δ}
            {η = ε}
            (subst (λ ρ → δ <⁺ ρ) (+⁺-comm δ η) (summand-left<sum δ η))
            η+δ<ε

        η<ε-δ : η <⁺ ε ⊖ δ [ δ<ε ]
        η<ε-δ =
          difference-from-sum< ε δ η δ+η<ε


  targetLimitElim :
    (x : Completion) (y : CauchyApproximation) (ε : ℚ⁺) →
    ComputedClose ε x (limit y) →
    ∥ Σ[ η ∈ ℚ⁺ ]
        Σ[ η<ε ∈ η <⁺ ε ]
        ComputedClose (ε ⊖ η [ η<ε ]) x (approximate y η)
    ∥₁
  targetLimitElim =
    PropInduction.ind kit
    where
    kit : PropInductionKit ℓᶜ
    kit .PropInductionKit.A x =
      (y : CauchyApproximation) (ε : ℚ⁺) →
      ComputedClose ε x (limit y) →
      ∥ Σ[ η ∈ ℚ⁺ ]
          Σ[ η<ε ∈ η <⁺ ε ]
          ComputedClose (ε ⊖ η [ η<ε ]) x (approximate y η)
      ∥₁
    kit .PropInductionKit.isPropA x =
      isPropΠ λ y →
      isPropΠ λ ε →
      isPropΠ λ _ →
        squash₁
    kit .PropInductionKit.point* a y ε a∼lim =
      a∼lim
    kit .PropInductionKit.limit* x xElim y ε =
      Prop.rec squash₁ step
      where
      refine :
        (δ : ℚ⁺) →
        (δ<ε : δ <⁺ ε) →
        Σ[ η ∈ ℚ⁺ ]
          Σ[ η<ε-δ ∈ η <⁺ ε ⊖ δ [ δ<ε ] ]
          ComputedClose
            ((ε ⊖ δ [ δ<ε ]) ⊖ η [ η<ε-δ ])
            (approximate x δ)
            (approximate y η) →
        ∥ Σ[ η ∈ ℚ⁺ ]
            Σ[ η<ε ∈ η <⁺ ε ]
            ComputedClose (ε ⊖ η [ η<ε ]) (limit x) (approximate y η)
        ∥₁
      refine δ δ<ε (η , η<ε-δ , xδ∼yη) =
        ∣ η , η<ε ,
            ∣ δ , δ<ε-η ,
                subst
                  (λ ρ → ComputedClose ρ (approximate x δ) (approximate y η))
                  (difference-difference-comm ε δ η δ<ε η<ε η<ε-δ δ<ε-η)
                  xδ∼yη
            ∣₁
        ∣₁
        where
        δ+η<ε : δ +⁺ η <⁺ ε
        δ+η<ε =
          sum<from-difference ε δ η δ<ε η<ε-δ

        η<ε : η <⁺ ε
        η<ε =
          <⁺-trans
            {ε = η}
            {δ = δ +⁺ η}
            {η = ε}
            (subst (λ ρ → η <⁺ ρ) (+⁺-comm η δ) (summand-left<sum η δ))
            δ+η<ε

        η+δ<ε : η +⁺ δ <⁺ ε
        η+δ<ε =
          subst (λ ρ → ρ <⁺ ε) (+⁺-comm δ η) δ+η<ε

        δ<ε-η : δ <⁺ ε ⊖ η [ η<ε ]
        δ<ε-η =
          difference-from-sum< ε η δ η+δ<ε

      step :
        Σ[ δ ∈ ℚ⁺ ]
          Σ[ δ<ε ∈ δ <⁺ ε ]
          ComputedClose (ε ⊖ δ [ δ<ε ]) (approximate x δ) (limit y) →
        ∥ Σ[ η ∈ ℚ⁺ ]
            Σ[ η<ε ∈ η <⁺ ε ]
            ComputedClose (ε ⊖ η [ η<ε ]) (limit x) (approximate y η)
        ∥₁
      step (δ , δ<ε , xδ∼lim) =
        Prop.rec squash₁ (refine δ δ<ε) (xElim δ y (ε ⊖ δ [ δ<ε ]) xδ∼lim)


  private
    closeToComputedKit : InductionKit ℓ-zero ℓ'
    closeToComputedKit .InductionKit.A x =
      Unit*
    closeToComputedKit .InductionKit.B ε {x = x} {y = y} x∼y _ _ =
      ComputedClose ε x y
    closeToComputedKit .InductionKit.point* a =
      tt*
    closeToComputedKit .InductionKit.limit* x a aCauchy =
      tt*
    closeToComputedKit .InductionKit.path* x y x∼y a b close* =
      isProp→PathP (λ i → isPropUnit*) a b
    closeToComputedKit .InductionKit.point-point* a b ε a∼b =
      a∼b
    closeToComputedKit .InductionKit.point-limit* a ε δ δ<ε y b bCauchy a∼yδ a∼bδ =
      ∣ δ , δ<ε , a∼bδ ∣₁
    closeToComputedKit .InductionKit.limit-point* x a aCauchy b ε δ δ<ε xδ∼b aδ∼b =
      ∣ δ , δ<ε , aδ∼b ∣₁
    closeToComputedKit .InductionKit.limit-limit*
      x y a b aCauchy bCauchy ε δ η δ+η<ε xδ∼yη aδ∼bη =
      ∣ δ , δ<ε ,
          targetLimitIntro (approximate x δ) y (ε ⊖ δ [ δ<ε ]) η η<ε-δ
            (subst
              (λ ρ → ComputedClose ρ (approximate x δ) (approximate y η))
              (sym (difference-difference-sum ε δ η δ+η<ε δ<ε η<ε-δ))
              aδ∼bη)
      ∣₁
      where
      δ<ε : δ <⁺ ε
      δ<ε =
        <⁺-trans
          {ε = δ}
          {δ = δ +⁺ η}
          {η = ε}
          (summand-left<sum δ η)
          δ+η<ε

      η<ε-δ : η <⁺ ε ⊖ δ [ δ<ε ]
      η<ε-δ =
        difference-from-sum< ε δ η δ+η<ε
    closeToComputedKit .InductionKit.squash* {x = x} {y = y} {ε = ε} p a b =
      isPropComputedClose x y ε

    module CloseToComputed = Induction closeToComputedKit


  close→computed :
    {x y : Completion} {ε : ℚ⁺} →
    x ∼[ ε ] y →
    ComputedClose ε x y
  close→computed =
    CloseToComputed.ind-close


  computed→close :
    (x y : Completion) (ε : ℚ⁺) →
    ComputedClose ε x y →
    x ∼[ ε ] y
  computed→close =
    PropInduction.ind kit
    where
    kit : PropInductionKit ℓᶜ
    kit .PropInductionKit.A x =
      (y : Completion) (ε : ℚ⁺) →
      ComputedClose ε x y →
      x ∼[ ε ] y
    kit .PropInductionKit.isPropA x =
      isPropΠ2 λ y ε →
        isPropΠ λ _ →
          squash
    kit .PropInductionKit.point* a =
      computedPoint→close a
    kit .PropInductionKit.limit* x xClose =
      PropInduction.ind targetKit
      where
      targetKit : PropInductionKit ℓᶜ
      targetKit .PropInductionKit.A y =
        (ε : ℚ⁺) →
        ComputedClose ε (limit x) y →
        limit x ∼[ ε ] y
      targetKit .PropInductionKit.isPropA y =
        isPropΠ2 λ ε _ →
          squash
      targetKit .PropInductionKit.point* a ε =
        Prop.rec squash step
        where
        step :
          Σ[ δ ∈ ℚ⁺ ]
            Σ[ δ<ε ∈ δ <⁺ ε ]
            ComputedClose (ε ⊖ δ [ δ<ε ]) (approximate x δ) (point a) →
          limit x ∼[ ε ] point a
        step (δ , δ<ε , xδ∼a) =
          limit-point-close x a ε δ δ<ε
            (xClose δ (point a) (ε ⊖ δ [ δ<ε ]) xδ∼a)

      targetKit .PropInductionKit.limit* y yClose ε =
        Prop.rec squash step
        where
        refine :
          (δ : ℚ⁺) →
          (δ<ε : δ <⁺ ε) →
          Σ[ η ∈ ℚ⁺ ]
            Σ[ η<ε-δ ∈ η <⁺ ε ⊖ δ [ δ<ε ] ]
            ComputedClose
              ((ε ⊖ δ [ δ<ε ]) ⊖ η [ η<ε-δ ])
              (approximate x δ)
              (approximate y η) →
          limit x ∼[ ε ] limit y
        refine δ δ<ε (η , η<ε-δ , xδ∼yη) =
          limit-limit-close x y ε δ η δ+η<ε
            (subst
              (λ ρ → approximate x δ ∼[ ρ ] approximate y η)
              (difference-difference-sum ε δ η δ+η<ε δ<ε η<ε-δ)
              (xClose δ (approximate y η)
                ((ε ⊖ δ [ δ<ε ]) ⊖ η [ η<ε-δ ])
                xδ∼yη))
          where
          δ+η<ε : δ +⁺ η <⁺ ε
          δ+η<ε =
            sum<from-difference ε δ η δ<ε η<ε-δ

        step :
          Σ[ δ ∈ ℚ⁺ ]
            Σ[ δ<ε ∈ δ <⁺ ε ]
            ComputedClose (ε ⊖ δ [ δ<ε ]) (approximate x δ) (limit y) →
          limit x ∼[ ε ] limit y
        step (δ , δ<ε , xδ∼lim) =
          Prop.rec squash (refine δ δ<ε)
            (targetLimitElim (approximate x δ) y (ε ⊖ δ [ δ<ε ]) xδ∼lim)


  close-triangle :
    {x y z : Completion} {η ε : ℚ⁺} →
    x ∼[ η ] y →
    y ∼[ ε ] z →
    x ∼[ η +⁺ ε ] z
  close-triangle {x = x} {y = y} {z = z} {η = η} {ε = ε} x∼y y∼z =
    computed→close x z (η +⁺ ε)
      (subst
        (λ ρ → ComputedClose ρ x z)
        (+⁺-comm ε η)
        (snd (computedRelation x∼y z ε) (close→computed y∼z)))


  pointConstructorTriangle :
    (a b : A) {u : Completion} {η ε : ℚ⁺} →
    MetricSpace.Close 𝓜 a η b →
    point b ∼[ ε ] u →
    point a ∼[ η +⁺ ε ] u
  pointConstructorTriangle a b {u = u} {η = η} {ε = ε} a∼b b∼u =
    computedPoint→close a u (η +⁺ ε)
      (PredicateStructure.mixedRight (pointSourceBundle a .snd)
        (point b) u ε η b∼u a∼b)
