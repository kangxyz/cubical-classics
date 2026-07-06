{-

Computed alternative closeness, rational source case

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Closeness.Internal.Computed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit* ; tt* ; isPropUnit*)
open import Cubical.Data.Rationals using (ℚ)
open import Cubical.HITs.PropositionalTruncation as Prop

open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Closeness.Internal.Prelength
open import Constructive.CauchyReals.Induction
open import Constructive.CauchyReals.Recursion


private
  isPropPrecisionRelation :
    (P Q : PrecisionBundle) (ε : ℚ⁺) →
    isProp (PrecisionRelation P Q ε)
  isPropPrecisionRelation P Q ε =
    isPropΠ λ η →
      isProp×
        (isProp→ (PrecisionStructure.isPropP (Q .snd) (η +⁺ ε)))
        (isProp→ (PrecisionStructure.isPropP (P .snd) (η +⁺ ε)))

  rationalTargetKit : ℚ → RecursionKit (ℓ-suc ℓ-zero) ℓ-zero
  rationalTargetKit q .RecursionKit.A =
    PrecisionBundle
  rationalTargetKit q .RecursionKit.B =
    λ ε P Q → PrecisionRelation P Q ε
  rationalTargetKit q .RecursionKit.isPropB =
    λ ε P Q → isPropPrecisionRelation P Q ε
  rationalTargetKit q .RecursionKit.separated =
    precision-separated
  rationalTargetKit q .RecursionKit.rational* =
    rationalPrecisionBundle q
  rationalTargetKit q .RecursionKit.limit* y f fCauchy =
    rationalLimitPrecisionBundle f
  rationalTargetKit q .RecursionKit.rational-rational* r s ε r∼s =
    rationalPrecisionRelation q r s ε r∼s
  rationalTargetKit q .RecursionKit.rational-limit* r ε δ δ<ε y g gCauchy r∼gδ =
    rationalLimitPrecisionRelation
      (rationalPrecisionBundle q r)
      g
      gCauchy
      ε δ δ<ε
      r∼gδ
  rationalTargetKit q .RecursionKit.limit-rational* y f fCauchy r ε δ δ<ε fδ∼r =
    limitRationalPrecisionRelation
      f
      (rationalPrecisionBundle q r)
      fCauchy
      ε δ δ<ε
      fδ∼r
  rationalTargetKit q .RecursionKit.limit-limit* x y f g fCauchy gCauchy ε δ η δ+η<ε fδ∼gη =
    limitLimitPrecisionRelation
      f g
      fCauchy gCauchy
      ε δ η δ+η<ε
      fδ∼gη

  module RationalTarget (q : ℚ) = Recursion (rationalTargetKit q)


rationalSourceBundle : ℚ → PredicateBundle
rationalSourceBundle q .fst u ε =
  precisionPredicate (RationalTarget.rec q u) ε
rationalSourceBundle q .snd .PredicateStructure.isPropP u ε =
  PrecisionStructure.isPropP (RationalTarget.rec q u .snd) ε
rationalSourceBundle q .snd .PredicateStructure.rounded u ε =
  PrecisionStructure.rounded (RationalTarget.rec q u .snd) ε
rationalSourceBundle q .snd .PredicateStructure.mixedRight u v ε η u∼v =
  fst (RationalTarget.rec-close q u∼v η)
rationalSourceBundle q .snd .PredicateStructure.mixedLeft u v ε η u∼v =
  snd (RationalTarget.rec-close q u∼v η)


ComputedRationalClose : ℚ → ℝᶜ → ℚ⁺ → Type₀
ComputedRationalClose q u ε =
  bundlePredicate (rationalSourceBundle q) u ε


computedRational→close :
  (q : ℚ) (u : ℝᶜ) (ε : ℚ⁺) →
  ComputedRationalClose q u ε →
  rational q ∼[ ε ] u
computedRational→close q =
  PropInduction.ind kit
  where
  kit : PropInductionKit ℓ-zero
  kit .PropInductionKit.A u =
    (ε : ℚ⁺) →
    ComputedRationalClose q u ε →
    rational q ∼[ ε ] u
  kit .PropInductionKit.isPropA u =
    isPropΠ2 λ ε _ → squash
  kit .PropInductionKit.rational* r ε =
    rational-rational-close q r ε
  kit .PropInductionKit.limit* y yClose ε =
    Prop.rec squash step
    where
    step :
      Σ[ δ ∈ ℚ⁺ ]
        Σ[ δ<ε ∈ δ <⁺ ε ]
        ComputedRationalClose q (approximate y δ) (ε ⊖ δ [ δ<ε ]) →
      rational q ∼[ ε ] limit y
    step (δ , δ<ε , q∼yδ) =
      rational-limit-close q ε δ δ<ε y
        (yClose δ (ε ⊖ δ [ δ<ε ]) q∼yδ)


private
  isPropRelation :
    (P Q : PredicateBundle) (ε : ℚ⁺) →
    isProp (Relation P Q ε)
  isPropRelation P Q ε =
    isPropΠ2 λ u η →
      isProp×
        (isProp→ (PredicateStructure.isPropP (Q .snd) u (η +⁺ ε)))
        (isProp→ (PredicateStructure.isPropP (P .snd) u (η +⁺ ε)))


rationalSourceRelation :
  (q r : ℚ) (ε : ℚ⁺) →
  Closeℚ q ε r →
  Relation (rationalSourceBundle q) (rationalSourceBundle r) ε
rationalSourceRelation q r ε q∼r u η =
  forward , backward
  where
  forward :
    ComputedRationalClose q u η →
    ComputedRationalClose r u (η +⁺ ε)
  forward q∼u =
    subst
      (ComputedRationalClose r u)
      (+⁺-comm ε η)
      (PredicateStructure.mixedRight (rationalSourceBundle r .snd)
        (rational q) u η ε
        (computedRational→close q u η q∼u)
        (rational-close-sym q r ε q∼r))

  backward :
    ComputedRationalClose r u η →
    ComputedRationalClose q u (η +⁺ ε)
  backward r∼u =
    subst
      (ComputedRationalClose q u)
      (+⁺-comm ε η)
      (PredicateStructure.mixedRight (rationalSourceBundle q .snd)
        (rational r) u η ε
        (computedRational→close r u η r∼u)
        q∼r)


private
  sourceKit : RecursionKit (ℓ-suc ℓ-zero) ℓ-zero
  sourceKit .RecursionKit.A =
    PredicateBundle
  sourceKit .RecursionKit.B =
    λ ε P Q → Relation P Q ε
  sourceKit .RecursionKit.isPropB =
    λ ε P Q → isPropRelation P Q ε
  sourceKit .RecursionKit.separated =
    bundle-separated
  sourceKit .RecursionKit.rational* =
    rationalSourceBundle
  sourceKit .RecursionKit.limit* x f fCauchy =
    limitSourceBundle f
  sourceKit .RecursionKit.rational-rational* q r ε q∼r =
    rationalSourceRelation q r ε q∼r
  sourceKit .RecursionKit.rational-limit* q ε δ δ<ε y g gCauchy q∼gδ =
    sourceLimitRelation
      (rationalSourceBundle q)
      g
      gCauchy
      ε δ δ<ε
      q∼gδ
  sourceKit .RecursionKit.limit-rational* x f fCauchy r ε δ δ<ε fδ∼r =
    limitSourceRelation
      f
      (rationalSourceBundle r)
      fCauchy
      ε δ δ<ε
      fδ∼r
  sourceKit .RecursionKit.limit-limit* x y f g fCauchy gCauchy ε δ η δ+η<ε fδ∼gη =
    limitLimitSourceRelation
      f g
      fCauchy gCauchy
      ε δ η δ+η<ε
      fδ∼gη

  module Source = Recursion sourceKit


computedBundle : ℝᶜ → PredicateBundle
computedBundle =
  Source.rec


ComputedClose : ℚ⁺ → ℝᶜ → ℝᶜ → Type₀
ComputedClose ε x y =
  bundlePredicate (computedBundle x) y ε


isPropComputedClose :
  (x y : ℝᶜ) (ε : ℚ⁺) →
  isProp (ComputedClose ε x y)
isPropComputedClose x y ε =
  PredicateStructure.isPropP (computedBundle x .snd) y ε


computedRelation :
  {x y : ℝᶜ} {ε : ℚ⁺} →
  x ∼[ ε ] y →
  Relation (computedBundle x) (computedBundle y) ε
computedRelation =
  Source.rec-close


targetLimitIntro :
  (x : ℝᶜ) (y : CauchyApproximation) (ε η : ℚ⁺) →
  (η<ε : η <⁺ ε) →
  ComputedClose (ε ⊖ η [ η<ε ]) x (approximate y η) →
  ComputedClose ε x (limit y)
targetLimitIntro =
  PropInduction.ind kit
  where
  kit : PropInductionKit ℓ-zero
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
  kit .PropInductionKit.rational* q y ε η η<ε q∼yη =
    ∣ η , η<ε , q∼yη ∣₁
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
  (x : ℝᶜ) (y : CauchyApproximation) (ε : ℚ⁺) →
  ComputedClose ε x (limit y) →
  ∥ Σ[ η ∈ ℚ⁺ ]
      Σ[ η<ε ∈ η <⁺ ε ]
      ComputedClose (ε ⊖ η [ η<ε ]) x (approximate y η)
  ∥₁
targetLimitElim =
  PropInduction.ind kit
  where
  kit : PropInductionKit ℓ-zero
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
  kit .PropInductionKit.rational* q y ε q∼lim =
    q∼lim
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
  closeToComputedKit : InductionKit ℓ-zero ℓ-zero
  closeToComputedKit .InductionKit.A x =
    Unit*
  closeToComputedKit .InductionKit.B ε {x = x} {y = y} x∼y _ _ =
    ComputedClose ε x y
  closeToComputedKit .InductionKit.rational* q =
    tt*
  closeToComputedKit .InductionKit.limit* x a aCauchy =
    tt*
  closeToComputedKit .InductionKit.path* x y x∼y a b close* =
    isProp→PathP (λ i → isPropUnit*) a b
  closeToComputedKit .InductionKit.rational-rational* q r ε q∼r =
    q∼r
  closeToComputedKit .InductionKit.rational-limit* q ε δ δ<ε y b bCauchy q∼yδ q∼bδ =
    ∣ δ , δ<ε , q∼bδ ∣₁
  closeToComputedKit .InductionKit.limit-rational* x a aCauchy r ε δ δ<ε xδ∼r aδ∼r =
    ∣ δ , δ<ε , aδ∼r ∣₁
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
  {x y : ℝᶜ} {ε : ℚ⁺} →
  x ∼[ ε ] y →
  ComputedClose ε x y
close→computed =
  CloseToComputed.ind-close


computed→close :
  (x y : ℝᶜ) (ε : ℚ⁺) →
  ComputedClose ε x y →
  x ∼[ ε ] y
computed→close =
  PropInduction.ind kit
  where
  kit : PropInductionKit ℓ-zero
  kit .PropInductionKit.A x =
    (y : ℝᶜ) (ε : ℚ⁺) →
    ComputedClose ε x y →
    x ∼[ ε ] y
  kit .PropInductionKit.isPropA x =
    isPropΠ2 λ y ε →
      isPropΠ λ _ →
        squash
  kit .PropInductionKit.rational* q =
    computedRational→close q
  kit .PropInductionKit.limit* x xClose =
    PropInduction.ind targetKit
    where
    targetKit : PropInductionKit ℓ-zero
    targetKit .PropInductionKit.A y =
      (ε : ℚ⁺) →
      ComputedClose ε (limit x) y →
      limit x ∼[ ε ] y
    targetKit .PropInductionKit.isPropA y =
      isPropΠ2 λ ε _ →
        squash
    targetKit .PropInductionKit.rational* r ε =
      Prop.rec squash step
      where
      step :
        Σ[ δ ∈ ℚ⁺ ]
          Σ[ δ<ε ∈ δ <⁺ ε ]
          ComputedClose (ε ⊖ δ [ δ<ε ]) (approximate x δ) (rational r) →
        limit x ∼[ ε ] rational r
      step (δ , δ<ε , xδ∼r) =
        limit-rational-close x r ε δ δ<ε
          (xClose δ (rational r) (ε ⊖ δ [ δ<ε ]) xδ∼r)

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
  {x y z : ℝᶜ} {η ε : ℚ⁺} →
  x ∼[ η ] y →
  y ∼[ ε ] z →
  x ∼[ η +⁺ ε ] z
close-triangle {x = x} {y = y} {z = z} {η = η} {ε = ε} x∼y y∼z =
  computed→close x z (η +⁺ ε)
    (subst
      (λ ρ → ComputedClose ρ x z)
      (+⁺-comm ε η)
      (snd (computedRelation x∼y z ε) (close→computed y∼z)))


rationalConstructorTriangle :
  (q r : ℚ) {u : ℝᶜ} {η ε : ℚ⁺} →
  Closeℚ q η r →
  rational r ∼[ ε ] u →
  rational q ∼[ η +⁺ ε ] u
rationalConstructorTriangle q r {u = u} {η = η} {ε = ε} q∼r r∼u =
  computedRational→close q u (η +⁺ ε)
    (PredicateStructure.mixedRight (rationalSourceBundle q .snd)
      (rational r) u ε η r∼u q∼r)
