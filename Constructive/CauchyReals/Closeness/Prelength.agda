{-

Prelength-style predicate bundles for alternative closeness

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Closeness.Prelength where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
  using (ℚCommRing)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.CauchyReals.Base


Predicate : Type₁
Predicate = ℝᶜ → ℚ⁺ → Type₀


PrecisionPredicate : Type₁
PrecisionPredicate = ℚ⁺ → Type₀


PrecisionRounded : PrecisionPredicate → Type₀
PrecisionRounded P =
  (ε : ℚ⁺) →
  (P ε → ∥ Σ[ δ ∈ ℚ⁺ ] (δ <⁺ ε) × P δ ∥₁) ×
  (∥ Σ[ δ ∈ ℚ⁺ ] (δ <⁺ ε) × P δ ∥₁ → P ε)


record PrecisionStructure (P : PrecisionPredicate) : Type₀ where
  no-eta-equality

  field
    isPropP : (ε : ℚ⁺) → isProp (P ε)
    rounded : PrecisionRounded P


PrecisionBundle : Type₁
PrecisionBundle = Σ[ P ∈ PrecisionPredicate ] PrecisionStructure P


precisionPredicate : PrecisionBundle → PrecisionPredicate
precisionPredicate = fst


PrecisionRelation : PrecisionBundle → PrecisionBundle → ℚ⁺ → Type₀
PrecisionRelation P Q ε =
  (η : ℚ⁺) →
  (precisionPredicate P η → precisionPredicate Q (η +⁺ ε)) ×
  (precisionPredicate Q η → precisionPredicate P (η +⁺ ε))


precisionRelation-sym :
  {P Q : PrecisionBundle} {ε : ℚ⁺} →
  PrecisionRelation P Q ε →
  PrecisionRelation Q P ε
precisionRelation-sym rel η =
  snd (rel η) , fst (rel η)


Rounded : Predicate → Type₀
Rounded P =
  (u : ℝᶜ) (ε : ℚ⁺) →
  (P u ε → ∥ Σ[ δ ∈ ℚ⁺ ] (δ <⁺ ε) × P u δ ∥₁) ×
  (∥ Σ[ δ ∈ ℚ⁺ ] (δ <⁺ ε) × P u δ ∥₁ → P u ε)


MixedRight : Predicate → Type₀
MixedRight P =
  (u v : ℝᶜ) (ε η : ℚ⁺) →
  u ∼[ ε ] v →
  P u η →
  P v (η +⁺ ε)


MixedLeft : Predicate → Type₀
MixedLeft P =
  (u v : ℝᶜ) (ε η : ℚ⁺) →
  u ∼[ ε ] v →
  P v η →
  P u (η +⁺ ε)


record PredicateStructure (P : Predicate) : Type₀ where
  no-eta-equality

  field
    isPropP : (u : ℝᶜ) (ε : ℚ⁺) → isProp (P u ε)
    rounded : Rounded P
    mixedRight : MixedRight P
    mixedLeft : MixedLeft P


PredicateBundle : Type₁
PredicateBundle = Σ[ P ∈ Predicate ] PredicateStructure P


bundlePredicate : PredicateBundle → Predicate
bundlePredicate = fst


Relation : PredicateBundle → PredicateBundle → ℚ⁺ → Type₀
Relation P Q ε =
  (u : ℝᶜ) (η : ℚ⁺) →
  (bundlePredicate P u η → bundlePredicate Q u (η +⁺ ε)) ×
  (bundlePredicate Q u η → bundlePredicate P u (η +⁺ ε))


relation-sym :
  {P Q : PredicateBundle} {ε : ℚ⁺} →
  Relation P Q ε →
  Relation Q P ε
relation-sym rel u η =
  snd (rel u η) , fst (rel u η)


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    shift-difference-sum :
      (η ε δ : 𝓡 .fst) →
      (η + ε) - δ ≡ η + (ε - δ)
    shift-difference-sum _ _ _ = solve! 𝓡

    source-shift :
      (η ε δ : 𝓡 .fst) →
      (η + ε) - δ ≡ (η - δ) + ε
    source-shift _ _ _ = solve! 𝓡

    limit-cauchy-shift :
      (η θ δ : 𝓡 .fst) →
      (η - θ) + (θ + δ) ≡ δ + η
    limit-cauchy-shift _ _ _ = solve! 𝓡

    limit-relation-shift :
      (η ε δ : 𝓡 .fst) →
      (δ + η) + (ε - δ) ≡ η + ε
    limit-relation-shift _ _ _ = solve! 𝓡

    limit-limit-relation-shift :
      (θ ε δ η : 𝓡 .fst) →
      (δ + θ) + (ε - (δ + η)) ≡ (θ + ε) - η
    limit-limit-relation-shift _ _ _ _ = solve! 𝓡

    double-difference-sum :
      (ε δ η : 𝓡 .fst) →
      (ε - δ) - η ≡ ε - (δ + η)
    double-difference-sum _ _ _ = solve! 𝓡

    double-difference-comm :
      (ε δ η : 𝓡 .fst) →
      (ε - δ) - η ≡ (ε - η) - δ
    double-difference-comm _ _ _ = solve! 𝓡

  sum-right<sum : (ε δ : ℚ⁺) → δ <⁺ ε +⁺ δ
  sum-right<sum ε δ =
    subst
      (λ q → radius δ ℚOrder.< q)
      (ℚ.+Comm (radius δ) (radius ε))
      (summand-left<sum δ ε)

  right<sum :
    (ε : ℚ⁺) {δ η : ℚ⁺} →
    δ <⁺ η →
    δ <⁺ ε +⁺ η
  right<sum ε {δ = δ} {η = η} δ<η =
    <⁺-trans {ε = δ} {δ = η} {η = ε +⁺ η}
      δ<η
      (sum-right<sum ε η)

  left<sum :
    (δ : ℚ⁺) {α ε : ℚ⁺} →
    α <⁺ ε →
    α <⁺ ε +⁺ δ
  left<sum δ {α = α} {ε = ε} α<ε =
    <⁺-trans {ε = α} {δ = ε} {η = ε +⁺ δ}
      α<ε
      (summand-left<sum ε δ)

  first-summand< :
    {δ η ε : ℚ⁺} →
    δ +⁺ η <⁺ ε →
    δ <⁺ ε
  first-summand< {δ = δ} {η = η} {ε = ε} δ+η<ε =
    <⁺-trans {ε = δ} {δ = δ +⁺ η} {η = ε}
      (summand-left<sum δ η)
      δ+η<ε

  second-summand< :
    {δ η ε : ℚ⁺} →
    δ +⁺ η <⁺ ε →
    η <⁺ ε
  second-summand< {δ = δ} {η = η} {ε = ε} δ+η<ε =
    <⁺-trans {ε = η} {δ = δ +⁺ η} {η = ε}
      (sum-right<sum δ η)
      δ+η<ε

  shift-difference-sum :
    (η ε δ : ℚ⁺) →
    (δ<ε : δ <⁺ ε) →
    (δ<η+ε : δ <⁺ η +⁺ ε) →
    (η +⁺ ε) ⊖ δ [ δ<η+ε ] ≡
    η +⁺ (ε ⊖ δ [ δ<ε ])
  shift-difference-sum η ε δ δ<ε δ<η+ε =
    ℚ⁺Path
      (SolverHelpers.shift-difference-sum ℚCommRing
        (radius η) (radius ε) (radius δ))

  source-shift :
    (η ε δ : ℚ⁺) →
    (δ<η : δ <⁺ η) →
    (δ<η+ε : δ <⁺ η +⁺ ε) →
    (η +⁺ ε) ⊖ δ [ δ<η+ε ] ≡
    (η ⊖ δ [ δ<η ]) +⁺ ε
  source-shift η ε δ δ<η δ<η+ε =
    ℚ⁺Path
      (SolverHelpers.source-shift ℚCommRing
        (radius η) (radius ε) (radius δ))

  limit-cauchy-shift :
    (η θ δ : ℚ⁺) →
    (θ<η : θ <⁺ η) →
    (η ⊖ θ [ θ<η ]) +⁺ (θ +⁺ δ) ≡ δ +⁺ η
  limit-cauchy-shift η θ δ θ<η =
    ℚ⁺Path
      (SolverHelpers.limit-cauchy-shift ℚCommRing
        (radius η) (radius θ) (radius δ))

  limit-relation-shift :
    (η ε δ : ℚ⁺) →
    (δ<ε : δ <⁺ ε) →
    (δ +⁺ η) +⁺ (ε ⊖ δ [ δ<ε ]) ≡ η +⁺ ε
  limit-relation-shift η ε δ δ<ε =
    ℚ⁺Path
      (SolverHelpers.limit-relation-shift ℚCommRing
        (radius η) (radius ε) (radius δ))

  limit-limit-relation-shift :
    (θ ε δ η : ℚ⁺) →
    (δ+η<ε : δ +⁺ η <⁺ ε) →
    (η<θ+ε : η <⁺ θ +⁺ ε) →
    (δ +⁺ θ) +⁺ (ε ⊖ (δ +⁺ η) [ δ+η<ε ]) ≡
    (θ +⁺ ε) ⊖ η [ η<θ+ε ]
  limit-limit-relation-shift θ ε δ η δ+η<ε η<θ+ε =
    ℚ⁺Path
      (SolverHelpers.limit-limit-relation-shift ℚCommRing
        (radius θ) (radius ε) (radius δ) (radius η))

  sum-comm-< :
    (ε δ η : ℚ⁺) →
    δ +⁺ η <⁺ ε →
    η +⁺ δ <⁺ ε
  sum-comm-< ε δ η δ+η<ε =
    subst
      (λ q → q ℚOrder.< radius ε)
      (ℚ.+Comm (radius δ) (radius η))
      δ+η<ε

  difference-sum-comm :
    (ε δ η : ℚ⁺) →
    (δ+η<ε : δ +⁺ η <⁺ ε) →
    (η+δ<ε : η +⁺ δ <⁺ ε) →
    ε ⊖ (δ +⁺ η) [ δ+η<ε ] ≡
    ε ⊖ (η +⁺ δ) [ η+δ<ε ]
  difference-sum-comm ε δ η δ+η<ε η+δ<ε =
    ℚ⁺Path (cong (λ q → radius ε ℚ.- q) (ℚ.+Comm (radius δ) (radius η)))

  isPropPrecisionStructure :
    (P : PrecisionPredicate) →
    isProp (PrecisionStructure P)
  isPropPrecisionStructure P s t i .PrecisionStructure.isPropP ε =
    isPropIsProp (s .PrecisionStructure.isPropP ε)
      (t .PrecisionStructure.isPropP ε) i
  isPropPrecisionStructure P s t i .PrecisionStructure.rounded =
    isPropΠ
      (λ ε →
        isProp×
          (isProp→ squash₁)
          (isProp→ (s .PrecisionStructure.isPropP ε)))
      (s .PrecisionStructure.rounded)
      (t .PrecisionStructure.rounded)
      i

  isPropPredicateStructure :
    (P : Predicate) →
    isProp (PredicateStructure P)
  isPropPredicateStructure P s t i .PredicateStructure.isPropP u ε =
    isPropIsProp (s .PredicateStructure.isPropP u ε)
      (t .PredicateStructure.isPropP u ε) i
  isPropPredicateStructure P s t i .PredicateStructure.rounded =
    isPropΠ2
      (λ u ε →
        isProp×
          (isProp→ squash₁)
          (isProp→ (s .PredicateStructure.isPropP u ε)))
      (s .PredicateStructure.rounded)
      (t .PredicateStructure.rounded)
      i
  isPropPredicateStructure P s t i .PredicateStructure.mixedRight =
    isPropΠ5
      (λ u v ε η _ →
        isProp→ (s .PredicateStructure.isPropP v (η +⁺ ε)))
      (s .PredicateStructure.mixedRight)
      (t .PredicateStructure.mixedRight)
      i
  isPropPredicateStructure P s t i .PredicateStructure.mixedLeft =
    isPropΠ5
      (λ u v ε η _ →
        isProp→ (s .PredicateStructure.isPropP u (η +⁺ ε)))
      (s .PredicateStructure.mixedLeft)
      (t .PredicateStructure.mixedLeft)
      i

  sum-difference-cancel :
    (ε δ : ℚ⁺) →
    (δ<ε : δ <⁺ ε) →
    δ +⁺ (ε ⊖ δ [ δ<ε ]) ≡ ε
  sum-difference-cancel ε δ δ<ε =
    ℚ⁺Path (sum-difference-cancel-left ε δ)


precision-separated :
  (P Q : PrecisionBundle) →
  ((ε : ℚ⁺) → PrecisionRelation P Q ε) →
  P ≡ Q
precision-separated P Q rel =
  Σ≡Prop isPropPrecisionStructure predicate-path
  where
  module P = PrecisionStructure (P .snd)
  module Q = PrecisionStructure (Q .snd)

  to :
    (ε : ℚ⁺) →
    precisionPredicate P ε →
    precisionPredicate Q ε
  to ε p =
    Prop.rec (Q.isPropP ε) step (fst (P.rounded ε) p)
    where
    step :
      Σ[ δ ∈ ℚ⁺ ] (δ <⁺ ε) × precisionPredicate P δ →
      precisionPredicate Q ε
    step (δ , δ<ε , pδ) =
      subst
        (precisionPredicate Q)
        (sum-difference-cancel ε δ δ<ε)
        (fst (rel (ε ⊖ δ [ δ<ε ]) δ) pδ)

  from :
    (ε : ℚ⁺) →
    precisionPredicate Q ε →
    precisionPredicate P ε
  from ε q =
    Prop.rec (P.isPropP ε) step (fst (Q.rounded ε) q)
    where
    step :
      Σ[ δ ∈ ℚ⁺ ] (δ <⁺ ε) × precisionPredicate Q δ →
      precisionPredicate P ε
    step (δ , δ<ε , qδ) =
      subst
        (precisionPredicate P)
        (sum-difference-cancel ε δ δ<ε)
        (snd (rel (ε ⊖ δ [ δ<ε ]) δ) qδ)

  predicate-path : precisionPredicate P ≡ precisionPredicate Q
  predicate-path =
    funExt λ ε →
      ua (propBiimpl→Equiv
        (P.isPropP ε)
        (Q.isPropP ε)
        (to ε)
        (from ε))


bundle-separated :
  (P Q : PredicateBundle) →
  ((ε : ℚ⁺) → Relation P Q ε) →
  P ≡ Q
bundle-separated P Q rel =
  Σ≡Prop isPropPredicateStructure predicate-path
  where
  module P = PredicateStructure (P .snd)
  module Q = PredicateStructure (Q .snd)

  to :
    (u : ℝᶜ) (ε : ℚ⁺) →
    bundlePredicate P u ε →
    bundlePredicate Q u ε
  to u ε p =
    Prop.rec (Q.isPropP u ε) step (fst (P.rounded u ε) p)
    where
    step :
      Σ[ δ ∈ ℚ⁺ ] (δ <⁺ ε) × bundlePredicate P u δ →
      bundlePredicate Q u ε
    step (δ , δ<ε , pδ) =
      subst
        (bundlePredicate Q u)
        (sum-difference-cancel ε δ δ<ε)
        (fst (rel (ε ⊖ δ [ δ<ε ]) u δ) pδ)

  from :
    (u : ℝᶜ) (ε : ℚ⁺) →
    bundlePredicate Q u ε →
    bundlePredicate P u ε
  from u ε q =
    Prop.rec (P.isPropP u ε) step (fst (Q.rounded u ε) q)
    where
    step :
      Σ[ δ ∈ ℚ⁺ ] (δ <⁺ ε) × bundlePredicate Q u δ →
      bundlePredicate P u ε
    step (δ , δ<ε , qδ) =
      subst
        (bundlePredicate P u)
        (sum-difference-cancel ε δ δ<ε)
        (snd (rel (ε ⊖ δ [ δ<ε ]) u δ) qδ)

  predicate-path : bundlePredicate P ≡ bundlePredicate Q
  predicate-path =
    funExt λ u →
    funExt λ ε →
      ua (propBiimpl→Equiv
        (P.isPropP u ε)
        (Q.isPropP u ε)
        (to u ε)
        (from u ε))


precision-mono :
  (P : PrecisionBundle) →
  {ε δ : ℚ⁺} →
  ε <⁺ δ →
  precisionPredicate P ε →
  precisionPredicate P δ
precision-mono P {ε = ε} {δ = δ} ε<δ p =
  snd (PrecisionStructure.rounded (P .snd) δ)
    ∣ ε , ε<δ , p ∣₁


bundle-mono :
  (P : PredicateBundle) →
  (u : ℝᶜ) →
  {ε δ : ℚ⁺} →
  ε <⁺ δ →
  bundlePredicate P u ε →
  bundlePredicate P u δ
bundle-mono P u {ε = ε} {δ = δ} ε<δ p =
  snd (PredicateStructure.rounded (P .snd) u δ)
    ∣ ε , ε<δ , p ∣₁


rationalPrecisionBundle : ℚ → ℚ → PrecisionBundle
rationalPrecisionBundle q r .fst ε =
  Closeℚ q ε r
rationalPrecisionBundle q r .snd .PrecisionStructure.isPropP ε =
  isPropCloseℚ q ε r
rationalPrecisionBundle q r .snd .PrecisionStructure.rounded ε =
  rational-close-rounded q r ε ,
  Prop.rec (isPropCloseℚ q ε r)
    (λ (δ , δ<ε , q∼r) →
      rational-close-mono q r δ ε δ<ε q∼r)


rationalPrecisionRelation :
  (q r s : ℚ) (ε : ℚ⁺) →
  Closeℚ r ε s →
  PrecisionRelation
    (rationalPrecisionBundle q r)
    (rationalPrecisionBundle q s)
    ε
rationalPrecisionRelation q r s ε r∼s η =
  (λ q∼r → rational-close-triangle q r s η ε q∼r r∼s) ,
  (λ q∼s →
    rational-close-triangle q s r η ε q∼s
      (rational-close-sym r s ε r∼s))


rationalLimitPrecisionBundle :
  (f : ℚ⁺ → PrecisionBundle) →
  PrecisionBundle
rationalLimitPrecisionBundle f .fst ε =
  ∥ Σ[ δ ∈ ℚ⁺ ]
      Σ[ δ<ε ∈ δ <⁺ ε ]
      precisionPredicate (f δ) (ε ⊖ δ [ δ<ε ])
  ∥₁
rationalLimitPrecisionBundle f .snd .PrecisionStructure.isPropP ε =
  squash₁
rationalLimitPrecisionBundle f .snd .PrecisionStructure.rounded ε =
  openP , monotoneP
  where
  P : PrecisionPredicate
  P = rationalLimitPrecisionBundle f .fst

  openP :
    P ε →
    ∥ Σ[ ζ ∈ ℚ⁺ ] (ζ <⁺ ε) × P ζ ∥₁
  openP =
    Prop.rec squash₁ λ (δ , δ<ε , fδ-close) →
      Prop.rec squash₁ (step δ δ<ε) (fst (PrecisionStructure.rounded (f δ .snd) _) fδ-close)
    where
    step :
      (δ : ℚ⁺) →
      (δ<ε : δ <⁺ ε) →
      Σ[ κ ∈ ℚ⁺ ]
        (κ <⁺ (ε ⊖ δ [ δ<ε ])) ×
        precisionPredicate (f δ) κ →
      ∥ Σ[ ζ ∈ ℚ⁺ ] (ζ <⁺ ε) × P ζ ∥₁
    step δ δ<ε (κ , κ<ε-δ , fδκ) =
      ∣ ζ , ζ<ε , ∣ δ , δ<ζ ,
          subst
            (precisionPredicate (f δ))
            (sym ζ-δ≡κ)
            fδκ
        ∣₁
      ∣₁
      where
      ζ : ℚ⁺
      ζ = δ +⁺ κ

      δ<ζ : δ <⁺ ζ
      δ<ζ = summand-left<sum δ κ

      ζ<ε : ζ <⁺ ε
      ζ<ε = sum<from-difference ε δ κ δ<ε κ<ε-δ

      ζ-δ≡κ : ζ ⊖ δ [ δ<ζ ] ≡ κ
      ζ-δ≡κ = sum-difference-left δ κ δ<ζ

  monotoneP :
    ∥ Σ[ ζ ∈ ℚ⁺ ] (ζ <⁺ ε) × P ζ ∥₁ →
    P ε
  monotoneP =
    Prop.rec squash₁ λ (ζ , ζ<ε , pζ) →
      Prop.rec squash₁ (step ζ ζ<ε) pζ
    where
    step :
      (ζ : ℚ⁺) →
      (ζ<ε : ζ <⁺ ε) →
      Σ[ δ ∈ ℚ⁺ ]
        Σ[ δ<ζ ∈ δ <⁺ ζ ]
        precisionPredicate (f δ) (ζ ⊖ δ [ δ<ζ ]) →
      P ε
    step ζ ζ<ε (δ , δ<ζ , fδ-close) =
      ∣ δ , δ<ε ,
          precision-mono (f δ)
            {ε = ζ ⊖ δ [ δ<ζ ]}
            {δ = ε ⊖ δ [ δ<ε ]}
            (difference-mono-left ζ ε δ δ<ζ δ<ε ζ<ε)
            fδ-close
      ∣₁
      where
      δ<ε : δ <⁺ ε
      δ<ε = <⁺-trans {ε = δ} {δ = ζ} {η = ε} δ<ζ ζ<ε


rationalLimitPrecisionForward :
  (R : PrecisionBundle) →
  (f : ℚ⁺ → PrecisionBundle) →
  (ε δ : ℚ⁺) →
  (δ<ε : δ <⁺ ε) →
  PrecisionRelation R (f δ) (ε ⊖ δ [ δ<ε ]) →
  (η : ℚ⁺) →
  precisionPredicate R η →
  precisionPredicate (rationalLimitPrecisionBundle f) (η +⁺ ε)
rationalLimitPrecisionForward R f ε δ δ<ε rel η rη =
  ∣ δ , δ<η+ε ,
      subst
        (precisionPredicate (f δ))
        (sym (shift-difference-sum η ε δ δ<ε δ<η+ε))
        (fst (rel η) rη)
  ∣₁
  where
  δ<η+ε : δ <⁺ η +⁺ ε
  δ<η+ε = right<sum η {δ = δ} {η = ε} δ<ε


rationalLimitPrecisionBackward :
  (R : PrecisionBundle) →
  (f : ℚ⁺ → PrecisionBundle) →
  ((θ δ : ℚ⁺) → PrecisionRelation (f θ) (f δ) (θ +⁺ δ)) →
  (ε δ : ℚ⁺) →
  (δ<ε : δ <⁺ ε) →
  PrecisionRelation R (f δ) (ε ⊖ δ [ δ<ε ]) →
  (η : ℚ⁺) →
  precisionPredicate (rationalLimitPrecisionBundle f) η →
  precisionPredicate R (η +⁺ ε)
rationalLimitPrecisionBackward R f fCauchy ε δ δ<ε rel η =
  Prop.rec
    (PrecisionStructure.isPropP (R .snd) (η +⁺ ε))
    step
  where
  step :
    Σ[ θ ∈ ℚ⁺ ]
      Σ[ θ<η ∈ θ <⁺ η ]
      precisionPredicate (f θ) (η ⊖ θ [ θ<η ]) →
    precisionPredicate R (η +⁺ ε)
  step (θ , θ<η , fθη) =
    subst
      (precisionPredicate R)
      (limit-relation-shift η ε δ δ<ε)
      (snd (rel (δ +⁺ η)) fδδη)
    where
    fδδη : precisionPredicate (f δ) (δ +⁺ η)
    fδδη =
      subst
        (precisionPredicate (f δ))
        (limit-cauchy-shift η θ δ θ<η)
        (fst (fCauchy θ δ (η ⊖ θ [ θ<η ])) fθη)


rationalLimitPrecisionRelation :
  (R : PrecisionBundle) →
  (f : ℚ⁺ → PrecisionBundle) →
  ((θ δ : ℚ⁺) → PrecisionRelation (f θ) (f δ) (θ +⁺ δ)) →
  (ε δ : ℚ⁺) →
  (δ<ε : δ <⁺ ε) →
  PrecisionRelation R (f δ) (ε ⊖ δ [ δ<ε ]) →
  PrecisionRelation R (rationalLimitPrecisionBundle f) ε
rationalLimitPrecisionRelation R f fCauchy ε δ δ<ε rel η =
  rationalLimitPrecisionForward R f ε δ δ<ε rel η ,
  rationalLimitPrecisionBackward R f fCauchy ε δ δ<ε rel η


limitRationalPrecisionRelation :
  (f : ℚ⁺ → PrecisionBundle) →
  (R : PrecisionBundle) →
  ((θ δ : ℚ⁺) → PrecisionRelation (f θ) (f δ) (θ +⁺ δ)) →
  (ε δ : ℚ⁺) →
  (δ<ε : δ <⁺ ε) →
  PrecisionRelation (f δ) R (ε ⊖ δ [ δ<ε ]) →
  PrecisionRelation (rationalLimitPrecisionBundle f) R ε
limitRationalPrecisionRelation f R fCauchy ε δ δ<ε rel =
  precisionRelation-sym
    {P = R}
    {Q = rationalLimitPrecisionBundle f}
    {ε = ε}
    (rationalLimitPrecisionRelation R f fCauchy ε δ δ<ε
      (precisionRelation-sym
        {P = f δ}
        {Q = R}
        {ε = ε ⊖ δ [ δ<ε ]}
        rel))


limitLimitPrecisionForward :
  (f g : ℚ⁺ → PrecisionBundle) →
  ((θ δ : ℚ⁺) → PrecisionRelation (f θ) (f δ) (θ +⁺ δ)) →
  (ε δ η : ℚ⁺) →
  (δ+η<ε : δ +⁺ η <⁺ ε) →
  PrecisionRelation (f δ) (g η) (ε ⊖ (δ +⁺ η) [ δ+η<ε ]) →
  (θ : ℚ⁺) →
  precisionPredicate (rationalLimitPrecisionBundle f) θ →
  precisionPredicate (rationalLimitPrecisionBundle g) (θ +⁺ ε)
limitLimitPrecisionForward f g fCauchy ε δ η δ+η<ε rel θ =
  Prop.rec
    squash₁
    step
  where
  η<ε : η <⁺ ε
  η<ε = second-summand< {δ = δ} {η = η} {ε = ε} δ+η<ε

  η<θ+ε : η <⁺ θ +⁺ ε
  η<θ+ε = right<sum θ {δ = η} {η = ε} η<ε

  step :
    Σ[ α ∈ ℚ⁺ ]
      Σ[ α<θ ∈ α <⁺ θ ]
      precisionPredicate (f α) (θ ⊖ α [ α<θ ]) →
    precisionPredicate (rationalLimitPrecisionBundle g) (θ +⁺ ε)
  step (α , α<θ , fαθ) =
    ∣ η , η<θ+ε ,
        subst
          (precisionPredicate (g η))
          (limit-limit-relation-shift θ ε δ η δ+η<ε η<θ+ε)
          (fst (rel (δ +⁺ θ)) fδδθ)
    ∣₁
    where
    fδδθ : precisionPredicate (f δ) (δ +⁺ θ)
    fδδθ =
      subst
        (precisionPredicate (f δ))
        (limit-cauchy-shift θ α δ α<θ)
        (fst (fCauchy α δ (θ ⊖ α [ α<θ ])) fαθ)


limitLimitPrecisionRelation :
  (f g : ℚ⁺ → PrecisionBundle) →
  ((θ δ : ℚ⁺) → PrecisionRelation (f θ) (f δ) (θ +⁺ δ)) →
  ((θ δ : ℚ⁺) → PrecisionRelation (g θ) (g δ) (θ +⁺ δ)) →
  (ε δ η : ℚ⁺) →
  (δ+η<ε : δ +⁺ η <⁺ ε) →
  PrecisionRelation (f δ) (g η) (ε ⊖ (δ +⁺ η) [ δ+η<ε ]) →
  PrecisionRelation
    (rationalLimitPrecisionBundle f)
    (rationalLimitPrecisionBundle g)
    ε
limitLimitPrecisionRelation f g fCauchy gCauchy ε δ η δ+η<ε rel θ =
  limitLimitPrecisionForward f g fCauchy ε δ η δ+η<ε rel θ ,
  limitLimitPrecisionForward g f gCauchy ε η δ η+δ<ε rel' θ
  where
  η+δ<ε : η +⁺ δ <⁺ ε
  η+δ<ε = sum-comm-< ε δ η δ+η<ε

  rel' :
    PrecisionRelation
      (g η)
      (f δ)
      (ε ⊖ (η +⁺ δ) [ η+δ<ε ])
  rel' =
    subst
      (λ ρ → PrecisionRelation (g η) (f δ) ρ)
      (difference-sum-comm ε δ η δ+η<ε η+δ<ε)
      (precisionRelation-sym
        {P = f δ}
        {Q = g η}
        {ε = ε ⊖ (δ +⁺ η) [ δ+η<ε ]}
        rel)


limitSourceBundle :
  (f : ℚ⁺ → PredicateBundle) →
  PredicateBundle
limitSourceBundle f .fst u ε =
  ∥ Σ[ δ ∈ ℚ⁺ ]
      Σ[ δ<ε ∈ δ <⁺ ε ]
      bundlePredicate (f δ) u (ε ⊖ δ [ δ<ε ])
  ∥₁
limitSourceBundle f .snd .PredicateStructure.isPropP u ε =
  squash₁
limitSourceBundle f .snd .PredicateStructure.rounded u ε =
  openP , monotoneP
  where
  P : Predicate
  P = limitSourceBundle f .fst

  openP :
    P u ε →
    ∥ Σ[ ζ ∈ ℚ⁺ ] (ζ <⁺ ε) × P u ζ ∥₁
  openP =
    Prop.rec squash₁ λ (δ , δ<ε , fδ-close) →
      Prop.rec squash₁ (step δ δ<ε)
        (fst (PredicateStructure.rounded (f δ .snd) u _) fδ-close)
    where
    step :
      (δ : ℚ⁺) →
      (δ<ε : δ <⁺ ε) →
      Σ[ κ ∈ ℚ⁺ ]
        (κ <⁺ (ε ⊖ δ [ δ<ε ])) ×
        bundlePredicate (f δ) u κ →
      ∥ Σ[ ζ ∈ ℚ⁺ ] (ζ <⁺ ε) × P u ζ ∥₁
    step δ δ<ε (κ , κ<ε-δ , fδκ) =
      ∣ ζ , ζ<ε , ∣ δ , δ<ζ ,
          subst
            (bundlePredicate (f δ) u)
            (sym ζ-δ≡κ)
            fδκ
        ∣₁
      ∣₁
      where
      ζ : ℚ⁺
      ζ = δ +⁺ κ

      δ<ζ : δ <⁺ ζ
      δ<ζ = summand-left<sum δ κ

      ζ<ε : ζ <⁺ ε
      ζ<ε = sum<from-difference ε δ κ δ<ε κ<ε-δ

      ζ-δ≡κ : ζ ⊖ δ [ δ<ζ ] ≡ κ
      ζ-δ≡κ = sum-difference-left δ κ δ<ζ

  monotoneP :
    ∥ Σ[ ζ ∈ ℚ⁺ ] (ζ <⁺ ε) × P u ζ ∥₁ →
    P u ε
  monotoneP =
    Prop.rec squash₁ λ (ζ , ζ<ε , pζ) →
      Prop.rec squash₁ (step ζ ζ<ε) pζ
    where
    step :
      (ζ : ℚ⁺) →
      (ζ<ε : ζ <⁺ ε) →
      Σ[ δ ∈ ℚ⁺ ]
        Σ[ δ<ζ ∈ δ <⁺ ζ ]
        bundlePredicate (f δ) u (ζ ⊖ δ [ δ<ζ ]) →
      P u ε
    step ζ ζ<ε (δ , δ<ζ , fδ-close) =
      ∣ δ , δ<ε ,
          bundle-mono (f δ) u
            {ε = ζ ⊖ δ [ δ<ζ ]}
            {δ = ε ⊖ δ [ δ<ε ]}
            (difference-mono-left ζ ε δ δ<ζ δ<ε ζ<ε)
            fδ-close
      ∣₁
      where
      δ<ε : δ <⁺ ε
      δ<ε = <⁺-trans {ε = δ} {δ = ζ} {η = ε} δ<ζ ζ<ε
limitSourceBundle f .snd .PredicateStructure.mixedRight u v ε η u∼v =
  Prop.rec squash₁ step
  where
  step :
    Σ[ δ ∈ ℚ⁺ ]
      Σ[ δ<η ∈ δ <⁺ η ]
      bundlePredicate (f δ) u (η ⊖ δ [ δ<η ]) →
    bundlePredicate (limitSourceBundle f) v (η +⁺ ε)
  step (δ , δ<η , fδu) =
    ∣ δ , δ<η+ε ,
        subst
          (bundlePredicate (f δ) v)
          (sym (source-shift η ε δ δ<η δ<η+ε))
          (PredicateStructure.mixedRight (f δ .snd)
            u v ε (η ⊖ δ [ δ<η ]) u∼v fδu)
    ∣₁
    where
    δ<η+ε : δ <⁺ η +⁺ ε
    δ<η+ε = left<sum ε {α = δ} {ε = η} δ<η
limitSourceBundle f .snd .PredicateStructure.mixedLeft u v ε η u∼v =
  Prop.rec squash₁ step
  where
  step :
    Σ[ δ ∈ ℚ⁺ ]
      Σ[ δ<η ∈ δ <⁺ η ]
      bundlePredicate (f δ) v (η ⊖ δ [ δ<η ]) →
    bundlePredicate (limitSourceBundle f) u (η +⁺ ε)
  step (δ , δ<η , fδv) =
    ∣ δ , δ<η+ε ,
        subst
          (bundlePredicate (f δ) u)
          (sym (source-shift η ε δ δ<η δ<η+ε))
          (PredicateStructure.mixedLeft (f δ .snd)
            u v ε (η ⊖ δ [ δ<η ]) u∼v fδv)
    ∣₁
    where
    δ<η+ε : δ <⁺ η +⁺ ε
    δ<η+ε = left<sum ε {α = δ} {ε = η} δ<η


sourceLimitForward :
  (R : PredicateBundle) →
  (f : ℚ⁺ → PredicateBundle) →
  (ε δ : ℚ⁺) →
  (δ<ε : δ <⁺ ε) →
  Relation R (f δ) (ε ⊖ δ [ δ<ε ]) →
  (u : ℝᶜ) (η : ℚ⁺) →
  bundlePredicate R u η →
  bundlePredicate (limitSourceBundle f) u (η +⁺ ε)
sourceLimitForward R f ε δ δ<ε rel u η rη =
  ∣ δ , δ<η+ε ,
      subst
        (bundlePredicate (f δ) u)
        (sym (shift-difference-sum η ε δ δ<ε δ<η+ε))
        (fst (rel u η) rη)
  ∣₁
  where
  δ<η+ε : δ <⁺ η +⁺ ε
  δ<η+ε = right<sum η {δ = δ} {η = ε} δ<ε


sourceLimitBackward :
  (R : PredicateBundle) →
  (f : ℚ⁺ → PredicateBundle) →
  ((θ δ : ℚ⁺) → Relation (f θ) (f δ) (θ +⁺ δ)) →
  (ε δ : ℚ⁺) →
  (δ<ε : δ <⁺ ε) →
  Relation R (f δ) (ε ⊖ δ [ δ<ε ]) →
  (u : ℝᶜ) (η : ℚ⁺) →
  bundlePredicate (limitSourceBundle f) u η →
  bundlePredicate R u (η +⁺ ε)
sourceLimitBackward R f fCauchy ε δ δ<ε rel u η =
  Prop.rec
    (PredicateStructure.isPropP (R .snd) u (η +⁺ ε))
    step
  where
  step :
    Σ[ θ ∈ ℚ⁺ ]
      Σ[ θ<η ∈ θ <⁺ η ]
      bundlePredicate (f θ) u (η ⊖ θ [ θ<η ]) →
    bundlePredicate R u (η +⁺ ε)
  step (θ , θ<η , fθη) =
    subst
      (bundlePredicate R u)
      (limit-relation-shift η ε δ δ<ε)
      (snd (rel u (δ +⁺ η)) fδδη)
    where
    fδδη : bundlePredicate (f δ) u (δ +⁺ η)
    fδδη =
      subst
        (bundlePredicate (f δ) u)
        (limit-cauchy-shift η θ δ θ<η)
        (fst (fCauchy θ δ u (η ⊖ θ [ θ<η ])) fθη)


sourceLimitRelation :
  (R : PredicateBundle) →
  (f : ℚ⁺ → PredicateBundle) →
  ((θ δ : ℚ⁺) → Relation (f θ) (f δ) (θ +⁺ δ)) →
  (ε δ : ℚ⁺) →
  (δ<ε : δ <⁺ ε) →
  Relation R (f δ) (ε ⊖ δ [ δ<ε ]) →
  Relation R (limitSourceBundle f) ε
sourceLimitRelation R f fCauchy ε δ δ<ε rel u η =
  sourceLimitForward R f ε δ δ<ε rel u η ,
  sourceLimitBackward R f fCauchy ε δ δ<ε rel u η


limitSourceRelation :
  (f : ℚ⁺ → PredicateBundle) →
  (R : PredicateBundle) →
  ((θ δ : ℚ⁺) → Relation (f θ) (f δ) (θ +⁺ δ)) →
  (ε δ : ℚ⁺) →
  (δ<ε : δ <⁺ ε) →
  Relation (f δ) R (ε ⊖ δ [ δ<ε ]) →
  Relation (limitSourceBundle f) R ε
limitSourceRelation f R fCauchy ε δ δ<ε rel =
  relation-sym
    {P = R}
    {Q = limitSourceBundle f}
    {ε = ε}
    (sourceLimitRelation R f fCauchy ε δ δ<ε
      (relation-sym
        {P = f δ}
        {Q = R}
        {ε = ε ⊖ δ [ δ<ε ]}
        rel))


limitLimitSourceForward :
  (f g : ℚ⁺ → PredicateBundle) →
  ((θ δ : ℚ⁺) → Relation (f θ) (f δ) (θ +⁺ δ)) →
  (ε δ η : ℚ⁺) →
  (δ+η<ε : δ +⁺ η <⁺ ε) →
  Relation (f δ) (g η) (ε ⊖ (δ +⁺ η) [ δ+η<ε ]) →
  (u : ℝᶜ) (θ : ℚ⁺) →
  bundlePredicate (limitSourceBundle f) u θ →
  bundlePredicate (limitSourceBundle g) u (θ +⁺ ε)
limitLimitSourceForward f g fCauchy ε δ η δ+η<ε rel u θ =
  Prop.rec
    squash₁
    step
  where
  η<ε : η <⁺ ε
  η<ε = second-summand< {δ = δ} {η = η} {ε = ε} δ+η<ε

  η<θ+ε : η <⁺ θ +⁺ ε
  η<θ+ε = right<sum θ {δ = η} {η = ε} η<ε

  step :
    Σ[ α ∈ ℚ⁺ ]
      Σ[ α<θ ∈ α <⁺ θ ]
      bundlePredicate (f α) u (θ ⊖ α [ α<θ ]) →
    bundlePredicate (limitSourceBundle g) u (θ +⁺ ε)
  step (α , α<θ , fαθ) =
    ∣ η , η<θ+ε ,
        subst
          (bundlePredicate (g η) u)
          (limit-limit-relation-shift θ ε δ η δ+η<ε η<θ+ε)
          (fst (rel u (δ +⁺ θ)) fδδθ)
    ∣₁
    where
    fδδθ : bundlePredicate (f δ) u (δ +⁺ θ)
    fδδθ =
      subst
        (bundlePredicate (f δ) u)
        (limit-cauchy-shift θ α δ α<θ)
        (fst (fCauchy α δ u (θ ⊖ α [ α<θ ])) fαθ)


limitLimitSourceRelation :
  (f g : ℚ⁺ → PredicateBundle) →
  ((θ δ : ℚ⁺) → Relation (f θ) (f δ) (θ +⁺ δ)) →
  ((θ δ : ℚ⁺) → Relation (g θ) (g δ) (θ +⁺ δ)) →
  (ε δ η : ℚ⁺) →
  (δ+η<ε : δ +⁺ η <⁺ ε) →
  Relation (f δ) (g η) (ε ⊖ (δ +⁺ η) [ δ+η<ε ]) →
  Relation
    (limitSourceBundle f)
    (limitSourceBundle g)
    ε
limitLimitSourceRelation f g fCauchy gCauchy ε δ η δ+η<ε rel u θ =
  limitLimitSourceForward f g fCauchy ε δ η δ+η<ε rel u θ ,
  limitLimitSourceForward g f gCauchy ε η δ η+δ<ε rel' u θ
  where
  η+δ<ε : η +⁺ δ <⁺ ε
  η+δ<ε = sum-comm-< ε δ η δ+η<ε

  rel' :
    Relation
      (g η)
      (f δ)
      (ε ⊖ (η +⁺ δ) [ η+δ<ε ])
  rel' =
    subst
      (λ ρ → Relation (g η) (f δ) ρ)
      (difference-sum-comm ε δ η δ+η<ε η+δ<ε)
      (relation-sym
        {P = f δ}
        {Q = g η}
        {ε = ε ⊖ (δ +⁺ η) [ δ+η<ε ]}
        rel)


difference-from-sum< :
  (ε δ η : ℚ⁺) →
  (δ+η<ε : δ +⁺ η <⁺ ε) →
  η <⁺ ε ⊖ δ [ first-summand< {δ = δ} {η = η} {ε = ε} δ+η<ε ]
difference-from-sum< ε δ η δ+η<ε =
  subst
    (λ q → q ℚOrder.< radius (ε ⊖ δ [ δ<ε ]))
    (cong radius (sum-difference-left δ η (summand-left<sum δ η)))
    (ℚOrder.<-+o (radius (δ +⁺ η)) (radius ε) (ℚ.- radius δ) δ+η<ε)
  where
  δ<ε : δ <⁺ ε
  δ<ε = first-summand< {δ = δ} {η = η} {ε = ε} δ+η<ε


difference-difference-sum :
  (ε δ η : ℚ⁺) →
  (δ+η<ε : δ +⁺ η <⁺ ε) →
  (δ<ε : δ <⁺ ε) →
  (η<ε-δ : η <⁺ ε ⊖ δ [ δ<ε ]) →
  (ε ⊖ δ [ δ<ε ]) ⊖ η [ η<ε-δ ] ≡
  ε ⊖ (δ +⁺ η) [ δ+η<ε ]
difference-difference-sum ε δ η δ+η<ε δ<ε η<ε-δ =
  ℚ⁺Path
    (SolverHelpers.double-difference-sum ℚCommRing
      (radius ε) (radius δ) (radius η))


difference-difference-comm :
  (ε δ η : ℚ⁺) →
  (δ<ε : δ <⁺ ε) →
  (η<ε : η <⁺ ε) →
  (η<ε-δ : η <⁺ ε ⊖ δ [ δ<ε ]) →
  (δ<ε-η : δ <⁺ ε ⊖ η [ η<ε ]) →
  (ε ⊖ δ [ δ<ε ]) ⊖ η [ η<ε-δ ] ≡
  (ε ⊖ η [ η<ε ]) ⊖ δ [ δ<ε-η ]
difference-difference-comm ε δ η δ<ε η<ε η<ε-δ δ<ε-η =
  ℚ⁺Path
    (SolverHelpers.double-difference-comm ℚCommRing
      (radius ε) (radius δ) (radius η))
