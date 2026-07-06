{-# OPTIONS --safe #-}

module Constructive.CauchyReals.Order.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.CauchyCompletion.Closeness
import Constructive.Analysis.CauchyCompletion.Extension as GenericExtension
open import Constructive.Analysis.CauchyCompletion.Induction
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.CauchyReals.Arithmetic.Lattice
open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Extension
open import Constructive.CauchyReals.Order.Base
open import Constructive.CauchyReals.Order.Rational
open ClosenessOf RationalsMetricSpace
open ComputedOf RationalsMetricSpace
open RoundedOf RationalsMetricSpace
open GenericExtension.ExtensionOf RationalsMetricSpace
  using
    ( limit-close-intro
    ; limit-limit-intro
    )
open InductionOf RationalsMetricSpace
open import Constructive.Data.PositiveRationals
open import Constructive.Data.Rationals.Closeness
import Constructive.Data.Rationals as Rational


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    regular-bound-shift :
      (η θ δ : 𝓡 .fst) →
      (η + θ) + (δ - θ) ≡ η + δ
    regular-bound-shift _ _ _ = solve! 𝓡

  regular-bound-shift :
    (η θ δ : ℚ⁺) →
    (θ<δ : θ <⁺ δ) →
    (η +⁺ θ) +⁺ (δ ⊖ θ [ θ<δ ]) ≡ η +⁺ δ
  regular-bound-shift η θ δ θ<δ =
    ℚ⁺Path
      (SolverHelpers.regular-bound-shift ℚCommRing
        (radius η) (radius θ) (radius δ))

  small-double< :
    (η μ : ℚ⁺) →
    η <⁺ quarter⁺ μ →
    η +⁺ η <⁺ μ
  small-double< η μ η<quarter =
    ℚOrder.isTrans<
      (radius (η +⁺ η))
      (radius (quarter⁺ μ +⁺ quarter⁺ μ))
      (radius μ)
      (ℚOrder.<Monotone+
        (radius η)
        (radius (quarter⁺ μ))
        (radius η)
        (radius (quarter⁺ μ))
        η<quarter
        η<quarter)
      (quarter-sum< μ)

  rational-close-upper-bound :
    (p q : ℚ) (δ ε : ℚ⁺) →
    δ <⁺ ε →
    Closeℚ p δ q →
    rational p ≤ᶜ rational (q ℚ.+ radius ε)
  rational-close-upper-bound p q δ ε δ<ε p∼q =
    ≤ℚ→rational≤ᶜ
      {q = p}
      {r = q ℚ.+ radius ε}
      (ℚOrder.<Weaken≤ p (q ℚ.+ radius ε) p<q+ε)
    where
    p-q<ε : p ℚ.- q ℚOrder.< radius ε
    p-q<ε =
      ℚOrder.isTrans<
        (p ℚ.- q)
        (radius δ)
        (radius ε)
        (p∼q .fst)
        δ<ε

    p<q+ε : p ℚOrder.< q ℚ.+ radius ε
    p<q+ε =
      subst
        (p ℚOrder.<_)
        (ℚ.+Comm (radius ε) q)
        (Rational.diff<→right+< p (radius ε) q p-q<ε)

  rational-close-lower-bound :
    (p q : ℚ) (δ ε : ℚ⁺) →
    δ <⁺ ε →
    Closeℚ p δ q →
    rational (q ℚ.- radius ε) ≤ᶜ rational p
  rational-close-lower-bound p q δ ε δ<ε p∼q =
    ≤ℚ→rational≤ᶜ
      {q = q ℚ.- radius ε}
      {r = p}
      (ℚOrder.<Weaken≤ (q ℚ.- radius ε) p q-ε<p)
    where
    q-p<ε : q ℚ.- p ℚOrder.< radius ε
    q-p<ε =
      ℚOrder.isTrans<
        (q ℚ.- p)
        (radius δ)
        (radius ε)
        (p∼q .snd)
        δ<ε

    q<p+ε : q ℚOrder.< p ℚ.+ radius ε
    q<p+ε =
      subst
        (q ℚOrder.<_)
        (ℚ.+Comm (radius ε) p)
        (Rational.diff<→right+< q (radius ε) p q-p<ε)

    q-ε<p : q ℚ.- radius ε ℚOrder.< p
    q-ε<p =
      Rational.<+→diff< q p (radius ε) q<p+ε


close-rational-upper-bound :
  (x : ℝᶜ) (q : ℚ) (δ ε : ℚ⁺) →
  δ <⁺ ε →
  x ∼[ δ ] rational q →
  x ≤ᶜ rational (q ℚ.+ radius ε)
close-rational-upper-bound =
  PropInduction.ind kit
  where
  kit : PropInductionKit ℓ-zero
  kit .PropInductionKit.A x =
    (q : ℚ) (δ ε : ℚ⁺) →
    δ <⁺ ε →
    x ∼[ δ ] rational q →
    x ≤ᶜ rational (q ℚ.+ radius ε)
  kit .PropInductionKit.isPropA x =
    isPropΠ λ q →
    isPropΠ λ δ →
    isPropΠ λ ε →
    isPropΠ λ δ<ε →
    isPropΠ λ _ →
      isProp≤ᶜ x (rational (q ℚ.+ radius ε))
  kit .PropInductionKit.point* p q δ ε δ<ε p∼q =
    rational-close-upper-bound p q δ ε δ<ε (close→computed p∼q)
  kit .PropInductionKit.limit* x upperAt q δ ε δ<ε lim∼q =
    Prop.rec
      (isProp≤ᶜ (limit x) (rational a))
      step
      (close→computed lim∼q)
    where
    a : ℚ
    a = q ℚ.+ radius ε

    step :
      Σ[ θ ∈ ℚ⁺ ]
        Σ[ θ<δ ∈ θ <⁺ δ ]
        ComputedClose (δ ⊖ θ [ θ<δ ]) (approximate x θ) (rational q) →
      limit x ≤ᶜ rational a
    step (θ , θ<δ , xθ∼q*) =
      min-rational-right (limit x) a ∙
      path (limit (cauchy-approximation f fCauchy)) (limit x) closeAt
      where
      f : ℚ⁺ → ℝᶜ
      f η = approximate x η ⊓ᶜ rational a

      fCauchy : (η κ : ℚ⁺) → f η ∼[ η +⁺ κ ] f κ
      fCauchy η κ =
        min-close-left (isRegular x η κ) (rational a)

      xθ∼q :
        approximate x θ ∼[ δ ⊖ θ [ θ<δ ] ] rational q
      xθ∼q =
        computed→close
          (approximate x θ)
          (rational q)
          (δ ⊖ θ [ θ<δ ])
          xθ∼q*

      closeAt :
        (μ : ℚ⁺) →
        limit (cauchy-approximation f fCauchy) ∼[ μ ] limit x
      closeAt μ =
        limit-limit-intro
          (cauchy-approximation f fCauchy)
          x
          μ
          η
          η
          η+η<μ
          fη∼xη
        where
        gap : ℚ⁺
        gap = ε ⊖ δ [ δ<ε ]

        η : ℚ⁺
        η = half⁺ (min⁺ (quarter⁺ μ) gap)

        η<quarter : η <⁺ quarter⁺ μ
        η<quarter =
          half-min⁺<left (quarter⁺ μ) gap

        η<gap : η <⁺ gap
        η<gap =
          half-min⁺<right (quarter⁺ μ) gap

        η+δ<ε : η +⁺ δ <⁺ ε
        η+δ<ε =
          subst
            (λ ρ → ρ <⁺ ε)
            (+⁺-comm δ η)
            (sum<from-difference ε δ η δ<ε η<gap)

        η+η<μ : η +⁺ η <⁺ μ
        η+η<μ =
          small-double< η μ η<quarter

        xη∼q : approximate x η ∼[ η +⁺ δ ] rational q
        xη∼q =
          subst
            (λ ρ → approximate x η ∼[ ρ ] rational q)
            (regular-bound-shift η θ δ θ<δ)
            (close-triangle (isRegular x η θ) xθ∼q)

        xη≤a : approximate x η ≤ᶜ rational a
        xη≤a =
          upperAt η q (η +⁺ δ) ε η+δ<ε xη∼q

        fη∼xη :
          f η ∼[ μ ⊖ (η +⁺ η) [ η+η<μ ] ] approximate x η
        fη∼xη =
          subst
            (λ y → f η ∼[ μ ⊖ (η +⁺ η) [ η+η<μ ] ] y)
            xη≤a
            (close-refl (f η) (μ ⊖ (η +⁺ η) [ η+η<μ ]))


close-rational-lower-bound :
  (x : ℝᶜ) (q : ℚ) (δ ε : ℚ⁺) →
  δ <⁺ ε →
  x ∼[ δ ] rational q →
  rational (q ℚ.- radius ε) ≤ᶜ x
close-rational-lower-bound =
  PropInduction.ind kit
  where
  kit : PropInductionKit ℓ-zero
  kit .PropInductionKit.A x =
    (q : ℚ) (δ ε : ℚ⁺) →
    δ <⁺ ε →
    x ∼[ δ ] rational q →
    rational (q ℚ.- radius ε) ≤ᶜ x
  kit .PropInductionKit.isPropA x =
    isPropΠ λ q →
    isPropΠ λ δ →
    isPropΠ λ ε →
    isPropΠ λ δ<ε →
    isPropΠ λ _ →
      isProp≤ᶜ (rational (q ℚ.- radius ε)) x
  kit .PropInductionKit.point* p q δ ε δ<ε p∼q =
    rational-close-lower-bound p q δ ε δ<ε (close→computed p∼q)
  kit .PropInductionKit.limit* x lowerAt q δ ε δ<ε lim∼q =
    Prop.rec
      (isProp≤ᶜ (rational a) (limit x))
      step
      (close→computed lim∼q)
    where
    a : ℚ
    a = q ℚ.- radius ε

    step :
      Σ[ θ ∈ ℚ⁺ ]
        Σ[ θ<δ ∈ θ <⁺ δ ]
        ComputedClose (δ ⊖ θ [ θ<δ ]) (approximate x θ) (rational q) →
      rational a ≤ᶜ limit x
    step (θ , θ<δ , xθ∼q*) =
      min-rational-left a (limit x) ∙
      path (limit (cauchy-approximation f fCauchy)) (rational a) closeAt
      where
      f : ℚ⁺ → ℝᶜ
      f η = rational a ⊓ᶜ approximate x η

      fCauchy : (η κ : ℚ⁺) → f η ∼[ η +⁺ κ ] f κ
      fCauchy η κ =
        min-close-right (rational a) (isRegular x η κ)

      xθ∼q :
        approximate x θ ∼[ δ ⊖ θ [ θ<δ ] ] rational q
      xθ∼q =
        computed→close
          (approximate x θ)
          (rational q)
          (δ ⊖ θ [ θ<δ ])
          xθ∼q*

      closeAt :
        (μ : ℚ⁺) →
        limit (cauchy-approximation f fCauchy) ∼[ μ ] rational a
      closeAt μ =
        limit-close-intro
          (cauchy-approximation f fCauchy)
          (rational a)
          μ
          η
          η<μ
          fη∼a
        where
        gap : ℚ⁺
        gap = ε ⊖ δ [ δ<ε ]

        η : ℚ⁺
        η = half⁺ (min⁺ (quarter⁺ μ) gap)

        η<quarter : η <⁺ quarter⁺ μ
        η<quarter =
          half-min⁺<left (quarter⁺ μ) gap

        η<gap : η <⁺ gap
        η<gap =
          half-min⁺<right (quarter⁺ μ) gap

        η<μ : η <⁺ μ
        η<μ =
          <⁺-trans
            {ε = η}
            {δ = quarter⁺ μ}
            {η = μ}
            η<quarter
            (quarter< μ)

        η+δ<ε : η +⁺ δ <⁺ ε
        η+δ<ε =
          subst
            (λ ρ → ρ <⁺ ε)
            (+⁺-comm δ η)
            (sum<from-difference ε δ η δ<ε η<gap)

        xη∼q : approximate x η ∼[ η +⁺ δ ] rational q
        xη∼q =
          subst
            (λ ρ → approximate x η ∼[ ρ ] rational q)
            (regular-bound-shift η θ δ θ<δ)
            (close-triangle (isRegular x η θ) xθ∼q)

        a≤xη : rational a ≤ᶜ approximate x η
        a≤xη =
          lowerAt η q (η +⁺ δ) ε η+δ<ε xη∼q

        fη∼a :
          f η ∼[ μ ⊖ η [ η<μ ] ] rational a
        fη∼a =
          subst
            (λ y → f η ∼[ μ ⊖ η [ η<μ ] ] y)
            a≤xη
            (close-refl (f η) (μ ⊖ η [ η<μ ]))


limit-rational-lower-bound :
  (a : ℚ) (x : CauchyApproximation) →
  ((δ : ℚ⁺) → rational a ≤ᶜ approximate x δ) →
  rational a ≤ᶜ limit x
limit-rational-lower-bound a x lower =
  min-rational-left a (limit x) ∙
  path (limit (cauchy-approximation f fCauchy)) (rational a) closeAt
  where
  f : ℚ⁺ → ℝᶜ
  f δ = rational a ⊓ᶜ approximate x δ

  fCauchy : (δ η : ℚ⁺) → f δ ∼[ δ +⁺ η ] f η
  fCauchy δ η =
    min-close-right (rational a) (isRegular x δ η)

  closeAt :
    (ε : ℚ⁺) →
    limit (cauchy-approximation f fCauchy) ∼[ ε ] rational a
  closeAt ε =
    limit-close-intro
      (cauchy-approximation f fCauchy)
      (rational a)
      ε
      δ
      δ<ε
      fδ∼a
    where
    δ : ℚ⁺
    δ = quarter⁺ ε

    δ<ε : δ <⁺ ε
    δ<ε = quarter< ε

    fδ∼a : f δ ∼[ ε ⊖ δ [ δ<ε ] ] rational a
    fδ∼a =
      subst
        (λ y → f δ ∼[ ε ⊖ δ [ δ<ε ] ] y)
        (lower δ)
        (close-refl (f δ) (ε ⊖ δ [ δ<ε ]))


limit-rational-upper-bound :
  (a : ℚ) (x : CauchyApproximation) →
  ((δ : ℚ⁺) → approximate x δ ≤ᶜ rational a) →
  limit x ≤ᶜ rational a
limit-rational-upper-bound a x upper =
  min-rational-right (limit x) a ∙
  path (limit (cauchy-approximation f fCauchy)) (limit x) closeAt
  where
  f : ℚ⁺ → ℝᶜ
  f δ = approximate x δ ⊓ᶜ rational a

  fCauchy : (δ η : ℚ⁺) → f δ ∼[ δ +⁺ η ] f η
  fCauchy δ η =
    min-close-left (isRegular x δ η) (rational a)

  closeAt :
    (ε : ℚ⁺) →
    limit (cauchy-approximation f fCauchy) ∼[ ε ] limit x
  closeAt ε =
    limit-limit-intro
      (cauchy-approximation f fCauchy)
      x
      ε
      δ
      δ
      δ+δ<ε
      fδ∼xδ
    where
    δ : ℚ⁺
    δ = quarter⁺ ε

    δ+δ<ε : δ +⁺ δ <⁺ ε
    δ+δ<ε = quarter-sum< ε

    fδ∼xδ :
      f δ ∼[ ε ⊖ (δ +⁺ δ) [ δ+δ<ε ] ] approximate x δ
    fδ∼xδ =
      subst
        (λ y → f δ ∼[ ε ⊖ (δ +⁺ δ) [ δ+δ<ε ] ] y)
        (upper δ)
        (close-refl (f δ) (ε ⊖ (δ +⁺ δ) [ δ+δ<ε ]))
