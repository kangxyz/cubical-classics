{-# OPTIONS --safe #-}

module Constructive.CauchyReals.Order.Tightness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ; Σ-syntax; _,_)
open import Cubical.Data.Sum as Sum using (_⊎_; inl; inr)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; squash₁)
open import Cubical.Relation.Nullary
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.CauchyReals.Arithmetic.Addition
open import Constructive.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.CauchyReals.Arithmetic.Base
open import Constructive.CauchyReals.Arithmetic.Lattice
open import Constructive.CauchyReals.Arithmetic.Negation
open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Closeness.Properties
open import Constructive.CauchyReals.Order.Base
open import Constructive.CauchyReals.Order.Bounds
open import Constructive.CauchyReals.Order.Density
open import Constructive.CauchyReals.Order.StrictPositive
open import Constructive.CauchyReals.PositiveRationals
open import Constructive.CauchyReals.RationalCloseness
import Constructive.Rationals as Rational


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    shift-neg-left :
      (q η : 𝓡 .fst) →
      0r + (- q) ≡ - q
    shift-neg-left _ _ = solve! 𝓡

    shift-neg-right :
      (q η : 𝓡 .fst) →
      (q + η) + (- q) ≡ η
    shift-neg-right _ _ = solve! 𝓡

  neg≤from-neg≤ :
    (q η : ℚ) →
    ℚ.- η ℚOrder.≤ q →
    ℚ.- q ℚOrder.≤ η
  neg≤from-neg≤ q η -η≤q =
    subst2
      ℚOrder._≤_
      (SolverHelpers.shift-neg-left ℚCommRing q η)
      (SolverHelpers.shift-neg-right ℚCommRing q η)
      (ℚOrder.≤-+o 0ℚ (q ℚ.+ η) (ℚ.- q) 0≤q+η)
    where
    0≤q+η : 0ℚ ℚOrder.≤ q ℚ.+ η
    0≤q+η =
      subst
        (λ r → r ℚOrder.≤ q ℚ.+ η)
        (ℚ.+InvL η)
        (ℚOrder.≤-+o (ℚ.- η) q η -η≤q)

  rational-min-zero-close :
    (q : ℚ) (η : ℚ⁺) →
    ℚ.- radius η ℚOrder.≤ q →
    Closeℚ (ℚ.min 0ℚ q) (η +⁺ η) 0ℚ
  rational-min-zero-close q η -η≤q with q ℚOrder.≟ 0ℚ
  ... | ℚOrder.lt q<0 =
    subst
      (λ m → Closeℚ m (η +⁺ η) 0ℚ)
      (sym
        (ℚ.minComm 0ℚ q ∙
         ℚOrder.≤→min q 0ℚ (ℚOrder.<Weaken≤ q 0ℚ q<0)))
      q-close
    where
    q<η+η : q ℚOrder.< radius (η +⁺ η)
    q<η+η =
      Rational.<≤-trans
        {p = q}
        {q = 0ℚ}
        {r = radius (η +⁺ η)}
        q<0
        (ℚOrder.<Weaken≤ 0ℚ (radius (η +⁺ η))
          (positive-sum {p = radius η} {q = radius η} (η .snd) (η .snd)))

    -q<η+η : ℚ.- q ℚOrder.< radius (η +⁺ η)
    -q<η+η =
      Rational.≤<-trans
        {p = ℚ.- q}
        {q = radius η}
        {r = radius (η +⁺ η)}
        (neg≤from-neg≤ q (radius η) -η≤q)
        (summand-left<sum η η)

    q-close : Closeℚ q (η +⁺ η) 0ℚ
    q-close =
      subst
        (λ r → r ℚOrder.< radius (η +⁺ η))
        (sym (ℚ.+IdR q))
        q<η+η ,
      subst
        (λ r → r ℚOrder.< radius (η +⁺ η))
        (sym (SolverHelpers.shift-neg-left ℚCommRing q (radius η)))
        -q<η+η
  ... | ℚOrder.eq q≡0 =
    subst
      (λ m → Closeℚ m (η +⁺ η) 0ℚ)
      (sym (ℚOrder.≤→min 0ℚ q (ℚOrder.≡Weaken≤ 0ℚ q (sym q≡0))))
      (rational-close-refl 0ℚ (η +⁺ η))
  ... | ℚOrder.gt 0<q =
    subst
      (λ m → Closeℚ m (η +⁺ η) 0ℚ)
      (sym (ℚOrder.≤→min 0ℚ q (ℚOrder.<Weaken≤ 0ℚ q 0<q)))
      (rational-close-refl 0ℚ (η +⁺ η))

  quarter-half-plus-double< :
    (μ : ℚ⁺) →
    half⁺ (quarter⁺ μ) +⁺ (quarter⁺ μ +⁺ quarter⁺ μ) <⁺ μ
  quarter-half-plus-double< μ =
    ℚOrder.isTrans<
      (radius (δ +⁺ (η +⁺ η)))
      (radius (η +⁺ (η +⁺ η)))
      (radius μ)
      δ+ηη<η+ηη
      η+ηη<μ
    where
    η δ : ℚ⁺
    η = quarter⁺ μ
    δ = half⁺ η

    δ+ηη<η+ηη : radius (δ +⁺ (η +⁺ η)) ℚOrder.< radius (η +⁺ (η +⁺ η))
    δ+ηη<η+ηη =
      ℚOrder.<-+o
        (radius δ)
        (radius η)
        (radius (η +⁺ η))
        (half< η)

    η+ηη<μ : radius (η +⁺ (η +⁺ η)) ℚOrder.< radius μ
    η+ηη<μ =
      subst
        (λ ρ → radius ρ ℚOrder.< radius μ)
        (+⁺-assoc η η η)
        (three-quarter< μ)

  min-close-zero-from-lower-bound :
    (x : ℝᶜ) (q : ℚ) (δ η μ : ℚ⁺) →
    x ∼[ δ ] rational q →
    ℚ.- radius η ℚOrder.≤ q →
    δ +⁺ (η +⁺ η) <⁺ μ →
    (0ᶜ ⊓ᶜ x) ∼[ μ ] 0ᶜ
  min-close-zero-from-lower-bound x q δ η μ x∼q -η≤q precision<μ =
    close-mono
      {ε = δ +⁺ (η +⁺ η)}
      {δ = μ}
      precision<μ
      (close-triangle
        (min-close-right 0ᶜ x∼q)
        (rational-rational-close
          (ℚ.min 0ℚ q)
          0ℚ
          (η +⁺ η)
          (rational-min-zero-close q η -η≤q)))

  negative-or-lower-bound :
    (q : ℚ) (η : ℚ⁺) →
    (q ℚOrder.< ℚ.- radius η) ⊎ (ℚ.- radius η ℚOrder.≤ q)
  negative-or-lower-bound q η with q ℚOrder.≟ (ℚ.- radius η)
  ... | ℚOrder.lt q<-η =
    inl q<-η
  ... | ℚOrder.eq q≡-η =
    inr (ℚOrder.≡Weaken≤ (ℚ.- radius η) q (sym q≡-η))
  ... | ℚOrder.gt -η<q =
    inr (ℚOrder.<Weaken≤ (ℚ.- radius η) q -η<q)

close-negative→positive-negᶜ :
  (x : ℝᶜ) (q : ℚ) (δ ε : ℚ⁺) →
  δ <⁺ ε →
  q ℚOrder.< ℚ.- radius ε →
  x ∼[ δ ] rational q →
  PositiveSepᶜ (-ᶜ x)
close-negative→positive-negᶜ x q δ ε δ<ε q<-ε x∼q =
  negative-upper-bound→positive-negᶜ x ζ x≤-ζ
  where
  q+ε<0 : q ℚ.+ radius ε ℚOrder.< 0ℚ
  q+ε<0 =
    subst
      (λ r → q ℚ.+ radius ε ℚOrder.< r)
      (ℚ.+InvL (radius ε))
      (ℚOrder.<-+o q (ℚ.- radius ε) (radius ε) q<-ε)

  ζ : ℚ⁺
  ζ =
    ℚ.- (q ℚ.+ radius ε) ,
    Rational.neg-positive {q = q ℚ.+ radius ε} q+ε<0

  x≤q+ε : x ≤ᶜ rational (q ℚ.+ radius ε)
  x≤q+ε =
    close-rational-upper-bound x q δ ε δ<ε x∼q

  q+ε≡-ζ : q ℚ.+ radius ε ≡ ℚ.- radius ζ
  q+ε≡-ζ =
    sym (ℚ.-Invol (q ℚ.+ radius ε))

  x≤-ζ : x ≤ᶜ rational (ℚ.- radius ζ)
  x≤-ζ =
    subst
      (x ≤ᶜ_)
      (cong rational q+ε≡-ζ)
      x≤q+ε


rational-min-zero-closeᶜ :
  (q : ℚ) (η : ℚ⁺) →
  ℚ.- radius η ℚOrder.≤ q →
  (rational (ℚ.min 0ℚ q)) ∼[ η +⁺ η ] 0ᶜ
rational-min-zero-closeᶜ q η -η≤q =
  rational-rational-close
    (ℚ.min 0ℚ q)
    0ℚ
    (η +⁺ η)
    (rational-min-zero-close q η -η≤q)


min-close-zero-from-lower-boundᶜ :
  (x : ℝᶜ) (q : ℚ) (δ η μ : ℚ⁺) →
  x ∼[ δ ] rational q →
  ℚ.- radius η ℚOrder.≤ q →
  δ +⁺ (η +⁺ η) <⁺ μ →
  (0ᶜ ⊓ᶜ x) ∼[ μ ] 0ᶜ
min-close-zero-from-lower-boundᶜ =
  min-close-zero-from-lower-bound


nonnegative-approx-stepᶜ :
  (x : ℝᶜ) (μ η δ : ℚ⁺) →
  δ <⁺ η →
  δ +⁺ (η +⁺ η) <⁺ μ →
  ¬ PositiveSepᶜ (-ᶜ x) →
  Σ[ q ∈ ℚ ] x ∼[ δ ] rational q →
  (0ᶜ ⊓ᶜ x) ∼[ μ ] 0ᶜ
nonnegative-approx-stepᶜ x μ η δ δ<η precision<μ ¬pos-neg (q , x∼q) =
  Sum.rec negativeCase lowerBoundCase (negative-or-lower-bound q η)
  where
  negativeCase :
    q ℚOrder.< ℚ.- radius η →
    (0ᶜ ⊓ᶜ x) ∼[ μ ] 0ᶜ
  negativeCase q<-η =
    Empty.rec
      (¬pos-neg (close-negative→positive-negᶜ x q δ η δ<η q<-η x∼q))

  lowerBoundCase :
    ℚ.- radius η ℚOrder.≤ q →
    (0ᶜ ⊓ᶜ x) ∼[ μ ] 0ᶜ
  lowerBoundCase -η≤q =
    min-close-zero-from-lower-boundᶜ x q δ η μ
      x∼q
      -η≤q
      precision<μ


nonnegative-from-not-positive-negᶜ :
  (x : ℝᶜ) →
  ¬ PositiveSepᶜ (-ᶜ x) →
  0ᶜ ≤ᶜ x
nonnegative-from-not-positive-negᶜ x ¬pos-neg =
  path (0ᶜ ⊓ᶜ x) 0ᶜ closeAt
  where
  closeAt : (μ : ℚ⁺) → (0ᶜ ⊓ᶜ x) ∼[ μ ] 0ᶜ
  closeAt μ =
    Prop.rec
      squash
      (nonnegative-approx-stepᶜ x μ η δ δ<η precision<μ ¬pos-neg)
      (rational-approximation x δ)
    where
    η δ : ℚ⁺
    η = quarter⁺ μ
    δ = half⁺ η

    δ<η : δ <⁺ η
    δ<η =
      half< η

    precision<μ : δ +⁺ (η +⁺ η) <⁺ μ
    precision<μ =
      quarter-half-plus-double< μ


opposite-diffᶜ :
  (x y : ℝᶜ) →
  -ᶜ (y +ᶜ (-ᶜ x)) ≡ x +ᶜ (-ᶜ y)
opposite-diffᶜ x y =
  neg-add y (-ᶜ x) ∙
  cong ((-ᶜ y) +ᶜ_) (neg-involutive x) ∙
  add-comm (-ᶜ y) x


¬>ᶜ→≤ᶜ :
  (x y : ℝᶜ) →
  ¬ (y <ᶜ x) →
  x ≤ᶜ y
¬>ᶜ→≤ᶜ x y ¬y<x =
  diffᶜ-nonnegative→≤ᶜ {x = x} {y = y}
    (nonnegative-from-not-positive-negᶜ d ¬pos-neg-d)
  where
  d : ℝᶜ
  d = y +ᶜ (-ᶜ x)

  ¬pos-neg-d : ¬ PositiveSepᶜ (-ᶜ d)
  ¬pos-neg-d pos-neg-d =
    ¬y<x (subst PositiveSepᶜ (opposite-diffᶜ x y) pos-neg-d)


≤ᶜ≃¬>ᶜ :
  (x y : ℝᶜ) →
  (x ≤ᶜ y) ≃ (¬ (y <ᶜ x))
≤ᶜ≃¬>ᶜ x y =
  propBiimpl→Equiv
    (isProp≤ᶜ x y)
    (isProp¬ (y <ᶜ x))
    (≤ᶜ→¬>ᶜ x y)
    (¬>ᶜ→≤ᶜ x y)
