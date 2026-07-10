{-

Cauchy-real boundedness and rational bounds

-}
{-# OPTIONS --safe #-}

module Constructive.Analysis.Reals.CauchyReals.Order.Bounded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ; Σ-syntax; _,_; _×_)
open import Cubical.Data.Sum as Sum using (inl; inr)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarOrder
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Instances.Rationals
open ClosenessOf RationalsMetricSpace
open ComputedOf RationalsMetricSpace
open RoundedOf RationalsMetricSpace
open import Constructive.Analysis.Reals.CauchyReals.Extension
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Order.Density
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive using (≤ᶜ-add)
open import Constructive.Data.PositiveRationals
open import Constructive.Data.Rationals.Closeness
import Constructive.Data.Rationals as Rational


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    diff-plus-cancel :
      (q φ : 𝓡 .fst) →
      (q + (- φ)) + φ ≡ q
    diff-plus-cancel _ _ = solve! 𝓡

    diff-zero-right :
      (q : 𝓡 .fst) →
      q + (- 0r) ≡ q
    diff-zero-right _ = solve! 𝓡

    zero-diff :
      (q : 𝓡 .fst) →
      0r + (- q) ≡ - q
    zero-diff _ = solve! 𝓡

    neg-diff :
      (q r : 𝓡 .fst) →
      - (q + (- r)) ≡ r + (- q)
    neg-diff _ _ = solve! 𝓡

    bounded-close-precision :
      (θ δ η : 𝓡 .fst) →
      θ + (δ + η) ≡ δ + (θ + η)
    bounded-close-precision _ _ _ = solve! 𝓡

  diff≤→≤+ :
    (q δ φ : ℚ) →
    q ℚ.- φ ℚOrder.≤ δ →
    q ℚOrder.≤ δ ℚ.+ φ
  diff≤→≤+ q δ φ q-φ≤δ =
    subst
      (λ s → s ℚOrder.≤ δ ℚ.+ φ)
      (SolverHelpers.diff-plus-cancel ℚCommRing q φ)
      (ℚOrder.≤-+o (q ℚ.- φ) δ φ q-φ≤δ)

  diff-zero-right :
    (q : ℚ) →
    q ℚ.- 0ℚ ≡ q
  diff-zero-right =
    SolverHelpers.diff-zero-right ℚCommRing

  zero-diff :
    (q : ℚ) →
    0ℚ ℚ.- q ≡ ℚ.- q
  zero-diff =
    SolverHelpers.zero-diff ℚCommRing

  neg-diff :
    (q r : ℚ) →
    ℚ.- (q ℚ.- r) ≡ r ℚ.- q
  neg-diff =
    SolverHelpers.neg-diff ℚCommRing

  product-bound< :
    (δ ε κ : ℚ⁺) →
    δ <⁺ ε →
    δ *⁺ κ <⁺ κ *⁺ ε
  product-bound< δ ε κ δ<ε =
    subst
      (λ ρ → ρ ℚOrder.< radius (κ *⁺ ε))
      (sym (ℚ.·Comm (radius δ) (radius κ)))
      (Rational.mul-left-positive-<
        {a = radius κ}
        {b = radius δ}
        {c = radius ε}
        (κ .snd)
        δ<ε)

  diff-close-zero→close :
    {x y : ℝᶜ} {ε : ℚ⁺} →
    (x +ᶜ (-ᶜ y)) ∼[ ε ] 0ᶜ →
    x ∼[ ε ] y
  diff-close-zero→close {x = x} {y = y} {ε = ε} diff∼0 =
    subst2
      (λ u v → u ∼[ ε ] v)
      (minus-plus-cancel-right x y)
      (add-zero-left y)
      (add-close-left diff∼0 y)


RationalBoundᶜ : ℚ⁺ → ℚ → Type₀
RationalBoundᶜ κ q =
  (q ℚOrder.< radius κ) × (ℚ.- q ℚOrder.< radius κ)


rational-boundᶜ :
  {κ : ℚ⁺} {q : ℚ} →
  q ℚOrder.< radius κ →
  ℚ.- q ℚOrder.< radius κ →
  RationalBoundᶜ κ q
rational-boundᶜ upper lower =
  upper , lower


module RationalBoundᶜ {κ : ℚ⁺} {q : ℚ} (bound : RationalBoundᶜ κ q) where
  upperℚ : q ℚOrder.< radius κ
  upperℚ =
    bound .fst

  lowerℚ : ℚ.- q ℚOrder.< radius κ
  lowerℚ =
    bound .snd


open RationalBoundᶜ public


RationalClosedBoundᶜ : ℚ⁺ → ℚ → Type₀
RationalClosedBoundᶜ κ q =
  (q ℚOrder.≤ radius κ) × (ℚ.- q ℚOrder.≤ radius κ)


rational-closed-boundᶜ :
  {κ : ℚ⁺} {q : ℚ} →
  q ℚOrder.≤ radius κ →
  ℚ.- q ℚOrder.≤ radius κ →
  RationalClosedBoundᶜ κ q
rational-closed-boundᶜ upper lower =
  upper , lower


module RationalClosedBoundᶜ
    {κ : ℚ⁺} {q : ℚ}
    (bound : RationalClosedBoundᶜ κ q) where
  upper≤ℚ : q ℚOrder.≤ radius κ
  upper≤ℚ =
    bound .fst

  lower≤ℚ : ℚ.- q ℚOrder.≤ radius κ
  lower≤ℚ =
    bound .snd


open RationalClosedBoundᶜ public


isPropRationalBoundᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  isProp (RationalBoundᶜ κ q)
isPropRationalBoundᶜ κ q =
  isProp×
    (ℚOrder.isProp< q (radius κ))
    (ℚOrder.isProp< (ℚ.- q) (radius κ))


isPropRationalClosedBoundᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  isProp (RationalClosedBoundᶜ κ q)
isPropRationalClosedBoundᶜ κ q =
  isProp×
    (ℚOrder.isProp≤ q (radius κ))
    (ℚOrder.isProp≤ (ℚ.- q) (radius κ))


BoundedByᶜ : ℚ⁺ → ℝᶜ → Type₀
BoundedByᶜ κ x =
  (x ≤ᶜ rational (radius κ)) × ((-ᶜ x) ≤ᶜ rational (radius κ))


bounded-byᶜ :
  {κ : ℚ⁺} {x : ℝᶜ} →
  x ≤ᶜ rational (radius κ) →
  (-ᶜ x) ≤ᶜ rational (radius κ) →
  BoundedByᶜ κ x
bounded-byᶜ upper lower =
  upper , lower


module BoundedByᶜ {κ : ℚ⁺} {x : ℝᶜ} (bound : BoundedByᶜ κ x) where
  upperᶜ : x ≤ᶜ rational (radius κ)
  upperᶜ =
    bound .fst

  lowerᶜ : (-ᶜ x) ≤ᶜ rational (radius κ)
  lowerᶜ =
    bound .snd


open BoundedByᶜ public


isPropBoundedByᶜ :
  (κ : ℚ⁺) (x : ℝᶜ) →
  isProp (BoundedByᶜ κ x)
isPropBoundedByᶜ κ x =
  isProp×
    (isProp≤ᶜ x (rational (radius κ)))
    (isProp≤ᶜ (-ᶜ x) (rational (radius κ)))


scalar-bound-rational-boundᶜ :
  (q : ℚ) →
  RationalBoundᶜ (scalar-bound q) q
scalar-bound-rational-boundᶜ q =
  rational-boundᶜ {κ = scalar-bound q} {q = q}
    (scalar-bound-upper q)
    (scalar-bound-lower q)


rational-diff-boundᶜ :
  (q r : ℚ) (ε : ℚ⁺) →
  Closeℚ q ε r →
  RationalBoundᶜ ε (q ℚ.- r)
rational-diff-boundᶜ q r ε q∼r =
  rational-boundᶜ {κ = ε} {q = q ℚ.- r}
    (q∼r .fst)
    (subst
      (λ s → s ℚOrder.< radius ε)
      (sym (neg-diff q r))
      (q∼r .snd))


rational-bound→closedᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  RationalBoundᶜ κ q →
  RationalClosedBoundᶜ κ q
rational-bound→closedᶜ κ q bound =
  rational-closed-boundᶜ {κ = κ} {q = q}
    (ℚOrder.<Weaken≤ q (radius κ) (upperℚ {κ = κ} {q = q} bound))
    (ℚOrder.<Weaken≤ (ℚ.- q) (radius κ) (lowerℚ {κ = κ} {q = q} bound))


rational-boundᶜ-monotone :
  {κ μ : ℚ⁺} {q : ℚ} →
  radius κ ℚOrder.≤ radius μ →
  RationalBoundᶜ κ q →
  RationalBoundᶜ μ q
rational-boundᶜ-monotone {κ = κ} {μ = μ} {q = q} κ≤μ bound =
  rational-boundᶜ {κ = μ} {q = q}
    (Rational.<≤-trans
      {p = q}
      {q = radius κ}
      {r = radius μ}
      (upperℚ {κ = κ} {q = q} bound)
      κ≤μ)
    (Rational.<≤-trans
      {p = ℚ.- q}
      {q = radius κ}
      {r = radius μ}
      (lowerℚ {κ = κ} {q = q} bound)
      κ≤μ)


rational-closed-boundᶜ-monotone :
  {κ μ : ℚ⁺} {q : ℚ} →
  radius κ ℚOrder.≤ radius μ →
  RationalClosedBoundᶜ κ q →
  RationalClosedBoundᶜ μ q
rational-closed-boundᶜ-monotone {κ = κ} {μ = μ} {q = q} κ≤μ bound =
  rational-closed-boundᶜ {κ = μ} {q = q}
    (Rational.≤-trans
      {p = q}
      {q = radius κ}
      {r = radius μ}
      (upper≤ℚ {κ = κ} {q = q} bound)
      κ≤μ)
    (Rational.≤-trans
      {p = ℚ.- q}
      {q = radius κ}
      {r = radius μ}
      (lower≤ℚ {κ = κ} {q = q} bound)
      κ≤μ)


rational-boundᶜ-neg :
  (κ : ℚ⁺) (q : ℚ) →
  RationalBoundᶜ κ q →
  RationalBoundᶜ κ (ℚ.- q)
rational-boundᶜ-neg κ q bound =
  rational-boundᶜ {κ = κ} {q = ℚ.- q}
    (lowerℚ {κ = κ} {q = q} bound)
    (subst
      (λ r → r ℚOrder.< radius κ)
      (sym (ℚ.-Invol q))
      (upperℚ {κ = κ} {q = q} bound))


rational-closed-boundᶜ-neg :
  (κ : ℚ⁺) (q : ℚ) →
  RationalClosedBoundᶜ κ q →
  RationalClosedBoundᶜ κ (ℚ.- q)
rational-closed-boundᶜ-neg κ q bound =
  rational-closed-boundᶜ {κ = κ} {q = ℚ.- q}
    (lower≤ℚ {κ = κ} {q = q} bound)
    (subst
      (λ r → r ℚOrder.≤ radius κ)
      (sym (ℚ.-Invol q))
      (upper≤ℚ {κ = κ} {q = q} bound))


rational-bound→boundedᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  RationalBoundᶜ κ q →
  BoundedByᶜ κ (rational q)
rational-bound→boundedᶜ κ q bound =
  bounded-byᶜ {κ = κ} {x = rational q}
    (≤ℚ→rational≤ᶜ
      (ℚOrder.<Weaken≤ q (radius κ) (upperℚ {κ = κ} {q = q} bound)))
    (≤ℚ→rational≤ᶜ
      (ℚOrder.<Weaken≤ (ℚ.- q) (radius κ) (lowerℚ {κ = κ} {q = q} bound)))


rational-closed-bound→boundedᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  RationalClosedBoundᶜ κ q →
  BoundedByᶜ κ (rational q)
rational-closed-bound→boundedᶜ κ q bound =
  bounded-byᶜ {κ = κ} {x = rational q}
    (≤ℚ→rational≤ᶜ (upper≤ℚ {κ = κ} {q = q} bound))
    (≤ℚ→rational≤ᶜ (lower≤ℚ {κ = κ} {q = q} bound))


bounded-rational→closed-boundᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  BoundedByᶜ κ (rational q) →
  RationalClosedBoundᶜ κ q
bounded-rational→closed-boundᶜ κ q bound =
  rational-closed-boundᶜ {κ = κ} {q = q}
    (rational≤ᶜ→≤ℚ (upperᶜ {κ = κ} {x = rational q} bound))
    (rational≤ᶜ→≤ℚ (lowerᶜ {κ = κ} {x = rational q} bound))


bounded-byᶜ-monotone :
  {κ μ : ℚ⁺} {x : ℝᶜ} →
  radius κ ℚOrder.≤ radius μ →
  BoundedByᶜ κ x →
  BoundedByᶜ μ x
bounded-byᶜ-monotone {κ = κ} {μ = μ} {x = x} κ≤μ bound =
  bounded-byᶜ {κ = μ} {x = x}
    (≤ᶜ-trans
      {x = x}
      {y = rational (radius κ)}
      {z = rational (radius μ)}
      (upperᶜ {κ = κ} {x = x} bound)
      κ≤μᶜ)
    (≤ᶜ-trans
      {x = -ᶜ x}
      {y = rational (radius κ)}
      {z = rational (radius μ)}
      (lowerᶜ {κ = κ} {x = x} bound)
      κ≤μᶜ)
  where
  κ≤μᶜ : rational (radius κ) ≤ᶜ rational (radius μ)
  κ≤μᶜ =
    ≤ℚ→rational≤ᶜ κ≤μ


bounded-byᶜ-neg :
  (κ : ℚ⁺) (x : ℝᶜ) →
  BoundedByᶜ κ x →
  BoundedByᶜ κ (-ᶜ x)
bounded-byᶜ-neg κ x bound =
  bounded-byᶜ {κ = κ} {x = -ᶜ x}
    (lowerᶜ {κ = κ} {x = x} bound)
    (subst
      (λ w → w ≤ᶜ rational (radius κ))
      (sym (neg-involutive x))
      (upperᶜ {κ = κ} {x = x} bound))


bounded-byᶜ-add :
  (κ μ : ℚ⁺) (x y : ℝᶜ) →
  BoundedByᶜ κ x →
  BoundedByᶜ μ y →
  BoundedByᶜ (κ +⁺ μ) (x +ᶜ y)
bounded-byᶜ-add κ μ x y x-bound y-bound =
  bounded-byᶜ {κ = κ +⁺ μ} {x = x +ᶜ y}
    (subst
      ((x +ᶜ y) ≤ᶜ_)
      (add-rational (radius κ) (radius μ))
      (≤ᶜ-add
        {a = x}
        {b = rational (radius κ)}
        {c = y}
        {d = rational (radius μ)}
        (upperᶜ {κ = κ} {x = x} x-bound)
        (upperᶜ {κ = μ} {x = y} y-bound)))
    (subst2
      _≤ᶜ_
      (sym (neg-add x y))
      (add-rational (radius κ) (radius μ))
      (≤ᶜ-add
        {a = -ᶜ x}
        {b = rational (radius κ)}
        {c = -ᶜ y}
        {d = rational (radius μ)}
        (lowerᶜ {κ = κ} {x = x} x-bound)
        (lowerᶜ {κ = μ} {x = y} y-bound)))


bounded-byᶜ-sub :
  (κ μ : ℚ⁺) (x y : ℝᶜ) →
  BoundedByᶜ κ x →
  BoundedByᶜ μ y →
  BoundedByᶜ (κ +⁺ μ) (x +ᶜ (-ᶜ y))
bounded-byᶜ-sub κ μ x y x-bound y-bound =
  bounded-byᶜ-add
    κ
    μ
    x
    (-ᶜ y)
    x-bound
    (bounded-byᶜ-neg μ y y-bound)


bounded-byᶜ-scale-nonnegative :
  (a : ℚ) (κ μ : ℚ⁺) (x : ℝᶜ) →
  0ℚ ℚOrder.≤ a →
  a ℚOrder.≤ radius μ →
  BoundedByᶜ κ x →
  BoundedByᶜ (μ *⁺ κ) (scalarMulᶜ a x)
bounded-byᶜ-scale-nonnegative a κ μ x 0≤a a≤μ x-bound =
  bounded-byᶜ {κ = μ *⁺ κ} {x = scalarMulᶜ a x}
    (≤ᶜ-trans
      {x = scalarMulᶜ a x}
      {y = scalarMulᶜ a (rational (radius κ))}
      {z = rational (radius (μ *⁺ κ))}
      (scalarMulᶜ-pres≤ᶜ-nonnegative
        a
        0≤a
        {x = x}
        {y = rational (radius κ)}
        (upperᶜ {κ = κ} {x = x} x-bound))
      upper-scale≤)
    (subst
      (λ w → w ≤ᶜ rational (radius (μ *⁺ κ)))
      (scalarMulᶜ-neg-real a x)
      (≤ᶜ-trans
        {x = scalarMulᶜ a (-ᶜ x)}
        {y = scalarMulᶜ a (rational (radius κ))}
        {z = rational (radius (μ *⁺ κ))}
        (scalarMulᶜ-pres≤ᶜ-nonnegative
          a
          0≤a
          {x = -ᶜ x}
          {y = rational (radius κ)}
          (lowerᶜ {κ = κ} {x = x} x-bound))
        upper-scale≤))
  where
  aκ≤μκ : a ℚ.· radius κ ℚOrder.≤ radius μ ℚ.· radius κ
  aκ≤μκ =
    ℚOrder.≤-·o
      a
      (radius μ)
      (radius κ)
      (Rational.<→≤ {p = 0ℚ} {q = radius κ} (κ .snd))
      a≤μ

  upper-scale≤ :
    scalarMulᶜ a (rational (radius κ)) ≤ᶜ
    rational (radius (μ *⁺ κ))
  upper-scale≤ =
    subst
      (λ w → w ≤ᶜ rational (radius (μ *⁺ κ)))
      (sym (scalarMulᶜ-rational a (radius κ)))
      (≤ℚ→rational≤ᶜ aκ≤μκ)


bounded-byᶜ-scale-rational-bound :
  (a : ℚ) (κ μ : ℚ⁺) (x : ℝᶜ) →
  RationalBoundᶜ μ a →
  BoundedByᶜ κ x →
  BoundedByᶜ (μ *⁺ κ) (scalarMulᶜ a x)
bounded-byᶜ-scale-rational-bound a κ μ x a-bound x-bound =
  Sum.rec negativeCase nonnegativeCase (Rational.negative-or-nonnegative a)
  where
  scalar-a≡neg-scale--a :
    scalarMulᶜ a x ≡ -ᶜ (scalarMulᶜ (ℚ.- a) x)
  scalar-a≡neg-scale--a =
    sym (cong (λ s → scalarMulᶜ s x) (ℚ.-Invol a)) ∙
    scalarMulᶜ-neg-scalar (ℚ.- a) x

  nonnegativeCase :
    0ℚ ℚOrder.≤ a →
    BoundedByᶜ (μ *⁺ κ) (scalarMulᶜ a x)
  nonnegativeCase 0≤a =
    bounded-byᶜ-scale-nonnegative
      a
      κ
      μ
      x
      0≤a
      (Rational.<→≤ {p = a} {q = radius μ} (upperℚ {κ = μ} {q = a} a-bound))
      x-bound

  negativeCase :
    a ℚOrder.< 0ℚ →
    BoundedByᶜ (μ *⁺ κ) (scalarMulᶜ a x)
  negativeCase a<0 =
    subst
      (BoundedByᶜ (μ *⁺ κ))
      (sym scalar-a≡neg-scale--a)
      (bounded-byᶜ-neg
        (μ *⁺ κ)
        (scalarMulᶜ (ℚ.- a) x)
        (bounded-byᶜ-scale-nonnegative
          (ℚ.- a)
          κ
          μ
          x
          (Rational.<→≤ {p = 0ℚ} {q = ℚ.- a}
            (Rational.neg-positive {q = a} a<0))
          (Rational.<→≤ {p = ℚ.- a} {q = radius μ} (lowerℚ {κ = μ} {q = a} a-bound))
          x-bound))


bounded-approximation-rational-boundᶜ :
  (κ φ η θ : ℚ⁺) (x : ℝᶜ) (q : ℚ) →
  θ <⁺ φ →
  φ <⁺ η →
  BoundedByᶜ κ x →
  x ∼[ θ ] rational q →
  RationalBoundᶜ (κ +⁺ η) q
bounded-approximation-rational-boundᶜ κ φ η θ x q θ<φ φ<η bound x∼q =
  rational-boundᶜ {κ = κ +⁺ η} {q = q} q<κ+η -q<κ+η
  where
  κ+φ<κ+η : radius (κ +⁺ φ) ℚOrder.< radius (κ +⁺ η)
  κ+φ<κ+η =
    ℚOrder.<-o+ (radius φ) (radius η) (radius κ) φ<η

  q-φ≤x : rational (q ℚ.- radius φ) ≤ᶜ x
  q-φ≤x =
    close-rational-lower-bound x q θ φ θ<φ x∼q

  q-φ≤κᶜ : rational (q ℚ.- radius φ) ≤ᶜ rational (radius κ)
  q-φ≤κᶜ =
    ≤ᶜ-trans
      {x = rational (q ℚ.- radius φ)}
      {y = x}
      {z = rational (radius κ)}
      q-φ≤x
      (upperᶜ {κ = κ} {x = x} bound)

  q≤κ+φ : q ℚOrder.≤ radius (κ +⁺ φ)
  q≤κ+φ =
    diff≤→≤+
      q
      (radius κ)
      (radius φ)
      (rational≤ᶜ→≤ℚ q-φ≤κᶜ)

  q<κ+η : q ℚOrder.< radius (κ +⁺ η)
  q<κ+η =
    Rational.≤<-trans
      {p = q}
      {q = radius (κ +⁺ φ)}
      {r = radius (κ +⁺ η)}
      q≤κ+φ
      κ+φ<κ+η

  -q-φ≤-x : rational ((ℚ.- q) ℚ.- radius φ) ≤ᶜ (-ᶜ x)
  -q-φ≤-x =
    close-rational-lower-bound
      (-ᶜ x)
      (ℚ.- q)
      θ
      φ
      θ<φ
      (neg-close x∼q)

  -q-φ≤κᶜ : rational ((ℚ.- q) ℚ.- radius φ) ≤ᶜ rational (radius κ)
  -q-φ≤κᶜ =
    ≤ᶜ-trans
      {x = rational ((ℚ.- q) ℚ.- radius φ)}
      {y = -ᶜ x}
      {z = rational (radius κ)}
      -q-φ≤-x
      (lowerᶜ {κ = κ} {x = x} bound)

  -q≤κ+φ : ℚ.- q ℚOrder.≤ radius (κ +⁺ φ)
  -q≤κ+φ =
    diff≤→≤+
      (ℚ.- q)
      (radius κ)
      (radius φ)
      (rational≤ᶜ→≤ℚ -q-φ≤κᶜ)

  -q<κ+η : ℚ.- q ℚOrder.< radius (κ +⁺ η)
  -q<κ+η =
    Rational.≤<-trans
      {p = ℚ.- q}
      {q = radius (κ +⁺ φ)}
      {r = radius (κ +⁺ η)}
      -q≤κ+φ
      κ+φ<κ+η


bounded-byᶜ-close-zero :
  (κ μ : ℚ⁺) (x : ℝᶜ) →
  BoundedByᶜ κ x →
  κ <⁺ μ →
  x ∼[ μ ] 0ᶜ
bounded-byᶜ-close-zero κ μ x bound κ<μ =
  Prop.rec squash step (rational-approximation x θ)
  where
  gap : ℚ⁺
  gap = μ ⊖ κ [ κ<μ ]

  φ θ η zeta : ℚ⁺
  φ = quarter⁺ gap
  θ = half⁺ φ
  η = φ +⁺ φ
  zeta = κ +⁺ η

  θ<φ : θ <⁺ φ
  θ<φ =
    half< φ

  φ<η : φ <⁺ η
  φ<η =
    summand-left<sum φ φ

  κ+φ<zeta : radius (κ +⁺ φ) ℚOrder.< radius zeta
  κ+φ<zeta =
    ℚOrder.<-o+ (radius φ) (radius η) (radius κ) φ<η

  θ+η<gap : radius (θ +⁺ η) ℚOrder.< radius gap
  θ+η<gap =
    ℚOrder.isTrans<
      (radius (θ +⁺ η))
      (radius (η +⁺ φ))
      (radius gap)
      θ+η<η+φ
      η+φ<gap
    where
    θ+η<η+φ : radius (θ +⁺ η) ℚOrder.< radius (η +⁺ φ)
    θ+η<η+φ =
      subst
        (λ ρ → ρ ℚOrder.< radius (η +⁺ φ))
        (ℚ.+Comm (radius η) (radius θ))
        (ℚOrder.<-o+ (radius θ) (radius φ) (radius η) θ<φ)

    η+φ<gap : radius (η +⁺ φ) ℚOrder.< radius gap
    η+φ<gap =
      three-quarter< gap

  θ+zeta<μ : θ +⁺ zeta <⁺ μ
  θ+zeta<μ =
    subst
      (λ ρ → ρ ℚOrder.< radius μ)
      (sym
        (SolverHelpers.bounded-close-precision
          ℚCommRing
          (radius θ)
          (radius κ)
          (radius η)))
      (sum<from-difference μ κ (θ +⁺ η) κ<μ θ+η<gap)

  step :
    Σ[ q ∈ ℚ ] x ∼[ θ ] rational q →
    x ∼[ μ ] 0ᶜ
  step (q , x∼q) =
    close-mono
      {ε = θ +⁺ zeta}
      {δ = μ}
      θ+zeta<μ
      (close-triangle
        x∼q
        (point-point-close q 0ℚ zeta q∼0))
    where
    q-φ≤x : rational (q ℚ.- radius φ) ≤ᶜ x
    q-φ≤x =
      close-rational-lower-bound x q θ φ θ<φ x∼q

    q-φ≤κᶜ : rational (q ℚ.- radius φ) ≤ᶜ rational (radius κ)
    q-φ≤κᶜ =
      ≤ᶜ-trans
        {x = rational (q ℚ.- radius φ)}
        {y = x}
        {z = rational (radius κ)}
        q-φ≤x
        (upperᶜ {κ = κ} {x = x} bound)

    q≤κ+φ : q ℚOrder.≤ radius (κ +⁺ φ)
    q≤κ+φ =
      diff≤→≤+
        q
        (radius κ)
        (radius φ)
        (rational≤ᶜ→≤ℚ q-φ≤κᶜ)

    -q-φ≤-x : rational ((ℚ.- q) ℚ.- radius φ) ≤ᶜ (-ᶜ x)
    -q-φ≤-x =
      close-rational-lower-bound
        (-ᶜ x)
        (ℚ.- q)
        θ
        φ
        θ<φ
        (neg-close x∼q)

    -q-φ≤κᶜ : rational ((ℚ.- q) ℚ.- radius φ) ≤ᶜ rational (radius κ)
    -q-φ≤κᶜ =
      ≤ᶜ-trans
        {x = rational ((ℚ.- q) ℚ.- radius φ)}
        {y = -ᶜ x}
        {z = rational (radius κ)}
        -q-φ≤-x
        (lowerᶜ {κ = κ} {x = x} bound)

    -q≤κ+φ : ℚ.- q ℚOrder.≤ radius (κ +⁺ φ)
    -q≤κ+φ =
      diff≤→≤+
        (ℚ.- q)
        (radius κ)
        (radius φ)
        (rational≤ᶜ→≤ℚ -q-φ≤κᶜ)

    q<zeta : q ℚOrder.< radius zeta
    q<zeta =
      Rational.≤<-trans
        {p = q}
        {q = radius (κ +⁺ φ)}
        {r = radius zeta}
        q≤κ+φ
        κ+φ<zeta

    -q<zeta : ℚ.- q ℚOrder.< radius zeta
    -q<zeta =
      Rational.≤<-trans
        {p = ℚ.- q}
        {q = radius (κ +⁺ φ)}
        {r = radius zeta}
        -q≤κ+φ
        κ+φ<zeta

    q∼0 : Closeℚ q zeta 0ℚ
    q∼0 =
      subst
        (λ ρ → ρ ℚOrder.< radius zeta)
        (sym (diff-zero-right q))
        q<zeta ,
      subst
        (λ ρ → ρ ℚOrder.< radius zeta)
        (sym (zero-diff q))
        -q<zeta


bounded-small-scalar-close-zeroᶜ :
  (κ : ℚ⁺) (x : ℝᶜ) →
  BoundedByᶜ κ x →
  (a : ℚ) (ε : ℚ⁺) →
  RationalBoundᶜ ε a →
  scalarMulᶜ a x ∼[ κ *⁺ ε ] 0ᶜ
bounded-small-scalar-close-zeroᶜ κ x x-bound a ε a-bound =
  Prop.rec squash step rounded-bound
  where
  close-zero→bound :
    (δ : ℚ⁺) →
    Closeℚ a δ 0ℚ →
    RationalBoundᶜ δ a
  close-zero→bound δ a∼0 =
    rational-boundᶜ {κ = δ} {q = a}
      (subst
        (λ ρ → ρ ℚOrder.< radius δ)
        (diff-zero-right a)
        (a∼0 .fst))
      (subst
        (λ ρ → ρ ℚOrder.< radius δ)
        (zero-diff a)
        (a∼0 .snd))

  a∼0 : Closeℚ a ε 0ℚ
  a∼0 =
    subst
      (λ ρ → ρ ℚOrder.< radius ε)
      (sym (diff-zero-right a))
      (upperℚ {κ = ε} {q = a} a-bound) ,
    subst
      (λ ρ → ρ ℚOrder.< radius ε)
      (sym (zero-diff a))
      (lowerℚ {κ = ε} {q = a} a-bound)

  rounded-bound :
    ∥ Σ[ δ ∈ ℚ⁺ ] (δ <⁺ ε) × RationalBoundᶜ δ a ∥₁
  rounded-bound =
    Prop.rec squash₁
      (λ (δ , δ<ε , a∼δ0) →
        ∣ δ , δ<ε , close-zero→bound δ a∼δ0 ∣₁)
      (rational-close-rounded a 0ℚ ε a∼0)

  step :
    Σ[ δ ∈ ℚ⁺ ] (δ <⁺ ε) × RationalBoundᶜ δ a →
    scalarMulᶜ a x ∼[ κ *⁺ ε ] 0ᶜ
  step (δ , δ<ε , aδ-bound) =
    bounded-byᶜ-close-zero
      (δ *⁺ κ)
      (κ *⁺ ε)
      (scalarMulᶜ a x)
      (bounded-byᶜ-scale-rational-bound a κ δ x aδ-bound x-bound)
      (product-bound< δ ε κ δ<ε)


rational-approximation-boundᶜ :
  (x : ℝᶜ) (q : ℚ) →
  x ∼[ half⁺ 1⁺ ] rational q →
  BoundedByᶜ (scalar-bound q) x
rational-approximation-boundᶜ x q x∼q =
  bounded-byᶜ {κ = scalar-bound q} {x = x}
    (≤ᶜ-trans
      {x = x}
      {y = rational (q ℚ.+ 1ℚ)}
      {z = rational (radius (scalar-bound q))}
      x≤q+1
      q+1≤bound)
    (≤ᶜ-trans
      {x = -ᶜ x}
      {y = rational ((ℚ.- q) ℚ.+ 1ℚ)}
      {z = rational (radius (scalar-bound q))}
      -x≤-q+1
      -q+1≤bound)
  where
  δ : ℚ⁺
  δ = half⁺ 1⁺

  δ<1 : δ <⁺ 1⁺
  δ<1 =
    half< 1⁺

  x≤q+1 : x ≤ᶜ rational (q ℚ.+ 1ℚ)
  x≤q+1 =
    close-rational-upper-bound x q δ 1⁺ δ<1 x∼q

  -x≤-q+1 : (-ᶜ x) ≤ᶜ rational ((ℚ.- q) ℚ.+ 1ℚ)
  -x≤-q+1 =
    close-rational-upper-bound (-ᶜ x) (ℚ.- q) δ 1⁺ δ<1 (neg-close x∼q)

  q+1≤boundℚ : q ℚ.+ 1ℚ ℚOrder.≤ radius (scalar-bound q)
  q+1≤boundℚ =
    ℚOrder.≤-+o
      q
      (ℚ.max q (ℚ.- q))
      1ℚ
      (ℚOrder.≤max q (ℚ.- q))

  -q+1≤boundℚ : (ℚ.- q) ℚ.+ 1ℚ ℚOrder.≤ radius (scalar-bound q)
  -q+1≤boundℚ =
    ℚOrder.≤-+o
      (ℚ.- q)
      (ℚ.max q (ℚ.- q))
      1ℚ
      (Rational.≤max-r q (ℚ.- q))

  q+1≤bound : rational (q ℚ.+ 1ℚ) ≤ᶜ rational (radius (scalar-bound q))
  q+1≤bound =
    ≤ℚ→rational≤ᶜ q+1≤boundℚ

  -q+1≤bound : rational ((ℚ.- q) ℚ.+ 1ℚ) ≤ᶜ rational (radius (scalar-bound q))
  -q+1≤bound =
    ≤ℚ→rational≤ᶜ -q+1≤boundℚ


merely-boundedᶜ :
  (x : ℝᶜ) →
  ∥ Σ[ κ ∈ ℚ⁺ ] BoundedByᶜ κ x ∥₁
merely-boundedᶜ x =
  Prop.rec squash₁ step (rational-approximation x (half⁺ 1⁺))
  where
  step :
    Σ[ q ∈ ℚ ] x ∼[ half⁺ 1⁺ ] rational q →
    ∥ Σ[ κ ∈ ℚ⁺ ] BoundedByᶜ κ x ∥₁
  step (q , x∼q) =
    ∣ scalar-bound q , rational-approximation-boundᶜ x q x∼q ∣₁
