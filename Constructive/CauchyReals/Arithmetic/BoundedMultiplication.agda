{-

Bounded multiplication interface for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Arithmetic.BoundedMultiplication where

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

open import Constructive.CauchyReals.Arithmetic.Addition
open import Constructive.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.CauchyReals.Arithmetic.Base
open import Constructive.CauchyReals.Arithmetic.Negation
open import Constructive.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.CauchyReals.Arithmetic.ScalarOrder
open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Closeness.Properties
open import Constructive.CauchyReals.Continuity
open import Constructive.CauchyReals.Extension.Properties
open import Constructive.CauchyReals.Lipschitz.Base
open import Constructive.CauchyReals.Order.Bounds
open import Constructive.CauchyReals.Order.Base
open import Constructive.CauchyReals.Order.Density
open import Constructive.CauchyReals.Order.Rational
open import Constructive.CauchyReals.Order.StrictPositive
open import Constructive.CauchyReals.PositiveRationals
import Constructive.Rationals as Rational


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


record RationalBoundᶜ (κ : ℚ⁺) (q : ℚ) : Type₀ where
  constructor rational-boundᶜ

  field
    upperℚ : q ℚOrder.< radius κ
    lowerℚ : ℚ.- q ℚOrder.< radius κ


open RationalBoundᶜ public


record RationalClosedBoundᶜ (κ : ℚ⁺) (q : ℚ) : Type₀ where
  constructor rational-closed-boundᶜ

  field
    upper≤ℚ : q ℚOrder.≤ radius κ
    lower≤ℚ : ℚ.- q ℚOrder.≤ radius κ


open RationalClosedBoundᶜ public


isPropRationalBoundᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  isProp (RationalBoundᶜ κ q)
isPropRationalBoundᶜ κ q b c i =
  rational-boundᶜ
    (ℚOrder.isProp< q (radius κ) (upperℚ b) (upperℚ c) i)
    (ℚOrder.isProp< (ℚ.- q) (radius κ) (lowerℚ b) (lowerℚ c) i)


isPropRationalClosedBoundᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  isProp (RationalClosedBoundᶜ κ q)
isPropRationalClosedBoundᶜ κ q b c i =
  rational-closed-boundᶜ
    (ℚOrder.isProp≤ q (radius κ) (upper≤ℚ b) (upper≤ℚ c) i)
    (ℚOrder.isProp≤ (ℚ.- q) (radius κ) (lower≤ℚ b) (lower≤ℚ c) i)


record BoundedByᶜ (κ : ℚ⁺) (x : ℝᶜ) : Type₀ where
  constructor bounded-byᶜ

  field
    upperᶜ : x ≤ᶜ rational (radius κ)
    lowerᶜ : (-ᶜ x) ≤ᶜ rational (radius κ)


open BoundedByᶜ public


isPropBoundedByᶜ :
  (κ : ℚ⁺) (x : ℝᶜ) →
  isProp (BoundedByᶜ κ x)
isPropBoundedByᶜ κ x b c i =
  bounded-byᶜ
    (isProp≤ᶜ x (rational (radius κ)) (upperᶜ b) (upperᶜ c) i)
    (isProp≤ᶜ (-ᶜ x) (rational (radius κ)) (lowerᶜ b) (lowerᶜ c) i)


scalar-bound-rational-boundᶜ :
  (q : ℚ) →
  RationalBoundᶜ (scalar-bound q) q
scalar-bound-rational-boundᶜ q =
  rational-boundᶜ
    (scalar-bound-upper q)
    (scalar-bound-lower q)


rational-diff-boundᶜ :
  (q r : ℚ) (ε : ℚ⁺) →
  Closeℚ q ε r →
  RationalBoundᶜ ε (q ℚ.- r)
rational-diff-boundᶜ q r ε q∼r =
  rational-boundᶜ
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
  rational-closed-boundᶜ
    (ℚOrder.<Weaken≤ q (radius κ) (upperℚ bound))
    (ℚOrder.<Weaken≤ (ℚ.- q) (radius κ) (lowerℚ bound))


rational-boundᶜ-monotone :
  {κ μ : ℚ⁺} {q : ℚ} →
  radius κ ℚOrder.≤ radius μ →
  RationalBoundᶜ κ q →
  RationalBoundᶜ μ q
rational-boundᶜ-monotone {κ = κ} {μ = μ} {q = q} κ≤μ bound =
  rational-boundᶜ
    (Rational.<≤-trans
      {p = q}
      {q = radius κ}
      {r = radius μ}
      (upperℚ bound)
      κ≤μ)
    (Rational.<≤-trans
      {p = ℚ.- q}
      {q = radius κ}
      {r = radius μ}
      (lowerℚ bound)
      κ≤μ)


rational-closed-boundᶜ-monotone :
  {κ μ : ℚ⁺} {q : ℚ} →
  radius κ ℚOrder.≤ radius μ →
  RationalClosedBoundᶜ κ q →
  RationalClosedBoundᶜ μ q
rational-closed-boundᶜ-monotone {κ = κ} {μ = μ} {q = q} κ≤μ bound =
  rational-closed-boundᶜ
    (Rational.≤-trans
      {p = q}
      {q = radius κ}
      {r = radius μ}
      (upper≤ℚ bound)
      κ≤μ)
    (Rational.≤-trans
      {p = ℚ.- q}
      {q = radius κ}
      {r = radius μ}
      (lower≤ℚ bound)
      κ≤μ)


rational-boundᶜ-neg :
  (κ : ℚ⁺) (q : ℚ) →
  RationalBoundᶜ κ q →
  RationalBoundᶜ κ (ℚ.- q)
rational-boundᶜ-neg κ q bound =
  rational-boundᶜ
    (lowerℚ bound)
    (subst
      (λ r → r ℚOrder.< radius κ)
      (sym (ℚ.-Invol q))
      (upperℚ bound))


rational-closed-boundᶜ-neg :
  (κ : ℚ⁺) (q : ℚ) →
  RationalClosedBoundᶜ κ q →
  RationalClosedBoundᶜ κ (ℚ.- q)
rational-closed-boundᶜ-neg κ q bound =
  rational-closed-boundᶜ
    (lower≤ℚ bound)
    (subst
      (λ r → r ℚOrder.≤ radius κ)
      (sym (ℚ.-Invol q))
      (upper≤ℚ bound))


rational-bound→boundedᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  RationalBoundᶜ κ q →
  BoundedByᶜ κ (rational q)
rational-bound→boundedᶜ κ q bound =
  bounded-byᶜ
    (≤ℚ→rational≤ᶜ
      (ℚOrder.<Weaken≤ q (radius κ) (upperℚ bound)))
    (≤ℚ→rational≤ᶜ
      (ℚOrder.<Weaken≤ (ℚ.- q) (radius κ) (lowerℚ bound)))


rational-closed-bound→boundedᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  RationalClosedBoundᶜ κ q →
  BoundedByᶜ κ (rational q)
rational-closed-bound→boundedᶜ κ q bound =
  bounded-byᶜ
    (≤ℚ→rational≤ᶜ (upper≤ℚ bound))
    (≤ℚ→rational≤ᶜ (lower≤ℚ bound))


bounded-rational→closed-boundᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  BoundedByᶜ κ (rational q) →
  RationalClosedBoundᶜ κ q
bounded-rational→closed-boundᶜ κ q bound =
  rational-closed-boundᶜ
    (rational≤ᶜ→≤ℚ (upperᶜ bound))
    (rational≤ᶜ→≤ℚ (lowerᶜ bound))


bounded-byᶜ-monotone :
  {κ μ : ℚ⁺} {x : ℝᶜ} →
  radius κ ℚOrder.≤ radius μ →
  BoundedByᶜ κ x →
  BoundedByᶜ μ x
bounded-byᶜ-monotone {κ = κ} {μ = μ} {x = x} κ≤μ bound =
  bounded-byᶜ
    (≤ᶜ-trans
      {x = x}
      {y = rational (radius κ)}
      {z = rational (radius μ)}
      (upperᶜ bound)
      κ≤μᶜ)
    (≤ᶜ-trans
      {x = -ᶜ x}
      {y = rational (radius κ)}
      {z = rational (radius μ)}
      (lowerᶜ bound)
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
  bounded-byᶜ
    (lowerᶜ bound)
    (subst
      (λ w → w ≤ᶜ rational (radius κ))
      (sym (neg-involutive x))
      (upperᶜ bound))


bounded-byᶜ-add :
  (κ μ : ℚ⁺) (x y : ℝᶜ) →
  BoundedByᶜ κ x →
  BoundedByᶜ μ y →
  BoundedByᶜ (κ +⁺ μ) (x +ᶜ y)
bounded-byᶜ-add κ μ x y x-bound y-bound =
  bounded-byᶜ
    (subst
      ((x +ᶜ y) ≤ᶜ_)
      (add-rational (radius κ) (radius μ))
      (≤ᶜ-add
        {a = x}
        {b = rational (radius κ)}
        {c = y}
        {d = rational (radius μ)}
        (upperᶜ x-bound)
        (upperᶜ y-bound)))
    (subst2
      _≤ᶜ_
      (sym (neg-add x y))
      (add-rational (radius κ) (radius μ))
      (≤ᶜ-add
        {a = -ᶜ x}
        {b = rational (radius κ)}
        {c = -ᶜ y}
        {d = rational (radius μ)}
        (lowerᶜ x-bound)
        (lowerᶜ y-bound)))


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
  bounded-byᶜ
    (≤ᶜ-trans
      {x = scalarMulᶜ a x}
      {y = scalarMulᶜ a (rational (radius κ))}
      {z = rational (radius (μ *⁺ κ))}
      (scalarMulᶜ-pres≤ᶜ-nonnegative
        a
        0≤a
        {x = x}
        {y = rational (radius κ)}
        (upperᶜ x-bound))
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
          (lowerᶜ x-bound))
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
      (Rational.<→≤ {p = a} {q = radius μ} (upperℚ a-bound))
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
          (Rational.<→≤ {p = ℚ.- a} {q = radius μ} (lowerℚ a-bound))
          x-bound))


bounded-approximation-rational-boundᶜ :
  (κ φ η θ : ℚ⁺) (x : ℝᶜ) (q : ℚ) →
  θ <⁺ φ →
  φ <⁺ η →
  BoundedByᶜ κ x →
  x ∼[ θ ] rational q →
  RationalBoundᶜ (κ +⁺ η) q
bounded-approximation-rational-boundᶜ κ φ η θ x q θ<φ φ<η bound x∼q =
  rational-boundᶜ q<κ+η -q<κ+η
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
      (upperᶜ bound)

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
      (lowerᶜ bound)

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
        (rational-rational-close q 0ℚ zeta q∼0))
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
        (upperᶜ bound)

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
        (lowerᶜ bound)

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
    rational-boundᶜ
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
      (upperℚ a-bound) ,
    subst
      (λ ρ → ρ ℚOrder.< radius ε)
      (sym (zero-diff a))
      (lowerℚ a-bound)

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


boundedMul-rational-leftᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  RationalBoundᶜ κ q →
  ℝᶜ → ℝᶜ
boundedMul-rational-leftᶜ κ q bound =
  boundedScalarMulᶜ q κ (upperℚ bound) (lowerℚ bound)


boundedMul-rational-leftᶜ-rational :
  (κ : ℚ⁺) (q r : ℚ) →
  (bound : RationalBoundᶜ κ q) →
  boundedMul-rational-leftᶜ κ q bound (rational r) ≡
  rational (q ℚ.· r)
boundedMul-rational-leftᶜ-rational κ q r bound =
  boundedScalarMulᶜ-rational q κ (upperℚ bound) (lowerℚ bound) r


boundedMul-rational-leftᶜ-close :
  (κ : ℚ⁺) (q : ℚ) →
  (bound : RationalBoundᶜ κ q) →
  {x y : ℝᶜ} {ε : ℚ⁺} →
  x ∼[ ε ] y →
  boundedMul-rational-leftᶜ κ q bound x
    ∼[ κ *⁺ ε ]
  boundedMul-rational-leftᶜ κ q bound y
boundedMul-rational-leftᶜ-close κ q bound =
  boundedScalarMulᶜ-close q κ (upperℚ bound) (lowerℚ bound)


scalarMulᶜ-close-rational-bound :
  (q : ℚ) (κ : ℚ⁺) →
  RationalBoundᶜ κ q →
  {x y : ℝᶜ} {ε : ℚ⁺} →
  x ∼[ ε ] y →
  scalarMulᶜ q x ∼[ κ *⁺ ε ] scalarMulᶜ q y
scalarMulᶜ-close-rational-bound q κ bound {x = x} {y = y} x∼y =
  subst2
    (λ u v → u ∼[ _ ] v)
    (sym scalar≡bounded-x)
    (sym scalar≡bounded-y)
    (boundedMul-rational-leftᶜ-close κ q bound x∼y)
  where
  scalar≡bounded-x :
    scalarMulᶜ q x ≡ boundedMul-rational-leftᶜ κ q bound x
  scalar≡bounded-x =
    boundedScalarMulᶜ-bound-independent
      q
      (scalar-bound q)
      κ
      (scalar-bound-upper q)
      (scalar-bound-lower q)
      (upperℚ bound)
      (lowerℚ bound)
      x

  scalar≡bounded-y :
    scalarMulᶜ q y ≡ boundedMul-rational-leftᶜ κ q bound y
  scalar≡bounded-y =
    boundedScalarMulᶜ-bound-independent
      q
      (scalar-bound q)
      κ
      (scalar-bound-upper q)
      (scalar-bound-lower q)
      (upperℚ bound)
      (lowerℚ bound)
      y


boundedMul-rational-leftᶜ-lipschitz :
  (κ : ℚ⁺) (q : ℚ) →
  (bound : RationalBoundᶜ κ q) →
  IsLipschitz (boundedMul-rational-leftᶜ κ q bound)
boundedMul-rational-leftᶜ-lipschitz κ q bound =
  boundedScalarMulᶜ-lipschitz q κ (upperℚ bound) (lowerℚ bound)


boundedMul-rational-leftᶜ-continuous :
  (κ : ℚ⁺) (q : ℚ) →
  (bound : RationalBoundᶜ κ q) →
  IsContinuous (boundedMul-rational-leftᶜ κ q bound)
boundedMul-rational-leftᶜ-continuous κ q bound =
  boundedScalarMulᶜ-continuous q κ (upperℚ bound) (lowerℚ bound)


boundedMul-rational-leftᶜ-bound-independent :
  (κ μ : ℚ⁺) (q : ℚ)
  (κ-bound : RationalBoundᶜ κ q)
  (μ-bound : RationalBoundᶜ μ q)
  (x : ℝᶜ) →
  boundedMul-rational-leftᶜ κ q κ-bound x ≡
  boundedMul-rational-leftᶜ μ q μ-bound x
boundedMul-rational-leftᶜ-bound-independent κ μ q κ-bound μ-bound =
  boundedScalarMulᶜ-bound-independent
    q
    κ
    μ
    (upperℚ κ-bound)
    (lowerℚ κ-bound)
    (upperℚ μ-bound)
    (lowerℚ μ-bound)


boundedMul-rational-leftᶜ-distrib-real-add :
  (κ : ℚ⁺) (q : ℚ) (bound : RationalBoundᶜ κ q)
  (x y : ℝᶜ) →
  boundedMul-rational-leftᶜ κ q bound (x +ᶜ y) ≡
  boundedMul-rational-leftᶜ κ q bound x +ᶜ
  boundedMul-rational-leftᶜ κ q bound y
boundedMul-rational-leftᶜ-distrib-real-add κ q bound =
  boundedScalarMulᶜ-distrib-real-add
    q
    κ
    (upperℚ bound)
    (lowerℚ bound)


boundedMul-rational-leftᶜ-zero-right :
  (κ : ℚ⁺) (q : ℚ) (bound : RationalBoundᶜ κ q) →
  boundedMul-rational-leftᶜ κ q bound 0ᶜ ≡ 0ᶜ
boundedMul-rational-leftᶜ-zero-right κ q bound =
  boundedScalarMulᶜ-zero-right
    q
    κ
    (upperℚ bound)
    (lowerℚ bound)


boundedMul-rational-leftᶜ-zero-left :
  (κ : ℚ⁺) (bound : RationalBoundᶜ κ 0ℚ) (x : ℝᶜ) →
  boundedMul-rational-leftᶜ κ 0ℚ bound x ≡ 0ᶜ
boundedMul-rational-leftᶜ-zero-left κ bound =
  boundedScalarMulᶜ-zero-scalar
    κ
    (upperℚ bound)
    (lowerℚ bound)


boundedMul-rational-leftᶜ-neg-real :
  (κ : ℚ⁺) (q : ℚ) (bound : RationalBoundᶜ κ q)
  (x : ℝᶜ) →
  boundedMul-rational-leftᶜ κ q bound (-ᶜ x) ≡
  -ᶜ (boundedMul-rational-leftᶜ κ q bound x)
boundedMul-rational-leftᶜ-neg-real κ q bound =
  boundedScalarMulᶜ-neg-real
    q
    κ
    (upperℚ bound)
    (lowerℚ bound)


boundedMul-rational-leftᶜ-neg-left :
  (κ : ℚ⁺) (q : ℚ) (bound : RationalBoundᶜ κ q)
  (x : ℝᶜ) →
  boundedMul-rational-leftᶜ κ (ℚ.- q) (rational-boundᶜ-neg κ q bound) x ≡
  -ᶜ (boundedMul-rational-leftᶜ κ q bound x)
boundedMul-rational-leftᶜ-neg-left κ q bound =
  boundedScalarMulᶜ-neg-scalar
    q
    κ
    (upperℚ bound)
    (lowerℚ bound)
    (lowerℚ (rational-boundᶜ-neg κ q bound))


RationalRightMultiplierᶜ :
  ℚ⁺ →
  ℝᶜ →
  Type₀
RationalRightMultiplierᶜ κ x =
  IsRationalLipschitzWithᶜ κ (λ q → scalarMulᶜ q x)


scalarMulᶜ-diff :
  (q r : ℚ) (x : ℝᶜ) →
  scalarMulᶜ (q ℚ.- r) x ≡
  scalarMulᶜ q x +ᶜ (-ᶜ (scalarMulᶜ r x))
scalarMulᶜ-diff q r x =
  scalarMulᶜ-distrib-scalar-add q (ℚ.- r) x ∙
  cong (scalarMulᶜ q x +ᶜ_) (scalarMulᶜ-neg-scalar r x)


bounded-real-right-multiplierᶜ :
  (κ : ℚ⁺) (x : ℝᶜ) →
  BoundedByᶜ κ x →
  RationalRightMultiplierᶜ κ x
bounded-real-right-multiplierᶜ κ x x-bound q r ε q∼r =
  diff-close-zero→close
    (subst
      (λ y → y ∼[ κ *⁺ ε ] 0ᶜ)
      (scalarMulᶜ-diff q r x)
      (bounded-small-scalar-close-zeroᶜ
        κ
        x
        x-bound
        (q ℚ.- r)
        ε
        (rational-diff-boundᶜ q r ε q∼r)))


boundedMul-leftᶜ :
  (κ : ℚ⁺) (x : ℝᶜ) →
  BoundedByᶜ κ x →
  RationalRightMultiplierᶜ κ x →
  ℝᶜ → ℝᶜ
boundedMul-leftᶜ κ x x-bound x-lip =
  extendRationalLipschitzWithᶜ κ (λ q → scalarMulᶜ q x) x-lip


boundedMul-leftᶜ-rational :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (x-lip : RationalRightMultiplierᶜ κ x)
  (q : ℚ) →
  boundedMul-leftᶜ κ x x-bound x-lip (rational q) ≡
  scalarMulᶜ q x
boundedMul-leftᶜ-rational κ x x-bound x-lip q =
  refl


boundedMul-leftᶜ-close :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (x-lip : RationalRightMultiplierᶜ κ x) →
  {y z : ℝᶜ} {ε : ℚ⁺} →
  y ∼[ ε ] z →
  boundedMul-leftᶜ κ x x-bound x-lip y
    ∼[ κ *⁺ ε ]
  boundedMul-leftᶜ κ x x-bound x-lip z
boundedMul-leftᶜ-close κ x x-bound x-lip =
  extendRationalLipschitzWithᶜ-close
    κ
    (λ q → scalarMulᶜ q x)
    x-lip


boundedMul-leftᶜ-lipschitz :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (x-lip : RationalRightMultiplierᶜ κ x) →
  IsLipschitz (boundedMul-leftᶜ κ x x-bound x-lip)
boundedMul-leftᶜ-lipschitz κ x x-bound x-lip =
  extendRationalLipschitzWithᶜ-lipschitz
    κ
    (λ q → scalarMulᶜ q x)
    x-lip


boundedMul-leftᶜ-continuous :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (x-lip : RationalRightMultiplierᶜ κ x) →
  IsContinuous (boundedMul-leftᶜ κ x x-bound x-lip)
boundedMul-leftᶜ-continuous κ x x-bound x-lip =
  extendRationalLipschitzWithᶜ-continuous
    κ
    (λ q → scalarMulᶜ q x)
    x-lip


boundedMul-leftᶜ-bound-independent :
  (κ μ : ℚ⁺) (x : ℝᶜ)
  (κ-bound : BoundedByᶜ κ x)
  (μ-bound : BoundedByᶜ μ x)
  (κ-lip : RationalRightMultiplierᶜ κ x)
  (μ-lip : RationalRightMultiplierᶜ μ x)
  (y : ℝᶜ) →
  boundedMul-leftᶜ κ x κ-bound κ-lip y ≡
  boundedMul-leftᶜ μ x μ-bound μ-lip y
boundedMul-leftᶜ-bound-independent κ μ x κ-bound μ-bound κ-lip μ-lip =
  continuous-equal
    (boundedMul-leftᶜ κ x κ-bound κ-lip)
    (boundedMul-leftᶜ μ x μ-bound μ-lip)
    (boundedMul-leftᶜ-continuous κ x κ-bound κ-lip)
    (boundedMul-leftᶜ-continuous μ x μ-bound μ-lip)
    (λ _ → refl)


boundedMul-leftᶜ-zero-right :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (x-lip : RationalRightMultiplierᶜ κ x) →
  boundedMul-leftᶜ κ x x-bound x-lip 0ᶜ ≡ 0ᶜ
boundedMul-leftᶜ-zero-right κ x x-bound x-lip =
  scalarMulᶜ-zero x


boundedMul-leftᶜ-zero-left :
  (κ : ℚ⁺)
  (0-bound : BoundedByᶜ κ 0ᶜ)
  (0-lip : RationalRightMultiplierᶜ κ 0ᶜ)
  (y : ℝᶜ) →
  boundedMul-leftᶜ κ 0ᶜ 0-bound 0-lip y ≡ 0ᶜ
boundedMul-leftᶜ-zero-left κ 0-bound 0-lip =
  continuous-constant-equal
    (boundedMul-leftᶜ κ 0ᶜ 0-bound 0-lip)
    0ᶜ
    (boundedMul-leftᶜ-continuous κ 0ᶜ 0-bound 0-lip)
    (λ q → scalarMulᶜ-zero-right q)


boundedMul-leftᶜ-neg-right :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (x-lip : RationalRightMultiplierᶜ κ x)
  (y : ℝᶜ) →
  boundedMul-leftᶜ κ x x-bound x-lip (-ᶜ y) ≡
  -ᶜ (boundedMul-leftᶜ κ x x-bound x-lip y)
boundedMul-leftᶜ-neg-right κ x x-bound x-lip =
  continuous-equal
    (λ y → boundedMul-leftᶜ κ x x-bound x-lip (-ᶜ y))
    (λ y → -ᶜ (boundedMul-leftᶜ κ x x-bound x-lip y))
    (comp-continuous
      (boundedMul-leftᶜ-continuous κ x x-bound x-lip)
      neg-continuous)
    (comp-continuous
      neg-continuous
      (boundedMul-leftᶜ-continuous κ x x-bound x-lip))
    (λ q → scalarMulᶜ-neg-scalar q x)


boundedMul-leftᶜ-distrib-real-add-rational-left :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (x-lip : RationalRightMultiplierᶜ κ x)
  (q : ℚ) (y : ℝᶜ) →
  boundedMul-leftᶜ κ x x-bound x-lip (rational q +ᶜ y) ≡
  scalarMulᶜ q x +ᶜ boundedMul-leftᶜ κ x x-bound x-lip y
boundedMul-leftᶜ-distrib-real-add-rational-left κ x x-bound x-lip q =
  continuous-equal
    (λ y → boundedMul-leftᶜ κ x x-bound x-lip (rational q +ᶜ y))
    (λ y → scalarMulᶜ q x +ᶜ boundedMul-leftᶜ κ x x-bound x-lip y)
    (comp-continuous
      (boundedMul-leftᶜ-continuous κ x x-bound x-lip)
      (add-continuous-right (rational q)))
    (comp-continuous
      (add-continuous-right (scalarMulᶜ q x))
      (boundedMul-leftᶜ-continuous κ x x-bound x-lip))
    (λ r → scalarMulᶜ-distrib-scalar-add q r x)


boundedMul-leftᶜ-distrib-real-add :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (x-lip : RationalRightMultiplierᶜ κ x)
  (y z : ℝᶜ) →
  boundedMul-leftᶜ κ x x-bound x-lip (y +ᶜ z) ≡
  boundedMul-leftᶜ κ x x-bound x-lip y +ᶜ
  boundedMul-leftᶜ κ x x-bound x-lip z
boundedMul-leftᶜ-distrib-real-add κ x x-bound x-lip y z =
  continuous-equal
    (λ w → boundedMul-leftᶜ κ x x-bound x-lip (w +ᶜ z))
    (λ w →
      boundedMul-leftᶜ κ x x-bound x-lip w +ᶜ
      boundedMul-leftᶜ κ x x-bound x-lip z)
    (comp-continuous
      (boundedMul-leftᶜ-continuous κ x x-bound x-lip)
      (add-continuous-left z))
    (comp-continuous
      (add-continuous-left (boundedMul-leftᶜ κ x x-bound x-lip z))
      (boundedMul-leftᶜ-continuous κ x x-bound x-lip))
    (λ q → boundedMul-leftᶜ-distrib-real-add-rational-left κ x x-bound x-lip q z)
    y


boundedMulᶜ :
  (κ : ℚ⁺) (x : ℝᶜ) →
  BoundedByᶜ κ x →
  ℝᶜ → ℝᶜ
boundedMulᶜ κ x x-bound =
  boundedMul-leftᶜ
    κ
    x
    x-bound
    (bounded-real-right-multiplierᶜ κ x x-bound)


boundedMulᶜ-rational :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (q : ℚ) →
  boundedMulᶜ κ x x-bound (rational q) ≡
  scalarMulᶜ q x
boundedMulᶜ-rational κ x x-bound =
  boundedMul-leftᶜ-rational
    κ
    x
    x-bound
    (bounded-real-right-multiplierᶜ κ x x-bound)


boundedMulᶜ-close :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x) →
  {y z : ℝᶜ} {ε : ℚ⁺} →
  y ∼[ ε ] z →
  boundedMulᶜ κ x x-bound y
    ∼[ κ *⁺ ε ]
  boundedMulᶜ κ x x-bound z
boundedMulᶜ-close κ x x-bound =
  boundedMul-leftᶜ-close
    κ
    x
    x-bound
    (bounded-real-right-multiplierᶜ κ x x-bound)


boundedMulᶜ-lipschitz :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x) →
  IsLipschitz (boundedMulᶜ κ x x-bound)
boundedMulᶜ-lipschitz κ x x-bound =
  boundedMul-leftᶜ-lipschitz
    κ
    x
    x-bound
    (bounded-real-right-multiplierᶜ κ x x-bound)


boundedMulᶜ-continuous :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x) →
  IsContinuous (boundedMulᶜ κ x x-bound)
boundedMulᶜ-continuous κ x x-bound =
  boundedMul-leftᶜ-continuous
    κ
    x
    x-bound
    (bounded-real-right-multiplierᶜ κ x x-bound)


boundedMulᶜ-bound-independent :
  (κ μ : ℚ⁺) (x : ℝᶜ)
  (κ-bound : BoundedByᶜ κ x)
  (μ-bound : BoundedByᶜ μ x)
  (y : ℝᶜ) →
  boundedMulᶜ κ x κ-bound y ≡
  boundedMulᶜ μ x μ-bound y
boundedMulᶜ-bound-independent κ μ x κ-bound μ-bound =
  boundedMul-leftᶜ-bound-independent
    κ
    μ
    x
    κ-bound
    μ-bound
    (bounded-real-right-multiplierᶜ κ x κ-bound)
    (bounded-real-right-multiplierᶜ μ x μ-bound)


boundedMulᶜ-zero-right :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x) →
  boundedMulᶜ κ x x-bound 0ᶜ ≡ 0ᶜ
boundedMulᶜ-zero-right κ x x-bound =
  boundedMul-leftᶜ-zero-right
    κ
    x
    x-bound
    (bounded-real-right-multiplierᶜ κ x x-bound)


boundedMulᶜ-zero-left :
  (κ : ℚ⁺)
  (0-bound : BoundedByᶜ κ 0ᶜ)
  (y : ℝᶜ) →
  boundedMulᶜ κ 0ᶜ 0-bound y ≡ 0ᶜ
boundedMulᶜ-zero-left κ 0-bound =
  boundedMul-leftᶜ-zero-left
    κ
    0-bound
    (bounded-real-right-multiplierᶜ κ 0ᶜ 0-bound)


boundedMulᶜ-neg-right :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (y : ℝᶜ) →
  boundedMulᶜ κ x x-bound (-ᶜ y) ≡
  -ᶜ (boundedMulᶜ κ x x-bound y)
boundedMulᶜ-neg-right κ x x-bound =
  boundedMul-leftᶜ-neg-right
    κ
    x
    x-bound
    (bounded-real-right-multiplierᶜ κ x x-bound)


boundedMulᶜ-distrib-real-add :
  (κ : ℚ⁺) (x : ℝᶜ)
  (x-bound : BoundedByᶜ κ x)
  (y z : ℝᶜ) →
  boundedMulᶜ κ x x-bound (y +ᶜ z) ≡
  boundedMulᶜ κ x x-bound y +ᶜ
  boundedMulᶜ κ x x-bound z
boundedMulᶜ-distrib-real-add κ x x-bound =
  boundedMul-leftᶜ-distrib-real-add
    κ
    x
    x-bound
    (bounded-real-right-multiplierᶜ κ x x-bound)


rational-right-multiplier-closedᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  RationalClosedBoundᶜ κ q →
  RationalRightMultiplierᶜ κ (rational q)
rational-right-multiplier-closedᶜ κ q bound r s ε r∼s =
  subst2
    (λ a b → rational a ∼[ κ *⁺ ε ] rational b)
    (ℚ.·Comm q r)
    (ℚ.·Comm q s)
    (rational-rational-close
      (q ℚ.· r)
      (q ℚ.· s)
      (κ *⁺ ε)
      (scale-close-closed-bound q κ (upper≤ℚ bound) (lower≤ℚ bound) r s ε r∼s))


rational-right-multiplierᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  RationalBoundᶜ κ q →
  RationalRightMultiplierᶜ κ (rational q)
rational-right-multiplierᶜ κ q bound =
  rational-right-multiplier-closedᶜ
    κ
    q
    (rational-bound→closedᶜ κ q bound)


rational-right-multiplier-from-boundedᶜ :
  (κ : ℚ⁺) (q : ℚ) →
  (bound : BoundedByᶜ κ (rational q)) →
  RationalRightMultiplierᶜ κ (rational q)
rational-right-multiplier-from-boundedᶜ κ q bound =
  rational-right-multiplier-closedᶜ
    κ
    q
    (bounded-rational→closed-boundᶜ κ q bound)


boundedMul-leftᶜ-rational-left-from-bounded :
  (κ : ℚ⁺) (q : ℚ)
  (bound : BoundedByᶜ κ (rational q))
  (q-lip : RationalRightMultiplierᶜ κ (rational q))
  (y : ℝᶜ) →
  boundedMul-leftᶜ κ (rational q) bound q-lip y ≡
  scalarMulᶜ q y
boundedMul-leftᶜ-rational-left-from-bounded κ q bound q-lip =
  continuous-equal
    (boundedMul-leftᶜ κ (rational q) bound q-lip)
    (scalarMulᶜ q)
    (boundedMul-leftᶜ-continuous κ (rational q) bound q-lip)
    (scalarMulᶜ-continuous q)
    rational-path
  where
  rational-path :
    (r : ℚ) →
    boundedMul-leftᶜ κ (rational q) bound q-lip (rational r) ≡
    scalarMulᶜ q (rational r)
  rational-path r =
    boundedMul-leftᶜ-rational κ (rational q) bound q-lip r ∙
    scalarMulᶜ-rational r q ∙
    cong rational (ℚ.·Comm r q) ∙
    sym (scalarMulᶜ-rational q r)


boundedMulᶜ-rational-left-from-bounded :
  (κ : ℚ⁺) (q : ℚ)
  (bound : BoundedByᶜ κ (rational q))
  (y : ℝᶜ) →
  boundedMulᶜ κ (rational q) bound y ≡
  scalarMulᶜ q y
boundedMulᶜ-rational-left-from-bounded κ q bound =
  boundedMul-leftᶜ-rational-left-from-bounded
    κ
    q
    bound
    (bounded-real-right-multiplierᶜ κ (rational q) bound)


boundedMul-leftᶜ-rational-left :
  (κ : ℚ⁺) (q : ℚ) (bound : RationalBoundᶜ κ q)
  (y : ℝᶜ) →
  boundedMul-leftᶜ
    κ
    (rational q)
    (rational-bound→boundedᶜ κ q bound)
    (rational-right-multiplierᶜ κ q bound)
    y ≡
  boundedMul-rational-leftᶜ κ q bound y
boundedMul-leftᶜ-rational-left κ q bound =
  continuous-equal
    (boundedMul-leftᶜ
      κ
      (rational q)
      (rational-bound→boundedᶜ κ q bound)
      (rational-right-multiplierᶜ κ q bound))
    (boundedMul-rational-leftᶜ κ q bound)
    (boundedMul-leftᶜ-continuous
      κ
      (rational q)
      (rational-bound→boundedᶜ κ q bound)
      (rational-right-multiplierᶜ κ q bound))
    (boundedMul-rational-leftᶜ-continuous κ q bound)
    (λ r → cong rational (ℚ.·Comm r q))


rational-approximation-boundᶜ :
  (x : ℝᶜ) (q : ℚ) →
  x ∼[ half⁺ 1⁺ ] rational q →
  BoundedByᶜ (scalar-bound q) x
rational-approximation-boundᶜ x q x∼q =
  bounded-byᶜ
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
