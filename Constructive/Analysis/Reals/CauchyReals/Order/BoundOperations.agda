{-

Cauchy-real boundedness and rational bounds

-}
{-# OPTIONS --safe #-}

module Constructive.Analysis.Reals.CauchyReals.Order.BoundOperations where

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
open import Constructive.Analysis.Reals.CauchyReals.Order.Approximation
open import Constructive.Analysis.Reals.CauchyReals.Order.BoundDefinitions
open import Constructive.Analysis.Reals.CauchyReals.Order.Density
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive using (≤ᶜ-add)
open import Constructive.Data.PositiveRationals
open import Constructive.Data.Rationals.Closeness
import Constructive.Data.Rationals as Rational


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    neg-diff :
      (q r : 𝓡 .fst) →
      - (q + (- r)) ≡ r + (- q)
    neg-diff _ _ = solve! 𝓡

  neg-diff :
    (q r : ℚ) →
    ℚ.- (q ℚ.- r) ≡ r ℚ.- q
  neg-diff =
    SolverHelpers.neg-diff ℚCommRing

  diff-close-zero→close-private :
    {x y : ℝᶜ} {ε : ℚ⁺} →
    (x +ᶜ (-ᶜ y)) ∼[ ε ] 0ᶜ →
    x ∼[ ε ] y
  diff-close-zero→close-private {x = x} {y = y} {ε = ε} diff∼0 =
    subst2
      (λ u v → u ∼[ ε ] v)
      (minus-plus-cancel-right x y)
      (add-zero-left y)
      (add-close-left diff∼0 y)


diff-close-zero→close :
  {x y : ℝᶜ} {ε : ℚ⁺} →
  (x +ᶜ (-ᶜ y)) ∼[ ε ] 0ᶜ →
  x ∼[ ε ] y
diff-close-zero→close =
  diff-close-zero→close-private



close-zero→bounded-byᶜ :
  {δ ε : ℚ⁺} →
  (x : ℝᶜ) →
  δ <⁺ ε →
  x ∼[ δ ] 0ᶜ →
  BoundedByᶜ ε x
close-zero→bounded-byᶜ {δ = δ} {ε = ε} x δ<ε x∼0 =
  bounded-byᶜ {κ = ε} {x = x} upperBound lowerBound
  where
  normalizeUpper :
    rational (Rational.0ℚ ℚ.+ radius ε) ≡ rational (radius ε)
  normalizeUpper =
    cong rational (ℚ.+IdL (radius ε))

  upperBound :
    x ≤ᶜ rational (radius ε)
  upperBound =
    subst
      (x ≤ᶜ_)
      normalizeUpper
      (close-rational-upper-bound
        x
        Rational.0ℚ
        δ
        ε
        δ<ε
        x∼0)

  -x∼0 :
    (-ᶜ x) ∼[ δ ] 0ᶜ
  -x∼0 =
    subst
      (λ y → (-ᶜ x) ∼[ δ ] y)
      (cong rational Rational.neg-zero)
      (neg-close x∼0)

  lowerBound :
    (-ᶜ x) ≤ᶜ rational (radius ε)
  lowerBound =
    subst
      ((-ᶜ x) ≤ᶜ_)
      normalizeUpper
      (close-rational-upper-bound
        (-ᶜ x)
        Rational.0ℚ
        δ
        ε
        δ<ε
        -x∼0)


close→difference-bounded-byᶜ :
  {δ ε : ℚ⁺} →
  (x y : ℝᶜ) →
  δ <⁺ ε →
  x ∼[ δ ] y →
  BoundedByᶜ ε (x +ᶜ (-ᶜ y))
close→difference-bounded-byᶜ {δ = δ} {ε = ε} x y δ<ε x∼y =
  close-zero→bounded-byᶜ
    {δ = δ}
    {ε = ε}
    (x +ᶜ (-ᶜ y))
    δ<ε
    diff∼0
  where
  diff∼0 :
    (x +ᶜ (-ᶜ y)) ∼[ δ ] 0ᶜ
  diff∼0 =
    subst
      (λ z → (x +ᶜ (-ᶜ y)) ∼[ δ ] z)
      (add-inverse-right y)
      (add-close-left x∼y (-ᶜ y))


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


bounded-byᶜ-zero :
  (ε : ℚ⁺) →
  BoundedByᶜ ε 0ᶜ
bounded-byᶜ-zero ε =
  rational-closed-bound→boundedᶜ
    ε
    Rational.0ℚ
    (rational-closed-boundᶜ
      {κ = ε}
      {q = Rational.0ℚ}
      0≤ε
      (subst
        (λ q → q ℚOrder.≤ radius ε)
        (sym Rational.neg-zero)
        0≤ε))
  where
  0≤ε : Rational.0ℚ ℚOrder.≤ radius ε
  0≤ε =
    ℚOrder.<Weaken≤ Rational.0ℚ (radius ε) (ε .snd)




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


bounded-byᶜ-scale-rational-closed-bound :
  (a : ℚ) (κ μ : ℚ⁺) (x : ℝᶜ) →
  RationalClosedBoundᶜ μ a →
  BoundedByᶜ κ x →
  BoundedByᶜ (μ *⁺ κ) (scalarMulᶜ a x)
bounded-byᶜ-scale-rational-closed-bound a κ μ x a-bound x-bound =
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
      (upper≤ℚ {κ = μ} {q = a} a-bound)
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
          (lower≤ℚ {κ = μ} {q = a} a-bound)
          x-bound))


oneBoundedᶜ :
  BoundedByᶜ 1⁺ 1ᶜ
oneBoundedᶜ =
  rational-closed-bound→boundedᶜ
    1⁺
    Rational.1ℚ
    (rational-closed-boundᶜ
      {κ = 1⁺}
      {q = Rational.1ℚ}
      (Rational.≤-refl Rational.1ℚ)
      (Rational.<→≤
        {p = Rational.-1ℚ}
        {q = Rational.1ℚ}
        (ℚOrder.isTrans<
          Rational.-1ℚ
          Rational.0ℚ
          Rational.1ℚ
          Rational.-1<0
          Rational.0<1)))
