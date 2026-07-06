{-

First reciprocal interfaces for HoTT Cauchy reals

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.CauchyReals.Arithmetic.BoundedReciprocal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax; _,_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Relation.Nullary
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.CauchyReals.Arithmetic.Base
open import Constructive.CauchyReals.Arithmetic.BoundedMultiplication
open import Constructive.CauchyReals.Arithmetic.Multiplication
open import Constructive.CauchyReals.Arithmetic.Negation
open import Constructive.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Closeness.Properties
open import Constructive.CauchyReals.Continuity
open import Constructive.CauchyReals.Lipschitz.Base
open import Constructive.CauchyReals.Order.Base
open import Constructive.CauchyReals.Order.Bounds
open import Constructive.CauchyReals.Order.Density
open import Constructive.CauchyReals.Order.Rational
open import Constructive.CauchyReals.Order.StrictPositive
open import Constructive.CauchyReals.PositiveRationals
import Constructive.Rationals as Rational


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    inv-diff :
      (u v u⁻¹ v⁻¹ : 𝓡 .fst) →
      (v · v⁻¹) · u⁻¹ + (- ((u · u⁻¹) · v⁻¹)) ≡
      (v + (- u)) · (u⁻¹ · v⁻¹)
    inv-diff _ _ _ _ = solve! 𝓡

    positive-product-bound :
      (δ κ : 𝓡 .fst) →
      δ · κ ≡ κ · δ
    positive-product-bound _ _ = solve! 𝓡

  posInv-reverse≤ :
    {p q : ℚ} →
    (0<p : 0ℚ ℚOrder.< p) →
    (0<q : 0ℚ ℚOrder.< q) →
    p ℚOrder.≤ q →
    Rational.posInv q 0<q ℚOrder.≤ Rational.posInv p 0<p
  posInv-reverse≤ {p = p} {q = q} 0<p 0<q p≤q =
    ℚOrder.≮→≥
      (Rational.posInv p 0<p)
      (Rational.posInv q 0<q)
      not-invp<invq
    where
    not-invp<invq :
      ¬ (Rational.posInv p 0<p ℚOrder.< Rational.posInv q 0<q)
    not-invp<invq invp<invq =
      ℚOrder.≤→≯ p q p≤q q<p
      where
      invp-positive : 0ℚ ℚOrder.< Rational.posInv p 0<p
      invp-positive =
        Rational.posInv-positive {q = p} 0<p

      invq-positive : 0ℚ ℚOrder.< Rational.posInv q 0<q
      invq-positive =
        Rational.posInv-positive {q = q} 0<q

      invinvq<invinvp :
        Rational.posInv (Rational.posInv q 0<q) invq-positive
          ℚOrder.<
        Rational.posInv (Rational.posInv p 0<p) invp-positive
      invinvq<invinvp =
        Rational.posInv-reverse<
          {p = Rational.posInv p 0<p}
          {q = Rational.posInv q 0<q}
          invp-positive
          invq-positive
          invp<invq

      q<p : q ℚOrder.< p
      q<p =
        subst2
          ℚOrder._<_
          (Rational.posInv-involutive q 0<q)
          (Rational.posInv-involutive p 0<p)
          invinvq<invinvp

  scale-precision-cancel :
    (κ ε : ℚ⁺) →
    κ *⁺ (posInv⁺ κ *⁺ ε) ≡ ε
  scale-precision-cancel κ ε =
    sym (*⁺-assoc κ (posInv⁺ κ) ε) ∙
    cong (λ ρ → ρ *⁺ ε) (*⁺-posInv-right κ) ∙
    *⁺-identity-left ε

  rational-max-left-upper :
    (q r s : ℚ) (ε : ℚ⁺) →
    Closeℚ q ε r →
    ℚ.max q s ℚOrder.< radius ε ℚ.+ ℚ.max r s
  rational-max-left-upper q r s ε q∼r =
    Rational.max<
      {r = q}
      {s = s}
      {q = radius ε ℚ.+ ℚ.max r s}
      q<ε+max
      s<ε+max
    where
    ε+r≤ε+max : radius ε ℚ.+ r ℚOrder.≤ radius ε ℚ.+ ℚ.max r s
    ε+r≤ε+max =
      ℚOrder.≤-o+ r (ℚ.max r s) (radius ε) (ℚOrder.≤max r s)

    q<ε+r : q ℚOrder.< radius ε ℚ.+ r
    q<ε+r =
      Rational.diff<→right+< q (radius ε) r (q∼r .fst)

    q<ε+max : q ℚOrder.< radius ε ℚ.+ ℚ.max r s
    q<ε+max =
      Rational.<≤-trans
        {p = q}
        {q = radius ε ℚ.+ r}
        {r = radius ε ℚ.+ ℚ.max r s}
        q<ε+r
        ε+r≤ε+max

    s≤max : s ℚOrder.≤ ℚ.max r s
    s≤max =
      Rational.≤max-r r s

    max<ε+max : ℚ.max r s ℚOrder.< radius ε ℚ.+ ℚ.max r s
    max<ε+max =
      subst
        (ℚ.max r s ℚOrder.<_)
        (ℚ.+Comm (ℚ.max r s) (radius ε))
        (Rational.q<q+positive (ℚ.max r s) (radius ε) (ε .snd))

    s<ε+max : s ℚOrder.< radius ε ℚ.+ ℚ.max r s
    s<ε+max =
      Rational.≤<-trans
        {p = s}
        {q = ℚ.max r s}
        {r = radius ε ℚ.+ ℚ.max r s}
        s≤max
        max<ε+max

  rational-close-max-left :
    (q r s : ℚ) (ε : ℚ⁺) →
    Closeℚ q ε r →
    Closeℚ (ℚ.max q s) ε (ℚ.max r s)
  rational-close-max-left q r s ε q∼r =
    Rational.<+→diff<
      (ℚ.max q s)
      (radius ε)
      (ℚ.max r s)
      (rational-max-left-upper q r s ε q∼r) ,
    Rational.<+→diff<
      (ℚ.max r s)
      (radius ε)
      (ℚ.max q s)
      (rational-max-left-upper r q s ε
        (rational-close-sym q r ε q∼r))

  posInv-diff-path :
    (u v : ℚ) →
    (0<u : 0ℚ ℚOrder.< u) →
    (0<v : 0ℚ ℚOrder.< v) →
    Rational.posInv u 0<u ℚ.- Rational.posInv v 0<v ≡
    (v ℚ.- u) ℚ.·
    (Rational.posInv u 0<u ℚ.· Rational.posInv v 0<v)
  posInv-diff-path u v 0<u 0<v =
    cong₂
      (λ a b → a ℚ.- b)
      invu-path
      invv-path ∙
    SolverHelpers.inv-diff ℚCommRing u v invu invv
    where
    invu : ℚ
    invu = Rational.posInv u 0<u

    invv : ℚ
    invv = Rational.posInv v 0<v

    invu-path : invu ≡ (v ℚ.· invv) ℚ.· invu
    invu-path =
      sym (ℚ.·IdL invu) ∙
      cong (λ a → a ℚ.· invu) (sym (Rational.posInv-right v 0<v))

    invv-path : invv ≡ (u ℚ.· invu) ℚ.· invv
    invv-path =
      sym (ℚ.·IdL invv) ∙
      cong (λ a → a ℚ.· invv) (sym (Rational.posInv-right u 0<u))

  posInv-path :
    {q r : ℚ} →
    q ≡ r →
    (0<q : 0ℚ ℚOrder.< q) →
    (0<r : 0ℚ ℚOrder.< r) →
    Rational.posInv q 0<q ≡ Rational.posInv r 0<r
  posInv-path {q = q} q≡r 0<q 0<r =
    subst
      (λ r → (0<r : 0ℚ ℚOrder.< r) →
        Rational.posInv q 0<q ≡ Rational.posInv r 0<r)
      q≡r
      same-q
      0<r
    where
    same-q :
      (0<q' : 0ℚ ℚOrder.< q) →
      Rational.posInv q 0<q ≡ Rational.posInv q 0<q'
    same-q 0<q' =
      cong (Rational.posInv q)
        (ℚOrder.isProp< 0ℚ q 0<q 0<q')



record BoundedAwayPositiveᶜ (ε : ℚ⁺) (x : ℝᶜ) : Type₀ where
  constructor bounded-away-positiveᶜ
  field
    lowerᶜ : rational (radius ε) ≤ᶜ x


isPropBoundedAwayPositiveᶜ :
  (ε : ℚ⁺) (x : ℝᶜ) →
  isProp (BoundedAwayPositiveᶜ ε x)
isPropBoundedAwayPositiveᶜ ε x a b i .BoundedAwayPositiveᶜ.lowerᶜ =
  isProp≤ᶜ (rational (radius ε)) x
    (a .BoundedAwayPositiveᶜ.lowerᶜ)
    (b .BoundedAwayPositiveᶜ.lowerᶜ)
    i


private
  close-above-half-lower-bound :
    (ε : ℚ⁺) {x : ℝᶜ} →
    BoundedAwayPositiveᶜ ε x →
    (q : ℚ) (θ : ℚ⁺) →
    θ <⁺ half⁺ ε →
    x ∼[ θ ] rational q →
    radius (half⁺ ε) ℚOrder.≤ q
  close-above-half-lower-bound ε {x = x} x-bound q θ θ<η x∼q =
    ℚOrder.≤-+o-cancel (radius η) q (radius η) η+η≤q+η
    where
    η : ℚ⁺
    η = half⁺ ε

    x≤q+η :
      x ≤ᶜ rational (q ℚ.+ radius η)
    x≤q+η =
      close-rational-upper-bound x q θ η θ<η x∼q

    ε≤q+ηᶜ :
      rational (radius ε) ≤ᶜ rational (q ℚ.+ radius η)
    ε≤q+ηᶜ =
      ≤ᶜ-trans
        {x = rational (radius ε)}
        {y = x}
        {z = rational (q ℚ.+ radius η)}
        (x-bound .BoundedAwayPositiveᶜ.lowerᶜ)
        x≤q+η

    ε≤q+η :
      radius ε ℚOrder.≤ q ℚ.+ radius η
    ε≤q+η =
      rational≤ᶜ→≤ℚ ε≤q+ηᶜ

    η+η≤q+η :
      radius η ℚ.+ radius η ℚOrder.≤ q ℚ.+ radius η
    η+η≤q+η =
      subst
        (λ ρ → ρ ℚOrder.≤ q ℚ.+ radius η)
        (sym (cong radius (half⁺+half⁺≡ ε)))
        ε≤q+η


positive-rational-awayᶜ :
  (q : ℚ) →
  (0<q : 0ℚ ℚOrder.< q) →
  BoundedAwayPositiveᶜ (q , 0<q) (rational q)
positive-rational-awayᶜ q 0<q =
  bounded-away-positiveᶜ (≤ᶜ-refl (rational q))


boundedAwayPositiveᶜ→positiveSepᶜ :
  {ε : ℚ⁺} {x : ℝᶜ} →
  BoundedAwayPositiveᶜ ε x →
  PositiveSepᶜ x
boundedAwayPositiveᶜ→positiveSepᶜ {ε = ε} bound =
  ∣ ε , bound .BoundedAwayPositiveᶜ.lowerᶜ ∣₁


positiveSepᶜ→merelyBoundedAwayPositiveᶜ :
  (x : ℝᶜ) →
  PositiveSepᶜ x →
  ∥ Σ[ ε ∈ ℚ⁺ ] BoundedAwayPositiveᶜ ε x ∥₁
positiveSepᶜ→merelyBoundedAwayPositiveᶜ x =
  Prop.rec squash₁ step
  where
  step :
    Σ[ ε ∈ ℚ⁺ ] rational (radius ε) ≤ᶜ x →
    ∥ Σ[ ε ∈ ℚ⁺ ] BoundedAwayPositiveᶜ ε x ∥₁
  step (ε , ε≤x) =
    ∣ ε , bounded-away-positiveᶜ ε≤x ∣₁


boundedAwayPositiveᶜ-weaken :
  {δ ε : ℚ⁺} {x : ℝᶜ} →
  radius δ ℚOrder.≤ radius ε →
  BoundedAwayPositiveᶜ ε x →
  BoundedAwayPositiveᶜ δ x
boundedAwayPositiveᶜ-weaken {δ = δ} {ε = ε} {x = x} δ≤ε bound =
  bounded-away-positiveᶜ
    (≤ᶜ-trans
      {x = rational (radius δ)}
      {y = rational (radius ε)}
      {z = x}
      (≤ℚ→rational≤ᶜ
        {q = radius δ}
        {r = radius ε}
        δ≤ε)
      (bound .BoundedAwayPositiveᶜ.lowerᶜ))


rationalInv₊ᶜ :
  (q : ℚ) →
  0ℚ ℚOrder.< q →
  ℝᶜ
rationalInv₊ᶜ q 0<q =
  rational (Rational.posInv q 0<q)


rationalInv₊ᶜ-positive :
  (q : ℚ) →
  (0<q : 0ℚ ℚOrder.< q) →
  0ᶜ <ᶜ rationalInv₊ᶜ q 0<q
rationalInv₊ᶜ-positive q 0<q =
  <ℚ→<ᶜ
    {q = 0ℚ}
    {r = Rational.posInv q 0<q}
    (Rational.posInv-positive {q = q} 0<q)


rationalInv₊ᶜ-right :
  (q : ℚ) →
  (0<q : 0ℚ ℚOrder.< q) →
  rational q ·ᶜ rationalInv₊ᶜ q 0<q ≡ 1ᶜ
rationalInv₊ᶜ-right q 0<q =
  mulᶜ-rational-rational q (Rational.posInv q 0<q) ∙
  cong rational (Rational.posInv-right q 0<q)


rationalInv₊ᶜ-left :
  (q : ℚ) →
  (0<q : 0ℚ ℚOrder.< q) →
  rationalInv₊ᶜ q 0<q ·ᶜ rational q ≡ 1ᶜ
rationalInv₊ᶜ-left q 0<q =
  mulᶜ-rational-rational (Rational.posInv q 0<q) q ∙
  cong rational (Rational.posInv-left q 0<q)


rationalInv₊ᶜ-closed-bound-positive :
  (ε : ℚ⁺) (q : ℚ) →
  (0<q : 0ℚ ℚOrder.< q) →
  (ε≤q : radius ε ℚOrder.≤ q) →
  RationalClosedBoundᶜ (posInv⁺ ε) (Rational.posInv q 0<q)
rationalInv₊ᶜ-closed-bound-positive ε q 0<q ε≤q =
  rational-closed-boundᶜ upper lower-bound
  where
  invq : ℚ
  invq =
    Rational.posInv q 0<q

  invε : ℚ
  invε =
    radius (posInv⁺ ε)

  upper : invq ℚOrder.≤ invε
  upper =
    posInv-reverse≤
      {p = radius ε}
      {q = q}
      (ε .snd)
      0<q
      ε≤q

  invq-positive : 0ℚ ℚOrder.< invq
  invq-positive =
    Rational.posInv-positive {q = q} 0<q

  -invq<0 : ℚ.- invq ℚOrder.< 0ℚ
  -invq<0 =
    subst
      (ℚ.- invq ℚOrder.<_)
      Rational.neg-zero
      (Rational.negReverse< {p = 0ℚ} {q = invq} invq-positive)

  0≤invε : 0ℚ ℚOrder.≤ invε
  0≤invε =
    Rational.<→≤ {p = 0ℚ} {q = invε}
      (Rational.posInv-positive {q = radius ε} (ε .snd))

  lower-bound : ℚ.- invq ℚOrder.≤ invε
  lower-bound =
    Rational.≤-trans
      {p = ℚ.- invq}
      {q = 0ℚ}
      {r = invε}
      (Rational.<→≤ {p = ℚ.- invq} {q = 0ℚ} -invq<0)
      0≤invε


rationalInv₊ᶜ-closed-bound :
  (ε : ℚ⁺) (q : ℚ) →
  (ε≤q : radius ε ℚOrder.≤ q) →
  RationalClosedBoundᶜ
    (posInv⁺ ε)
    (Rational.posInv q
      (Rational.<≤-trans
        {p = 0ℚ}
        {q = radius ε}
        {r = q}
        (ε .snd)
        ε≤q))
rationalInv₊ᶜ-closed-bound ε q ε≤q =
  rationalInv₊ᶜ-closed-bound-positive ε q 0<q ε≤q
  where
  0<q : 0ℚ ℚOrder.< q
  0<q =
    Rational.<≤-trans
      {p = 0ℚ}
      {q = radius ε}
      {r = q}
      (ε .snd)
      ε≤q


rationalInv₊ᶜ-bound :
  (ε : ℚ⁺) (q : ℚ) →
  (ε≤q : radius ε ℚOrder.≤ q) →
  BoundedByᶜ (posInv⁺ ε)
    (rationalInv₊ᶜ q
      (Rational.<≤-trans
        {p = 0ℚ}
        {q = radius ε}
        {r = q}
        (ε .snd)
        ε≤q))
rationalInv₊ᶜ-bound ε q ε≤q =
  rational-closed-bound→boundedᶜ
    (posInv⁺ ε)
    (Rational.posInv q 0<q)
    (rationalInv₊ᶜ-closed-bound ε q ε≤q)
  where
  0<q : 0ℚ ℚOrder.< q
  0<q =
    Rational.<≤-trans
      {p = 0ℚ}
      {q = radius ε}
      {r = q}
      (ε .snd)
      ε≤q


reciprocalLipschitzBase⁺ : ℚ⁺ → ℚ⁺
reciprocalLipschitzBase⁺ ε =
  radius (posInv⁺ ε) ℚ.+ 1ℚ ,
  positive-sum
    {p = radius (posInv⁺ ε)}
    {q = 1ℚ}
    (posInv⁺ ε .snd)
    Rational.0<1


reciprocalLipschitzBound⁺ : ℚ⁺ → ℚ⁺
reciprocalLipschitzBound⁺ ε =
  reciprocalLipschitzBase⁺ ε *⁺ reciprocalLipschitzBase⁺ ε


clampLower : ℚ⁺ → ℚ → ℚ
clampLower ε q =
  ℚ.max q (radius ε)


clampLower-bound :
  (ε : ℚ⁺) (q : ℚ) →
  radius ε ℚOrder.≤ clampLower ε q
clampLower-bound ε q =
  Rational.≤max-r q (radius ε)


clampLower-positive :
  (ε : ℚ⁺) (q : ℚ) →
  0ℚ ℚOrder.< clampLower ε q
clampLower-positive ε q =
  Rational.<≤-trans
    {p = 0ℚ}
    {q = radius ε}
    {r = clampLower ε q}
    (ε .snd)
    (clampLower-bound ε q)


clampLower-stable :
  (ε : ℚ⁺) (q : ℚ) →
  radius ε ℚOrder.≤ q →
  clampLower ε q ≡ q
clampLower-stable ε q ε≤q =
  ℚ.maxComm q (radius ε) ∙
  ℚOrder.≤→max (radius ε) q ε≤q


clampedRationalInv₊ᶜ :
  ℚ⁺ →
  ℚ →
  ℝᶜ
clampedRationalInv₊ᶜ ε q =
  rationalInv₊ᶜ (clampLower ε q) (clampLower-positive ε q)


clampedRationalInv₊ᶜ-stable :
  (ε : ℚ⁺) (q : ℚ) →
  (0<q : 0ℚ ℚOrder.< q) →
  radius ε ℚOrder.≤ q →
  clampedRationalInv₊ᶜ ε q ≡ rationalInv₊ᶜ q 0<q
clampedRationalInv₊ᶜ-stable ε q 0<q ε≤q =
  cong rational
    (posInv-path
      (clampLower-stable ε q ε≤q)
      (clampLower-positive ε q)
      0<q)


private
  reciprocalBound-upper :
    (ε : ℚ⁺) (u : ℚ) →
    (0<u : 0ℚ ℚOrder.< u) →
    radius ε ℚOrder.≤ u →
    Rational.posInv u 0<u ℚOrder.< radius (reciprocalLipschitzBase⁺ ε)
  reciprocalBound-upper ε u 0<u ε≤u =
    Rational.≤<-trans
      {p = Rational.posInv u 0<u}
      {q = radius (posInv⁺ ε)}
      {r = radius (reciprocalLipschitzBase⁺ ε)}
      invu≤invε
      invε<base
    where
    invu≤invε :
      Rational.posInv u 0<u ℚOrder.≤ radius (posInv⁺ ε)
    invu≤invε =
      posInv-reverse≤
        {p = radius ε}
        {q = u}
        (ε .snd)
        0<u
        ε≤u

    invε<base :
      radius (posInv⁺ ε) ℚOrder.< radius (reciprocalLipschitzBase⁺ ε)
    invε<base =
      Rational.q<q+positive
        (radius (posInv⁺ ε))
        1ℚ
        Rational.0<1

  reciprocalBound-closed :
    (ε : ℚ⁺) (u : ℚ) →
    (0<u : 0ℚ ℚOrder.< u) →
    radius ε ℚOrder.≤ u →
    RationalClosedBoundᶜ
      (reciprocalLipschitzBase⁺ ε)
      (Rational.posInv u 0<u)
  reciprocalBound-closed ε u 0<u ε≤u =
    rational-closed-boundᶜ upper lower-bound
    where
    invu : ℚ
    invu =
      Rational.posInv u 0<u

    upper :
      invu ℚOrder.≤ radius (reciprocalLipschitzBase⁺ ε)
    upper =
      Rational.<→≤
        {p = invu}
        {q = radius (reciprocalLipschitzBase⁺ ε)}
        (reciprocalBound-upper ε u 0<u ε≤u)

    invu-positive : 0ℚ ℚOrder.< invu
    invu-positive =
      Rational.posInv-positive {q = u} 0<u

    -invu<0 : ℚ.- invu ℚOrder.< 0ℚ
    -invu<0 =
      subst
        (ℚ.- invu ℚOrder.<_)
        Rational.neg-zero
        (Rational.negReverse< {p = 0ℚ} {q = invu} invu-positive)

    0<base : 0ℚ ℚOrder.< radius (reciprocalLipschitzBase⁺ ε)
    0<base =
      reciprocalLipschitzBase⁺ ε .snd

    lower-bound :
      ℚ.- invu ℚOrder.≤ radius (reciprocalLipschitzBase⁺ ε)
    lower-bound =
      Rational.<→≤
        {p = ℚ.- invu}
        {q = radius (reciprocalLipschitzBase⁺ ε)}
        (Rational.<≤-trans
          {p = ℚ.- invu}
          {q = 0ℚ}
          {r = radius (reciprocalLipschitzBase⁺ ε)}
          -invu<0
          (Rational.<→≤
            {p = 0ℚ}
            {q = radius (reciprocalLipschitzBase⁺ ε)}
            0<base))

  reciprocalProduct-bound :
    (ε : ℚ⁺) (u v : ℚ) →
    (0<u : 0ℚ ℚOrder.< u) →
    (0<v : 0ℚ ℚOrder.< v) →
    radius ε ℚOrder.≤ u →
    radius ε ℚOrder.≤ v →
    Rational.posInv u 0<u ℚ.· Rational.posInv v 0<v
      ℚOrder.<
    radius (reciprocalLipschitzBound⁺ ε)
  reciprocalProduct-bound ε u v 0<u 0<v ε≤u ε≤v =
    Rational.mul-mono-positive-<
      {a = Rational.posInv u 0<u}
      {b = Rational.posInv v 0<v}
      {c = radius (reciprocalLipschitzBase⁺ ε)}
      {d = radius (reciprocalLipschitzBase⁺ ε)}
      (reciprocalBound-upper ε u 0<u ε≤u)
      (reciprocalBound-upper ε v 0<v ε≤v)
      (Rational.posInv-positive {q = v} 0<v)
      (reciprocalLipschitzBase⁺ ε .snd)

  reciprocal-diff-upper :
    (ε δ : ℚ⁺) (u v : ℚ) →
    (0<u : 0ℚ ℚOrder.< u) →
    (0<v : 0ℚ ℚOrder.< v) →
    radius ε ℚOrder.≤ u →
    radius ε ℚOrder.≤ v →
    v ℚ.- u ℚOrder.< radius δ →
    Rational.posInv u 0<u ℚ.- Rational.posInv v 0<v
      ℚOrder.<
    radius (reciprocalLipschitzBound⁺ ε *⁺ δ)
  reciprocal-diff-upper ε δ u v 0<u 0<v ε≤u ε≤v v-u<δ =
    subst2
      ℚOrder._<_
      (sym (posInv-diff-path u v 0<u 0<v))
      (SolverHelpers.positive-product-bound ℚCommRing
        (radius δ)
        (radius (reciprocalLipschitzBound⁺ ε)))
      product<
    where
    invProduct : ℚ
    invProduct =
      Rational.posInv u 0<u ℚ.· Rational.posInv v 0<v

    invProduct-positive : 0ℚ ℚOrder.< invProduct
    invProduct-positive =
      Rational.mul-positive
        {a = Rational.posInv u 0<u}
        {b = Rational.posInv v 0<v}
        (Rational.posInv-positive {q = u} 0<u)
        (Rational.posInv-positive {q = v} 0<v)

    invProduct<bound :
      invProduct ℚOrder.< radius (reciprocalLipschitzBound⁺ ε)
    invProduct<bound =
      reciprocalProduct-bound ε u v 0<u 0<v ε≤u ε≤v

    product< :
      (v ℚ.- u) ℚ.· invProduct
        ℚOrder.<
      radius δ ℚ.· radius (reciprocalLipschitzBound⁺ ε)
    product< =
      Rational.mul-mono-positive-<
        {a = v ℚ.- u}
        {b = invProduct}
        {c = radius δ}
        {d = radius (reciprocalLipschitzBound⁺ ε)}
        v-u<δ
        invProduct<bound
        invProduct-positive
        (δ .snd)

  clampedRationalInv-close :
    (ε : ℚ⁺) (p q : ℚ) (δ : ℚ⁺) →
    Closeℚ p δ q →
    Closeℚ
      (Rational.posInv
        (clampLower ε p)
        (clampLower-positive ε p))
      (reciprocalLipschitzBound⁺ ε *⁺ δ)
      (Rational.posInv
        (clampLower ε q)
        (clampLower-positive ε q))
  clampedRationalInv-close ε p q δ p∼q =
    reciprocal-diff-upper
      ε δ u v 0<u 0<v ε≤u ε≤v v-u<δ ,
    reciprocal-diff-upper
      ε δ v u 0<v 0<u ε≤v ε≤u u-v<δ
    where
    u v : ℚ
    u = clampLower ε p
    v = clampLower ε q

    0<u : 0ℚ ℚOrder.< u
    0<u = clampLower-positive ε p

    0<v : 0ℚ ℚOrder.< v
    0<v = clampLower-positive ε q

    ε≤u : radius ε ℚOrder.≤ u
    ε≤u = clampLower-bound ε p

    ε≤v : radius ε ℚOrder.≤ v
    ε≤v = clampLower-bound ε q

    u∼v : Closeℚ u δ v
    u∼v =
      rational-close-max-left p q (radius ε) δ p∼q

    u-v<δ : u ℚ.- v ℚOrder.< radius δ
    u-v<δ = u∼v .fst

    v-u<δ : v ℚ.- u ℚOrder.< radius δ
    v-u<δ = u∼v .snd


clampedRationalInv₊ᶜ-lipschitz :
  (ε : ℚ⁺) →
  IsRationalLipschitzWithᶜ
    (reciprocalLipschitzBound⁺ ε)
    (clampedRationalInv₊ᶜ ε)
clampedRationalInv₊ᶜ-lipschitz ε p q δ p∼q =
  rational-rational-close
    (Rational.posInv
      (clampLower ε p)
      (clampLower-positive ε p))
    (Rational.posInv
      (clampLower ε q)
      (clampLower-positive ε q))
    (reciprocalLipschitzBound⁺ ε *⁺ δ)
    (clampedRationalInv-close ε p q δ p∼q)


clampedRationalInv₊ᶜ-bound :
  (ε : ℚ⁺) (q : ℚ) →
  BoundedByᶜ
    (reciprocalLipschitzBase⁺ ε)
    (clampedRationalInv₊ᶜ ε q)
clampedRationalInv₊ᶜ-bound ε q =
  rational-closed-bound→boundedᶜ
    (reciprocalLipschitzBase⁺ ε)
    (Rational.posInv
      (clampLower ε q)
      (clampLower-positive ε q))
    (reciprocalBound-closed
      ε
      (clampLower ε q)
      (clampLower-positive ε q)
      (clampLower-bound ε q))


boundedReciprocalᶜ :
  ℚ⁺ →
  ℝᶜ → ℝᶜ
boundedReciprocalᶜ ε =
  extendRationalLipschitzWithᶜ
    (reciprocalLipschitzBound⁺ ε)
    (clampedRationalInv₊ᶜ ε)
    (clampedRationalInv₊ᶜ-lipschitz ε)


boundedReciprocalᶜ-rational :
  (ε : ℚ⁺) (q : ℚ) →
  boundedReciprocalᶜ ε (rational q) ≡ clampedRationalInv₊ᶜ ε q
boundedReciprocalᶜ-rational ε q =
  extendRationalLipschitzWithᶜ-rational
    (reciprocalLipschitzBound⁺ ε)
    (clampedRationalInv₊ᶜ ε)
    (clampedRationalInv₊ᶜ-lipschitz ε)
    q


boundedReciprocalᶜ-rational-stable :
  (ε : ℚ⁺) (q : ℚ) →
  (0<q : 0ℚ ℚOrder.< q) →
  radius ε ℚOrder.≤ q →
  boundedReciprocalᶜ ε (rational q) ≡ rationalInv₊ᶜ q 0<q
boundedReciprocalᶜ-rational-stable ε q 0<q ε≤q =
  boundedReciprocalᶜ-rational ε q ∙
  clampedRationalInv₊ᶜ-stable ε q 0<q ε≤q


boundedReciprocalᶜ-rational-right :
  (ε : ℚ⁺) (q : ℚ) →
  (0<q : 0ℚ ℚOrder.< q) →
  (ε≤q : radius ε ℚOrder.≤ q) →
  rational q ·ᶜ boundedReciprocalᶜ ε (rational q) ≡ 1ᶜ
boundedReciprocalᶜ-rational-right ε q 0<q ε≤q =
  cong
    (rational q ·ᶜ_)
    (boundedReciprocalᶜ-rational-stable ε q 0<q ε≤q) ∙
  rationalInv₊ᶜ-right q 0<q


boundedReciprocalᶜ-rational-left :
  (ε : ℚ⁺) (q : ℚ) →
  (0<q : 0ℚ ℚOrder.< q) →
  (ε≤q : radius ε ℚOrder.≤ q) →
  boundedReciprocalᶜ ε (rational q) ·ᶜ rational q ≡ 1ᶜ
boundedReciprocalᶜ-rational-left ε q 0<q ε≤q =
  cong
    (_·ᶜ rational q)
    (boundedReciprocalᶜ-rational-stable ε q 0<q ε≤q) ∙
  rationalInv₊ᶜ-left q 0<q


boundedReciprocalᶜ-lipschitz :
  (ε : ℚ⁺) →
  IsLipschitz (boundedReciprocalᶜ ε)
boundedReciprocalᶜ-lipschitz ε =
  extendRationalLipschitzWithᶜ-lipschitz
    (reciprocalLipschitzBound⁺ ε)
    (clampedRationalInv₊ᶜ ε)
    (clampedRationalInv₊ᶜ-lipschitz ε)


boundedReciprocalᶜ-continuous :
  (ε : ℚ⁺) →
  IsContinuous (boundedReciprocalᶜ ε)
boundedReciprocalᶜ-continuous ε =
  extendRationalLipschitzWithᶜ-continuous
    (reciprocalLipschitzBound⁺ ε)
    (clampedRationalInv₊ᶜ ε)
    (clampedRationalInv₊ᶜ-lipschitz ε)


boundedReciprocalᶜ-bound :
  (ε : ℚ⁺) (x : ℝᶜ) →
  BoundedByᶜ
    (reciprocalLipschitzBase⁺ ε)
    (boundedReciprocalᶜ ε x)
boundedReciprocalᶜ-bound ε x =
  bounded-byᶜ upper-bound lower-bound
  where
  f : ℝᶜ → ℝᶜ
  f = boundedReciprocalᶜ ε

  one : ℚ⁺
  one = 1⁺

  δ : ℚ⁺
  δ = half⁺ one

  δ<one : δ <⁺ one
  δ<one =
    half< one

  θ : ℚ⁺
  θ =
    fst (boundedReciprocalᶜ-continuous ε δ)

  f-close :
    {y z : ℝᶜ} →
    y ∼[ θ ] z →
    f y ∼[ δ ] f z
  f-close =
    snd (boundedReciprocalᶜ-continuous ε δ)

  upper-step :
    Σ[ q ∈ ℚ ] x ∼[ θ ] rational q →
    f x ≤ᶜ rational (radius (reciprocalLipschitzBase⁺ ε))
  upper-step (q , x∼q) =
    ≤ᶜ-trans
      {x = f x}
      {y = rational (invu ℚ.+ 1ℚ)}
      {z = rational (radius (reciprocalLipschitzBase⁺ ε))}
      close-upper
      invu+1≤baseᶜ
    where
    u : ℚ
    u = clampLower ε q

    0<u : 0ℚ ℚOrder.< u
    0<u = clampLower-positive ε q

    ε≤u : radius ε ℚOrder.≤ u
    ε≤u = clampLower-bound ε q

    invu : ℚ
    invu = Rational.posInv u 0<u

    fx∼fu : f x ∼[ δ ] rational invu
    fx∼fu =
      subst
        (λ y → f x ∼[ δ ] y)
        (boundedReciprocalᶜ-rational ε q)
        (f-close x∼q)

    close-upper :
      f x ≤ᶜ rational (invu ℚ.+ 1ℚ)
    close-upper =
      close-rational-upper-bound (f x) invu δ one δ<one fx∼fu

    invu≤invε :
      invu ℚOrder.≤ radius (posInv⁺ ε)
    invu≤invε =
      posInv-reverse≤
        {p = radius ε}
        {q = u}
        (ε .snd)
        0<u
        ε≤u

    invu+1≤base :
      invu ℚ.+ 1ℚ ℚOrder.≤ radius (reciprocalLipschitzBase⁺ ε)
    invu+1≤base =
      ℚOrder.≤Monotone+
        invu
        (radius (posInv⁺ ε))
        1ℚ
        1ℚ
        invu≤invε
        (Rational.≤-refl 1ℚ)

    invu+1≤baseᶜ :
      rational (invu ℚ.+ 1ℚ) ≤ᶜ
      rational (radius (reciprocalLipschitzBase⁺ ε))
    invu+1≤baseᶜ =
      ≤ℚ→rational≤ᶜ
        {q = invu ℚ.+ 1ℚ}
        {r = radius (reciprocalLipschitzBase⁺ ε)}
        invu+1≤base

  lower-step :
    Σ[ q ∈ ℚ ] x ∼[ θ ] rational q →
    (-ᶜ f x) ≤ᶜ rational (radius (reciprocalLipschitzBase⁺ ε))
  lower-step (q , x∼q) =
    ≤ᶜ-trans
      {x = -ᶜ f x}
      {y = rational ((ℚ.- invu) ℚ.+ 1ℚ)}
      {z = rational (radius (reciprocalLipschitzBase⁺ ε))}
      close-upper
      -invu+1≤baseᶜ
    where
    u : ℚ
    u = clampLower ε q

    0<u : 0ℚ ℚOrder.< u
    0<u = clampLower-positive ε q

    ε≤u : radius ε ℚOrder.≤ u
    ε≤u = clampLower-bound ε q

    invu : ℚ
    invu = Rational.posInv u 0<u

    fx∼fu : f x ∼[ δ ] rational invu
    fx∼fu =
      subst
        (λ y → f x ∼[ δ ] y)
        (boundedReciprocalᶜ-rational ε q)
        (f-close x∼q)

    -fx∼-fu : (-ᶜ f x) ∼[ δ ] rational (ℚ.- invu)
    -fx∼-fu =
      neg-close fx∼fu

    close-upper :
      (-ᶜ f x) ≤ᶜ rational ((ℚ.- invu) ℚ.+ 1ℚ)
    close-upper =
      close-rational-upper-bound
        (-ᶜ f x)
        (ℚ.- invu)
        δ
        one
        δ<one
        -fx∼-fu

    invu-positive : 0ℚ ℚOrder.< invu
    invu-positive =
      Rational.posInv-positive {q = u} 0<u

    -invu<0 : ℚ.- invu ℚOrder.< 0ℚ
    -invu<0 =
      subst
        (ℚ.- invu ℚOrder.<_)
        Rational.neg-zero
        (Rational.negReverse< {p = 0ℚ} {q = invu} invu-positive)

    0≤invε : 0ℚ ℚOrder.≤ radius (posInv⁺ ε)
    0≤invε =
      Rational.<→≤
        {p = 0ℚ}
        {q = radius (posInv⁺ ε)}
        (posInv⁺ ε .snd)

    -invu≤invε : ℚ.- invu ℚOrder.≤ radius (posInv⁺ ε)
    -invu≤invε =
      Rational.≤-trans
        {p = ℚ.- invu}
        {q = 0ℚ}
        {r = radius (posInv⁺ ε)}
        (Rational.<→≤ {p = ℚ.- invu} {q = 0ℚ} -invu<0)
        0≤invε

    -invu+1≤base :
      (ℚ.- invu) ℚ.+ 1ℚ ℚOrder.≤
      radius (reciprocalLipschitzBase⁺ ε)
    -invu+1≤base =
      ℚOrder.≤Monotone+
        (ℚ.- invu)
        (radius (posInv⁺ ε))
        1ℚ
        1ℚ
        -invu≤invε
        (Rational.≤-refl 1ℚ)

    -invu+1≤baseᶜ :
      rational ((ℚ.- invu) ℚ.+ 1ℚ) ≤ᶜ
      rational (radius (reciprocalLipschitzBase⁺ ε))
    -invu+1≤baseᶜ =
      ≤ℚ→rational≤ᶜ
        {q = (ℚ.- invu) ℚ.+ 1ℚ}
        {r = radius (reciprocalLipschitzBase⁺ ε)}
        -invu+1≤base

  upper-bound : f x ≤ᶜ rational (radius (reciprocalLipschitzBase⁺ ε))
  upper-bound =
    Prop.rec
      (isProp≤ᶜ (f x) (rational (radius (reciprocalLipschitzBase⁺ ε))))
      upper-step
      (rational-approximation x θ)

  lower-bound :
    (-ᶜ f x) ≤ᶜ rational (radius (reciprocalLipschitzBase⁺ ε))
  lower-bound =
    Prop.rec
      (isProp≤ᶜ
        (-ᶜ f x)
        (rational (radius (reciprocalLipschitzBase⁺ ε))))
      lower-step
      (rational-approximation x θ)


boundedAwayReciprocalᶜ :
  (ε : ℚ⁺) (x : ℝᶜ) →
  BoundedAwayPositiveᶜ ε x →
  ℝᶜ
boundedAwayReciprocalᶜ ε x _ =
  boundedReciprocalᶜ (half⁺ ε) x


boundedAwayReciprocalᶜ-bound :
  (ε : ℚ⁺) (x : ℝᶜ) →
  (x-bound : BoundedAwayPositiveᶜ ε x) →
  BoundedByᶜ
    (reciprocalLipschitzBase⁺ (half⁺ ε))
    (boundedAwayReciprocalᶜ ε x x-bound)
boundedAwayReciprocalᶜ-bound ε x _ =
  boundedReciprocalᶜ-bound (half⁺ ε) x


boundedAwayReciprocalᶜ-right :
  (ε : ℚ⁺) (x : ℝᶜ) →
  (x-bound : BoundedAwayPositiveᶜ ε x) →
  x ·ᶜ boundedAwayReciprocalᶜ ε x x-bound ≡ 1ᶜ
boundedAwayReciprocalᶜ-right ε x x-bound =
  path (x ·ᶜ f x) 1ᶜ closeAt
  where
  lowerBound : ℚ⁺
  lowerBound = half⁺ ε

  f : ℝᶜ → ℝᶜ
  f = boundedReciprocalᶜ lowerBound

  closeAt :
    (μ : ℚ⁺) →
    (x ·ᶜ f x) ∼[ μ ] 1ᶜ
  closeAt μ =
    Prop.rec squash stepBound (merely-boundedᶜ x)
    where
    α : ℚ⁺
    α = quarter⁺ μ

    B : ℚ⁺
    B = reciprocalLipschitzBase⁺ lowerBound

    L : ℚ⁺
    L = reciprocalLipschitzBound⁺ lowerBound

    stepBound :
      Σ[ κ ∈ ℚ⁺ ] BoundedByᶜ κ x →
      (x ·ᶜ f x) ∼[ μ ] 1ᶜ
    stepBound (κ , xκ) =
      Prop.rec squash stepApprox (rational-approximation x θ)
      where
      ηA θA θB θ : ℚ⁺
      ηA = posInv⁺ κ *⁺ α
      θA = posInv⁺ L *⁺ ηA
      θB = posInv⁺ B *⁺ α
      θ = half⁺ (min⁺ θA (min⁺ θB lowerBound))

      θ<θA : θ <⁺ θA
      θ<θA =
        half-min⁺<left θA (min⁺ θB lowerBound)

      θ<θB : θ <⁺ θB
      θ<θB =
        Rational.<≤-trans
          {p = radius θ}
          {q = radius (min⁺ θB lowerBound)}
          {r = radius θB}
          (half-min⁺<right θA (min⁺ θB lowerBound))
          (min⁺≤left θB lowerBound)

      θ<lowerBound : θ <⁺ lowerBound
      θ<lowerBound =
        Rational.<≤-trans
          {p = radius θ}
          {q = radius (min⁺ θB lowerBound)}
          {r = radius lowerBound}
          (half-min⁺<right θA (min⁺ θB lowerBound))
          (min⁺≤right θB lowerBound)

      stepApprox :
        Σ[ q ∈ ℚ ] x ∼[ θ ] rational q →
        (x ·ᶜ f x) ∼[ μ ] 1ᶜ
      stepApprox (q , x∼q) =
        close-mono
          {ε = α +⁺ α}
          {δ = μ}
          (quarter-sum< μ)
          (subst
            (λ y → (x ·ᶜ f x) ∼[ α +⁺ α ] y)
            q-law
            (close-triangle termA termB))
        where
        fq : ℝᶜ
        fq = f (rational q)

        x∼qθA : x ∼[ θA ] rational q
        x∼qθA =
          close-mono θ<θA x∼q

        x∼qθB : x ∼[ θB ] rational q
        x∼qθB =
          close-mono θ<θB x∼q

        fx∼fq : f x ∼[ ηA ] fq
        fx∼fq =
          snd (boundedReciprocalᶜ-lipschitz lowerBound) ηA x∼qθA

        termA-raw :
          boundedMulᶜ κ x xκ (f x) ∼[ κ *⁺ ηA ]
          boundedMulᶜ κ x xκ fq
        termA-raw =
          boundedMulᶜ-close κ x xκ fx∼fq

        termA-scaled :
          boundedMulᶜ κ x xκ (f x) ∼[ α ]
          boundedMulᶜ κ x xκ fq
        termA-scaled =
          subst
            (λ ρ →
              boundedMulᶜ κ x xκ (f x) ∼[ ρ ]
              boundedMulᶜ κ x xκ fq)
            (scale-precision-cancel κ α)
            termA-raw

        termA :
          (x ·ᶜ f x) ∼[ α ] (x ·ᶜ fq)
        termA =
          subst2
            (λ u v → u ∼[ α ] v)
            (sym (mulᶜ-bound κ x xκ (f x)))
            (sym (mulᶜ-bound κ x xκ fq))
            termA-scaled

        fq-bound : BoundedByᶜ B fq
        fq-bound =
          boundedReciprocalᶜ-bound lowerBound (rational q)

        termB-raw :
          boundedMulᶜ B fq fq-bound x ∼[ B *⁺ θB ]
          boundedMulᶜ B fq fq-bound (rational q)
        termB-raw =
          boundedMulᶜ-close B fq fq-bound x∼qθB

        termB-scaled :
          boundedMulᶜ B fq fq-bound x ∼[ α ]
          boundedMulᶜ B fq fq-bound (rational q)
        termB-scaled =
          subst
            (λ ρ →
              boundedMulᶜ B fq fq-bound x ∼[ ρ ]
              boundedMulᶜ B fq fq-bound (rational q))
            (scale-precision-cancel B α)
            termB-raw

        termB-global :
          (fq ·ᶜ x) ∼[ α ] (fq ·ᶜ rational q)
        termB-global =
          subst2
            (λ u v → u ∼[ α ] v)
            (sym (mulᶜ-bound B fq fq-bound x))
            (sym (mulᶜ-bound B fq fq-bound (rational q)))
            termB-scaled

        termB :
          (x ·ᶜ fq) ∼[ α ] (rational q ·ᶜ fq)
        termB =
          subst2
            (λ u v → u ∼[ α ] v)
            (sym (mulᶜ-comm x fq))
            (sym (mulᶜ-comm (rational q) fq))
            termB-global

        lower≤q : radius lowerBound ℚOrder.≤ q
        lower≤q =
          close-above-half-lower-bound ε x-bound q θ θ<lowerBound x∼q

        0<q : 0ℚ ℚOrder.< q
        0<q =
          Rational.<≤-trans
            {p = 0ℚ}
            {q = radius lowerBound}
            {r = q}
            (lowerBound .snd)
            lower≤q

        q-law :
          rational q ·ᶜ fq ≡ 1ᶜ
        q-law =
          boundedReciprocalᶜ-rational-right lowerBound q 0<q lower≤q


boundedAwayReciprocalᶜ-left :
  (ε : ℚ⁺) (x : ℝᶜ) →
  (x-bound : BoundedAwayPositiveᶜ ε x) →
  boundedAwayReciprocalᶜ ε x x-bound ·ᶜ x ≡ 1ᶜ
boundedAwayReciprocalᶜ-left ε x x-bound =
  mulᶜ-comm (boundedAwayReciprocalᶜ ε x x-bound) x ∙
  boundedAwayReciprocalᶜ-right ε x x-bound


boundedAwayReciprocalᶜ-rational-right :
  (ε : ℚ⁺) (q : ℚ) →
  (0<q : 0ℚ ℚOrder.< q) →
  (ε≤q : radius ε ℚOrder.≤ q) →
  rational q ·ᶜ
    boundedAwayReciprocalᶜ ε (rational q)
      (bounded-away-positiveᶜ
        (≤ℚ→rational≤ᶜ
          {q = radius ε}
          {r = q}
          ε≤q))
    ≡ 1ᶜ
boundedAwayReciprocalᶜ-rational-right ε q 0<q ε≤q =
  boundedReciprocalᶜ-rational-right
    (half⁺ ε)
    q
    0<q
    (Rational.<→≤
      {p = radius (half⁺ ε)}
      {q = q}
      (Rational.<≤-trans
        {p = radius (half⁺ ε)}
        {q = radius ε}
        {r = q}
        (half< ε)
        ε≤q))


boundedAwayReciprocalᶜ-rational-left :
  (ε : ℚ⁺) (q : ℚ) →
  (0<q : 0ℚ ℚOrder.< q) →
  (ε≤q : radius ε ℚOrder.≤ q) →
  boundedAwayReciprocalᶜ ε (rational q)
    (bounded-away-positiveᶜ
      (≤ℚ→rational≤ᶜ
        {q = radius ε}
        {r = q}
        ε≤q))
    ·ᶜ rational q
    ≡ 1ᶜ
boundedAwayReciprocalᶜ-rational-left ε q 0<q ε≤q =
  boundedReciprocalᶜ-rational-left
    (half⁺ ε)
    q
    0<q
    (Rational.<→≤
      {p = radius (half⁺ ε)}
      {q = q}
      (Rational.<≤-trans
        {p = radius (half⁺ ε)}
        {q = radius ε}
        {r = q}
        (half< ε)
        ε≤q))
