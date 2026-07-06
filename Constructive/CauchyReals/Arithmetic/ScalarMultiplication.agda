{-

Rational scalar multiplication infrastructure for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Arithmetic.ScalarMultiplication where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.CauchyReals.Arithmetic.Addition
open import Constructive.CauchyReals.Arithmetic.Base
open import Constructive.CauchyReals.Arithmetic.Negation
open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Closeness
open import Constructive.CauchyReals.Continuity
open import Constructive.CauchyReals.Extension
open import Constructive.CauchyReals.Lipschitz.Base
open import Constructive.CauchyReals.Lipschitz.RationalExtension
open import Constructive.Data.PositiveRationals
open import Constructive.Data.Rationals.Closeness
open import Constructive.CauchyReals.Recursion
import Constructive.Data.Rationals as Rational


private
  pointwise-sum-continuous :
    {f g : ℝᶜ → ℝᶜ} →
    IsContinuous f →
    IsContinuous g →
    IsContinuous (λ x → f x +ᶜ g x)
  pointwise-sum-continuous {f = f} {g = g} f-cont g-cont ε =
    δ , closeAt
    where
    α : ℚ⁺
    α = half⁺ ε

    μf μg : ℚ⁺
    μf = fst (f-cont α)
    μg = fst (g-cont α)

    μ : ℚ⁺
    μ = min⁺ μf μg

    δ : ℚ⁺
    δ = half⁺ μ

    δ<μf : δ <⁺ μf
    δ<μf =
      half-min⁺<left μf μg

    δ<μg : δ <⁺ μg
    δ<μg =
      half-min⁺<right μf μg

    closeAt :
      {x y : ℝᶜ} →
      x ∼[ δ ] y →
      (f x +ᶜ g x) ∼[ ε ] (f y +ᶜ g y)
    closeAt {x = x} {y = y} x∼y =
      subst
        (λ ρ → (f x +ᶜ g x) ∼[ ρ ] (f y +ᶜ g y))
        (half⁺+half⁺≡ ε)
        (add-close
          (snd (f-cont α) (close-mono δ<μf x∼y))
          (snd (g-cont α) (close-mono δ<μg x∼y)))

  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    scale-diff-positive :
      (a p q : 𝓡 .fst) →
      (a · p) - (a · q) ≡ a · (p - q)
    scale-diff-positive _ _ _ = solve! 𝓡

    scale-diff-negative :
      (a p q : 𝓡 .fst) →
      (a · p) - (a · q) ≡ (- a) · (q - p)
    scale-diff-negative _ _ _ = solve! 𝓡

    scale-diff-zero :
      (p q : 𝓡 .fst) →
      (0r · p) - (0r · q) ≡ 0r
    scale-diff-zero _ _ = solve! 𝓡

    scale-zero-right :
      (a : 𝓡 .fst) →
      a · 0r ≡ 0r
    scale-zero-right _ = solve! 𝓡

    scale-neg-right :
      (a q : 𝓡 .fst) →
      a · (- q) ≡ - (a · q)
    scale-neg-right _ _ = solve! 𝓡

    scale-neg-left :
      (a q : 𝓡 .fst) →
      (- a) · q ≡ - (a · q)
    scale-neg-left _ _ = solve! 𝓡

    scale-diff-sum :
      (κ ε δ η : 𝓡 .fst) →
      (κ · ε) - ((κ · δ) + (κ · η)) ≡ κ · (ε - (δ + η))
    scale-diff-sum _ _ _ _ = solve! 𝓡


private
  scale-positive-bound< :
    (a p q : ℚ) (κ ε : ℚ⁺) →
    0ℚ ℚOrder.< a →
    a ℚOrder.< radius κ →
    p ℚ.- q ℚOrder.< radius ε →
    (a ℚ.· p) ℚ.- (a ℚ.· q) ℚOrder.< radius (κ *⁺ ε)
  scale-positive-bound< a p q κ ε 0<a a<κ p-q<ε =
    subst
      (λ r → r ℚOrder.< radius (κ *⁺ ε))
      (sym (SolverHelpers.scale-diff-positive ℚCommRing a p q))
      a[p-q]<κε
    where
    a[p-q]<aε : a ℚ.· (p ℚ.- q) ℚOrder.< a ℚ.· radius ε
    a[p-q]<aε =
      Rational.mul-left-positive-< {a = a} {b = p ℚ.- q} {c = radius ε}
        0<a
        p-q<ε

    aε<κε : a ℚ.· radius ε ℚOrder.< radius κ ℚ.· radius ε
    aε<κε =
      ℚOrder.<-·o a (radius κ) (radius ε) (ε .snd) a<κ

    a[p-q]<κε : a ℚ.· (p ℚ.- q) ℚOrder.< radius (κ *⁺ ε)
    a[p-q]<κε =
      ℚOrder.isTrans<
        (a ℚ.· (p ℚ.- q))
        (a ℚ.· radius ε)
        (radius (κ *⁺ ε))
        a[p-q]<aε
        aε<κε

  scale-negative-bound< :
    (a p q : ℚ) (κ ε : ℚ⁺) →
    a ℚOrder.< 0ℚ →
    ℚ.- a ℚOrder.< radius κ →
    q ℚ.- p ℚOrder.< radius ε →
    (a ℚ.· p) ℚ.- (a ℚ.· q) ℚOrder.< radius (κ *⁺ ε)
  scale-negative-bound< a p q κ ε a<0 -a<κ q-p<ε =
    subst
      (λ r → r ℚOrder.< radius (κ *⁺ ε))
      (sym (SolverHelpers.scale-diff-negative ℚCommRing a p q))
      -a[q-p]<κε
    where
    0<-a : 0ℚ ℚOrder.< ℚ.- a
    0<-a =
      Rational.neg-positive {q = a} a<0

    -a[q-p]<-aε : (ℚ.- a) ℚ.· (q ℚ.- p) ℚOrder.< (ℚ.- a) ℚ.· radius ε
    -a[q-p]<-aε =
      Rational.mul-left-positive-< {a = ℚ.- a} {b = q ℚ.- p} {c = radius ε}
        0<-a
        q-p<ε

    -aε<κε : (ℚ.- a) ℚ.· radius ε ℚOrder.< radius κ ℚ.· radius ε
    -aε<κε =
      ℚOrder.<-·o (ℚ.- a) (radius κ) (radius ε) (ε .snd) -a<κ

    -a[q-p]<κε : (ℚ.- a) ℚ.· (q ℚ.- p) ℚOrder.< radius (κ *⁺ ε)
    -a[q-p]<κε =
      ℚOrder.isTrans<
        ((ℚ.- a) ℚ.· (q ℚ.- p))
        ((ℚ.- a) ℚ.· radius ε)
        (radius (κ *⁺ ε))
        -a[q-p]<-aε
        -aε<κε

  scale-zero-bound< :
    (p q : ℚ) (κ ε : ℚ⁺) →
    (0ℚ ℚ.· p) ℚ.- (0ℚ ℚ.· q) ℚOrder.< radius (κ *⁺ ε)
  scale-zero-bound< p q κ ε =
    subst
      (λ r → r ℚOrder.< radius (κ *⁺ ε))
      (sym (SolverHelpers.scale-diff-zero ℚCommRing p q))
      (Rational.mul-positive {a = radius κ} {b = radius ε} (κ .snd) (ε .snd))

  scale-positive-closed-bound< :
    (a p q : ℚ) (κ ε : ℚ⁺) →
    0ℚ ℚOrder.< a →
    a ℚOrder.≤ radius κ →
    p ℚ.- q ℚOrder.< radius ε →
    (a ℚ.· p) ℚ.- (a ℚ.· q) ℚOrder.< radius (κ *⁺ ε)
  scale-positive-closed-bound< a p q κ ε 0<a a≤κ p-q<ε =
    subst
      (λ r → r ℚOrder.< radius (κ *⁺ ε))
      (sym (SolverHelpers.scale-diff-positive ℚCommRing a p q))
      a[p-q]<κε
    where
    a[p-q]<aε : a ℚ.· (p ℚ.- q) ℚOrder.< a ℚ.· radius ε
    a[p-q]<aε =
      Rational.mul-left-positive-< {a = a} {b = p ℚ.- q} {c = radius ε}
        0<a
        p-q<ε

    aε≤κε : a ℚ.· radius ε ℚOrder.≤ radius κ ℚ.· radius ε
    aε≤κε =
      ℚOrder.≤-·o
        a
        (radius κ)
        (radius ε)
        (ℚOrder.<Weaken≤ 0ℚ (radius ε) (ε .snd))
        a≤κ

    a[p-q]<κε : a ℚ.· (p ℚ.- q) ℚOrder.< radius (κ *⁺ ε)
    a[p-q]<κε =
      ℚOrder.isTrans<≤
        (a ℚ.· (p ℚ.- q))
        (a ℚ.· radius ε)
        (radius (κ *⁺ ε))
        a[p-q]<aε
        aε≤κε

  scale-negative-closed-bound< :
    (a p q : ℚ) (κ ε : ℚ⁺) →
    a ℚOrder.< 0ℚ →
    ℚ.- a ℚOrder.≤ radius κ →
    q ℚ.- p ℚOrder.< radius ε →
    (a ℚ.· p) ℚ.- (a ℚ.· q) ℚOrder.< radius (κ *⁺ ε)
  scale-negative-closed-bound< a p q κ ε a<0 -a≤κ q-p<ε =
    subst
      (λ r → r ℚOrder.< radius (κ *⁺ ε))
      (sym (SolverHelpers.scale-diff-negative ℚCommRing a p q))
      -a[q-p]<κε
    where
    0<-a : 0ℚ ℚOrder.< ℚ.- a
    0<-a =
      Rational.neg-positive {q = a} a<0

    -a[q-p]<-aε : (ℚ.- a) ℚ.· (q ℚ.- p) ℚOrder.< (ℚ.- a) ℚ.· radius ε
    -a[q-p]<-aε =
      Rational.mul-left-positive-< {a = ℚ.- a} {b = q ℚ.- p} {c = radius ε}
        0<-a
        q-p<ε

    -aε≤κε : (ℚ.- a) ℚ.· radius ε ℚOrder.≤ radius κ ℚ.· radius ε
    -aε≤κε =
      ℚOrder.≤-·o
        (ℚ.- a)
        (radius κ)
        (radius ε)
        (ℚOrder.<Weaken≤ 0ℚ (radius ε) (ε .snd))
        -a≤κ

    -a[q-p]<κε : (ℚ.- a) ℚ.· (q ℚ.- p) ℚOrder.< radius (κ *⁺ ε)
    -a[q-p]<κε =
      ℚOrder.isTrans<≤
        ((ℚ.- a) ℚ.· (q ℚ.- p))
        ((ℚ.- a) ℚ.· radius ε)
        (radius (κ *⁺ ε))
        -a[q-p]<-aε
        -aε≤κε


scale-close-bound :
  (a : ℚ) (κ : ℚ⁺) →
  a ℚOrder.< radius κ →
  ℚ.- a ℚOrder.< radius κ →
  (p q : ℚ) (ε : ℚ⁺) →
  Closeℚ p ε q →
  Closeℚ (a ℚ.· p) (κ *⁺ ε) (a ℚ.· q)
scale-close-bound a κ a<κ -a<κ p q ε p∼q with a ℚOrder.≟ 0ℚ
... | ℚOrder.lt a<0 =
  scale-negative-bound< a p q κ ε a<0 -a<κ (p∼q .snd) ,
  scale-negative-bound< a q p κ ε a<0 -a<κ (p∼q .fst)
... | ℚOrder.eq a≡0 =
  subst
    (λ r → (r ℚ.· p) ℚ.- (r ℚ.· q) ℚOrder.< radius (κ *⁺ ε))
    (sym a≡0)
    (scale-zero-bound< p q κ ε) ,
  subst
    (λ r → (r ℚ.· q) ℚ.- (r ℚ.· p) ℚOrder.< radius (κ *⁺ ε))
    (sym a≡0)
    (scale-zero-bound< q p κ ε)
... | ℚOrder.gt 0<a =
  scale-positive-bound< a p q κ ε 0<a a<κ (p∼q .fst) ,
  scale-positive-bound< a q p κ ε 0<a a<κ (p∼q .snd)


scale-close-closed-bound :
  (a : ℚ) (κ : ℚ⁺) →
  a ℚOrder.≤ radius κ →
  ℚ.- a ℚOrder.≤ radius κ →
  (p q : ℚ) (ε : ℚ⁺) →
  Closeℚ p ε q →
  Closeℚ (a ℚ.· p) (κ *⁺ ε) (a ℚ.· q)
scale-close-closed-bound a κ a≤κ -a≤κ p q ε p∼q with a ℚOrder.≟ 0ℚ
... | ℚOrder.lt a<0 =
  scale-negative-closed-bound< a p q κ ε a<0 -a≤κ (p∼q .snd) ,
  scale-negative-closed-bound< a q p κ ε a<0 -a≤κ (p∼q .fst)
... | ℚOrder.eq a≡0 =
  subst
    (λ r → (r ℚ.· p) ℚ.- (r ℚ.· q) ℚOrder.< radius (κ *⁺ ε))
    (sym a≡0)
    (scale-zero-bound< p q κ ε) ,
  subst
    (λ r → (r ℚ.· q) ℚ.- (r ℚ.· p) ℚOrder.< radius (κ *⁺ ε))
    (sym a≡0)
    (scale-zero-bound< q p κ ε)
... | ℚOrder.gt 0<a =
  scale-positive-closed-bound< a p q κ ε 0<a a≤κ (p∼q .fst) ,
  scale-positive-closed-bound< a q p κ ε 0<a a≤κ (p∼q .snd)


scale-close :
  (a p q : ℚ) (ε : ℚ⁺) →
  Closeℚ p ε q →
  Closeℚ (a ℚ.· p) (scalar-bound a *⁺ ε) (a ℚ.· q)
scale-close a p q ε =
  scale-close-bound
    a
    (scalar-bound a)
    (scalar-bound-upper a)
    (scalar-bound-lower a)
    p
    q
    ε


scale-rational-close :
  (a p q : ℚ) (ε : ℚ⁺) →
  Closeℚ p ε q →
  rational (a ℚ.· p) ∼[ scalar-bound a *⁺ ε ] rational (a ℚ.· q)
scale-rational-close a p q ε p∼q =
  rational-rational-close
    (a ℚ.· p)
    (a ℚ.· q)
    (scalar-bound a *⁺ ε)
    (scale-close a p q ε p∼q)


private
  scaleKit :
    (a : ℚ) (κ : ℚ⁺) →
    a ℚOrder.< radius κ →
    ℚ.- a ℚOrder.< radius κ →
    RecursionKit ℓ-zero ℓ-zero
  scaleKit a κ a<κ -a<κ .RecursionKit.A =
    ℝᶜ
  scaleKit a κ a<κ -a<κ .RecursionKit.B ε x y =
    x ∼[ κ *⁺ ε ] y
  scaleKit a κ a<κ -a<κ .RecursionKit.isPropB ε x y =
    squash
  scaleKit a κ a<κ -a<κ .RecursionKit.separated x y closeAt =
    path x y λ ε →
      subst
        (λ ρ → x ∼[ ρ ] y)
        (scale-precision-cancel κ ε)
        (closeAt (posInv⁺ κ *⁺ ε))
  scaleKit a κ a<κ -a<κ .RecursionKit.rational* q =
    rational (a ℚ.· q)
  scaleKit a κ a<κ -a<κ .RecursionKit.limit* x g gCauchy =
    limit (scaledCauchyApproximation κ g gCauchy)
  scaleKit a κ a<κ -a<κ .RecursionKit.rational-rational* q r ε q∼r =
    rational-rational-close
      (a ℚ.· q)
      (a ℚ.· r)
      (κ *⁺ ε)
      (scale-close-bound a κ a<κ -a<κ q r ε q∼r)
  scaleKit a κ a<κ -a<κ .RecursionKit.rational-limit* q ε δ δ<ε y g gCauchy q∼gδ =
    rational-limit-close
      (a ℚ.· q)
      (κ *⁺ ε)
      (κ *⁺ δ)
      κδ<κε
      (scaledCauchyApproximation κ g gCauchy)
      q∼hκδ
    where
    κδ<κε : κ *⁺ δ <⁺ κ *⁺ ε
    κδ<κε =
      scale-precision-mono κ δ ε δ<ε

    precisionPath :
      (κ *⁺ ε) ⊖ (κ *⁺ δ) [ κδ<κε ] ≡
      κ *⁺ (ε ⊖ δ [ δ<ε ])
    precisionPath =
      scale-precision-difference κ ε δ δ<ε κδ<κε

    indexPath : posInv⁺ κ *⁺ (κ *⁺ δ) ≡ δ
    indexPath =
      scale-precision-cancel-left κ δ

    q∼hκδ :
      rational (a ℚ.· q)
        ∼[ (κ *⁺ ε) ⊖ (κ *⁺ δ) [ κδ<κε ] ]
      approximate (scaledCauchyApproximation κ g gCauchy) (κ *⁺ δ)
    q∼hκδ =
      subst2
        (λ ρ θ → rational (a ℚ.· q) ∼[ ρ ] g θ)
        (sym precisionPath)
        (sym indexPath)
        q∼gδ
  scaleKit a κ a<κ -a<κ .RecursionKit.limit-rational* x f fCauchy r ε δ δ<ε fδ∼r =
    limit-rational-close
      (scaledCauchyApproximation κ f fCauchy)
      (a ℚ.· r)
      (κ *⁺ ε)
      (κ *⁺ δ)
      κδ<κε
      hκδ∼r
    where
    κδ<κε : κ *⁺ δ <⁺ κ *⁺ ε
    κδ<κε =
      scale-precision-mono κ δ ε δ<ε

    precisionPath :
      (κ *⁺ ε) ⊖ (κ *⁺ δ) [ κδ<κε ] ≡
      κ *⁺ (ε ⊖ δ [ δ<ε ])
    precisionPath =
      scale-precision-difference κ ε δ δ<ε κδ<κε

    indexPath : posInv⁺ κ *⁺ (κ *⁺ δ) ≡ δ
    indexPath =
      scale-precision-cancel-left κ δ

    hκδ∼r :
      approximate (scaledCauchyApproximation κ f fCauchy) (κ *⁺ δ)
        ∼[ (κ *⁺ ε) ⊖ (κ *⁺ δ) [ κδ<κε ] ]
      rational (a ℚ.· r)
    hκδ∼r =
      subst2
        (λ θ ρ → f θ ∼[ ρ ] rational (a ℚ.· r))
        (sym indexPath)
        (sym precisionPath)
        fδ∼r
  scaleKit a κ a<κ -a<κ .RecursionKit.limit-limit* x y f g fCauchy gCauchy ε δ η δ+η<ε fδ∼gη =
    limit-limit-close
      (scaledCauchyApproximation κ f fCauchy)
      (scaledCauchyApproximation κ g gCauchy)
      (κ *⁺ ε)
      (κ *⁺ δ)
      (κ *⁺ η)
      κδη<κε
      hκδ∼hκη
    where
    κδη<κε : (κ *⁺ δ) +⁺ (κ *⁺ η) <⁺ κ *⁺ ε
    κδη<κε =
      scale-precision-sum< κ ε δ η δ+η<ε

    precisionPath :
      (κ *⁺ ε) ⊖ ((κ *⁺ δ) +⁺ (κ *⁺ η)) [ κδη<κε ] ≡
      κ *⁺ (ε ⊖ (δ +⁺ η) [ δ+η<ε ])
    precisionPath =
      scale-precision-sum-difference κ ε δ η δ+η<ε κδη<κε

    δIndexPath : posInv⁺ κ *⁺ (κ *⁺ δ) ≡ δ
    δIndexPath =
      scale-precision-cancel-left κ δ

    ηIndexPath : posInv⁺ κ *⁺ (κ *⁺ η) ≡ η
    ηIndexPath =
      scale-precision-cancel-left κ η

    neededPrecision : ℚ⁺
    neededPrecision =
      (κ *⁺ ε) ⊖ ((κ *⁺ δ) +⁺ (κ *⁺ η)) [ κδη<κε ]

    fδ∼gη-neededPrecision :
      f δ ∼[ neededPrecision ] g η
    fδ∼gη-neededPrecision =
      subst
        (λ ρ → f δ ∼[ ρ ] g η)
        (sym precisionPath)
        fδ∼gη

    fδ∼hκη :
      f δ ∼[ neededPrecision ]
      approximate (scaledCauchyApproximation κ g gCauchy) (κ *⁺ η)
    fδ∼hκη =
      subst
        (λ θ → f δ ∼[ neededPrecision ] g θ)
        (sym ηIndexPath)
        fδ∼gη-neededPrecision

    hκδ∼hκη :
      approximate (scaledCauchyApproximation κ f fCauchy) (κ *⁺ δ)
        ∼[ neededPrecision ]
      approximate (scaledCauchyApproximation κ g gCauchy) (κ *⁺ η)
    hκδ∼hκη =
      subst
        (λ θ →
          f θ ∼[ neededPrecision ]
          approximate (scaledCauchyApproximation κ g gCauchy) (κ *⁺ η))
        (sym δIndexPath)
        fδ∼hκη

  module ScaleRecursion
    (a : ℚ) (κ : ℚ⁺)
    (a<κ : a ℚOrder.< radius κ)
    (-a<κ : ℚ.- a ℚOrder.< radius κ) =
    Recursion (scaleKit a κ a<κ -a<κ)


boundedScalarMulᶜ :
  (a : ℚ) (κ : ℚ⁺) →
  a ℚOrder.< radius κ →
  ℚ.- a ℚOrder.< radius κ →
  ℝᶜ → ℝᶜ
boundedScalarMulᶜ a κ a<κ -a<κ =
  ScaleRecursion.rec a κ a<κ -a<κ


boundedScalarMulᶜ-rational :
  (a : ℚ) (κ : ℚ⁺)
  (a<κ : a ℚOrder.< radius κ)
  (-a<κ : ℚ.- a ℚOrder.< radius κ)
  (q : ℚ) →
  boundedScalarMulᶜ a κ a<κ -a<κ (rational q) ≡ rational (a ℚ.· q)
boundedScalarMulᶜ-rational a κ a<κ -a<κ q =
  refl


boundedScalarMulᶜ-close :
  (a : ℚ) (κ : ℚ⁺)
  (a<κ : a ℚOrder.< radius κ)
  (-a<κ : ℚ.- a ℚOrder.< radius κ) →
  {x y : ℝᶜ} {ε : ℚ⁺} →
  x ∼[ ε ] y →
  boundedScalarMulᶜ a κ a<κ -a<κ x
    ∼[ κ *⁺ ε ]
  boundedScalarMulᶜ a κ a<κ -a<κ y
boundedScalarMulᶜ-close a κ a<κ -a<κ =
  ScaleRecursion.rec-close a κ a<κ -a<κ


boundedScalarMulᶜ-lipschitz :
  (a : ℚ) (κ : ℚ⁺)
  (a<κ : a ℚOrder.< radius κ)
  (-a<κ : ℚ.- a ℚOrder.< radius κ) →
  IsLipschitz (boundedScalarMulᶜ a κ a<κ -a<κ)
boundedScalarMulᶜ-lipschitz a κ a<κ -a<κ =
  (λ ε → posInv⁺ κ *⁺ ε) ,
  λ ε {x = x} {y = y} x∼y →
    subst
      (λ ρ → boundedScalarMulᶜ a κ a<κ -a<κ x
        ∼[ ρ ]
        boundedScalarMulᶜ a κ a<κ -a<κ y)
      (scale-precision-cancel κ ε)
      (boundedScalarMulᶜ-close a κ a<κ -a<κ x∼y)


boundedScalarMulᶜ-continuous :
  (a : ℚ) (κ : ℚ⁺)
  (a<κ : a ℚOrder.< radius κ)
  (-a<κ : ℚ.- a ℚOrder.< radius κ) →
  IsContinuous (boundedScalarMulᶜ a κ a<κ -a<κ)
boundedScalarMulᶜ-continuous a κ a<κ -a<κ =
  lipschitz→continuous (boundedScalarMulᶜ-lipschitz a κ a<κ -a<κ)


boundedScalarMulᶜ-bound-independent :
  (a : ℚ) (κ μ : ℚ⁺)
  (a<κ : a ℚOrder.< radius κ)
  (-a<κ : ℚ.- a ℚOrder.< radius κ)
  (a<μ : a ℚOrder.< radius μ)
  (-a<μ : ℚ.- a ℚOrder.< radius μ)
  (x : ℝᶜ) →
  boundedScalarMulᶜ a κ a<κ -a<κ x ≡
  boundedScalarMulᶜ a μ a<μ -a<μ x
boundedScalarMulᶜ-bound-independent a κ μ a<κ -a<κ a<μ -a<μ =
  continuous-equal
    (boundedScalarMulᶜ a κ a<κ -a<κ)
    (boundedScalarMulᶜ a μ a<μ -a<μ)
    (boundedScalarMulᶜ-continuous a κ a<κ -a<κ)
    (boundedScalarMulᶜ-continuous a μ a<μ -a<μ)
    (λ _ → refl)


boundedScalarMulᶜ-distrib-real-add-rational-left :
  (a : ℚ) (κ : ℚ⁺)
  (a<κ : a ℚOrder.< radius κ)
  (-a<κ : ℚ.- a ℚOrder.< radius κ)
  (q : ℚ) (y : ℝᶜ) →
  boundedScalarMulᶜ a κ a<κ -a<κ (rational q +ᶜ y) ≡
  boundedScalarMulᶜ a κ a<κ -a<κ (rational q) +ᶜ
  boundedScalarMulᶜ a κ a<κ -a<κ y
boundedScalarMulᶜ-distrib-real-add-rational-left a κ a<κ -a<κ q =
  continuous-equal
    (λ y → boundedScalarMulᶜ a κ a<κ -a<κ (rational q +ᶜ y))
    (λ y →
      boundedScalarMulᶜ a κ a<κ -a<κ (rational q) +ᶜ
      boundedScalarMulᶜ a κ a<κ -a<κ y)
    (comp-continuous
      (boundedScalarMulᶜ-continuous a κ a<κ -a<κ)
      (add-continuous-right (rational q)))
    (comp-continuous
      (add-continuous-right
        (boundedScalarMulᶜ a κ a<κ -a<κ (rational q)))
      (boundedScalarMulᶜ-continuous a κ a<κ -a<κ))
    (λ r → cong rational (ℚ.·DistL+ a q r))


boundedScalarMulᶜ-distrib-real-add :
  (a : ℚ) (κ : ℚ⁺)
  (a<κ : a ℚOrder.< radius κ)
  (-a<κ : ℚ.- a ℚOrder.< radius κ)
  (x y : ℝᶜ) →
  boundedScalarMulᶜ a κ a<κ -a<κ (x +ᶜ y) ≡
  boundedScalarMulᶜ a κ a<κ -a<κ x +ᶜ
  boundedScalarMulᶜ a κ a<κ -a<κ y
boundedScalarMulᶜ-distrib-real-add a κ a<κ -a<κ x y =
  continuous-equal
    (λ z → boundedScalarMulᶜ a κ a<κ -a<κ (z +ᶜ y))
    (λ z →
      boundedScalarMulᶜ a κ a<κ -a<κ z +ᶜ
      boundedScalarMulᶜ a κ a<κ -a<κ y)
    (comp-continuous
      (boundedScalarMulᶜ-continuous a κ a<κ -a<κ)
      (add-continuous-left y))
    (comp-continuous
      (add-continuous-left
        (boundedScalarMulᶜ a κ a<κ -a<κ y))
      (boundedScalarMulᶜ-continuous a κ a<κ -a<κ))
    (λ q → boundedScalarMulᶜ-distrib-real-add-rational-left a κ a<κ -a<κ q y)
    x


boundedScalarMulᶜ-zero-right :
  (a : ℚ) (κ : ℚ⁺)
  (a<κ : a ℚOrder.< radius κ)
  (-a<κ : ℚ.- a ℚOrder.< radius κ) →
  boundedScalarMulᶜ a κ a<κ -a<κ 0ᶜ ≡ 0ᶜ
boundedScalarMulᶜ-zero-right a κ a<κ -a<κ =
  cong rational (SolverHelpers.scale-zero-right ℚCommRing a)


boundedScalarMulᶜ-zero-scalar :
  (κ : ℚ⁺)
  (0<κ : 0ℚ ℚOrder.< radius κ)
  (0<κ' : ℚ.- 0ℚ ℚOrder.< radius κ)
  (x : ℝᶜ) →
  boundedScalarMulᶜ 0ℚ κ 0<κ 0<κ' x ≡ 0ᶜ
boundedScalarMulᶜ-zero-scalar κ 0<κ 0<κ' =
  continuous-constant-equal
    (boundedScalarMulᶜ 0ℚ κ 0<κ 0<κ')
    0ᶜ
    (boundedScalarMulᶜ-continuous 0ℚ κ 0<κ 0<κ')
    (λ q → cong rational (ℚ.·AnnihilL q))


boundedScalarMulᶜ-neg-real :
  (a : ℚ) (κ : ℚ⁺)
  (a<κ : a ℚOrder.< radius κ)
  (-a<κ : ℚ.- a ℚOrder.< radius κ)
  (x : ℝᶜ) →
  boundedScalarMulᶜ a κ a<κ -a<κ (-ᶜ x) ≡
  -ᶜ (boundedScalarMulᶜ a κ a<κ -a<κ x)
boundedScalarMulᶜ-neg-real a κ a<κ -a<κ =
  continuous-equal
    (λ x → boundedScalarMulᶜ a κ a<κ -a<κ (-ᶜ x))
    (λ x → -ᶜ (boundedScalarMulᶜ a κ a<κ -a<κ x))
    (comp-continuous
      (boundedScalarMulᶜ-continuous a κ a<κ -a<κ)
      neg-continuous)
    (comp-continuous
      neg-continuous
      (boundedScalarMulᶜ-continuous a κ a<κ -a<κ))
    (λ q → cong rational (SolverHelpers.scale-neg-right ℚCommRing a q))


boundedScalarMulᶜ-neg-scalar :
  (a : ℚ) (κ : ℚ⁺)
  (a<κ : a ℚOrder.< radius κ)
  (-a<κ : ℚ.- a ℚOrder.< radius κ)
  (negneg-a<κ : ℚ.- (ℚ.- a) ℚOrder.< radius κ)
  (x : ℝᶜ) →
  boundedScalarMulᶜ (ℚ.- a) κ -a<κ negneg-a<κ x ≡
  -ᶜ (boundedScalarMulᶜ a κ a<κ -a<κ x)
boundedScalarMulᶜ-neg-scalar a κ a<κ -a<κ negneg-a<κ =
  continuous-equal
    (boundedScalarMulᶜ (ℚ.- a) κ -a<κ negneg-a<κ)
    (λ x → -ᶜ (boundedScalarMulᶜ a κ a<κ -a<κ x))
    (boundedScalarMulᶜ-continuous (ℚ.- a) κ -a<κ negneg-a<κ)
    (comp-continuous
      neg-continuous
      (boundedScalarMulᶜ-continuous a κ a<κ -a<κ))
    (λ q → cong rational (SolverHelpers.scale-neg-left ℚCommRing a q))


scalarMulᶜ : ℚ → ℝᶜ → ℝᶜ
scalarMulᶜ a =
  boundedScalarMulᶜ a (scalar-bound a) (scalar-bound-upper a) (scalar-bound-lower a)


scalarMulᶜ-rational :
  (a q : ℚ) →
  scalarMulᶜ a (rational q) ≡ rational (a ℚ.· q)
scalarMulᶜ-rational a q =
  refl


scalarMulᶜ-close :
  (a : ℚ) →
  {x y : ℝᶜ} {ε : ℚ⁺} →
  x ∼[ ε ] y →
  scalarMulᶜ a x ∼[ scalar-bound a *⁺ ε ] scalarMulᶜ a y
scalarMulᶜ-close a =
  boundedScalarMulᶜ-close
    a
    (scalar-bound a)
    (scalar-bound-upper a)
    (scalar-bound-lower a)


scalarMulᶜ-lipschitz :
  (a : ℚ) →
  IsLipschitz (scalarMulᶜ a)
scalarMulᶜ-lipschitz a =
  (λ ε → posInv⁺ (scalar-bound a) *⁺ ε) ,
  λ ε {x = x} {y = y} x∼y →
    subst
      (λ ρ → scalarMulᶜ a x ∼[ ρ ] scalarMulᶜ a y)
      (scale-precision-cancel (scalar-bound a) ε)
      (scalarMulᶜ-close a x∼y)


scalarMulᶜ-continuous :
  (a : ℚ) →
  IsContinuous (scalarMulᶜ a)
scalarMulᶜ-continuous a =
  lipschitz→continuous (scalarMulᶜ-lipschitz a)


scalarMulᶜ-one :
  (x : ℝᶜ) →
  scalarMulᶜ 1ℚ x ≡ x
scalarMulᶜ-one =
  continuous-equal
    (scalarMulᶜ 1ℚ)
    (λ x → x)
    (scalarMulᶜ-continuous 1ℚ)
    (nonexpanding→continuous id-nonexpanding)
    (λ q → cong rational (ℚ.·IdL q))


scalarMulᶜ-zero :
  (x : ℝᶜ) →
  scalarMulᶜ 0ℚ x ≡ 0ᶜ
scalarMulᶜ-zero =
  continuous-constant-equal
    (scalarMulᶜ 0ℚ)
    0ᶜ
    (scalarMulᶜ-continuous 0ℚ)
    (λ q → cong rational (ℚ.·AnnihilL q))


scalarMulᶜ-zero-right :
  (a : ℚ) →
  scalarMulᶜ a 0ᶜ ≡ 0ᶜ
scalarMulᶜ-zero-right a =
  cong rational (SolverHelpers.scale-zero-right ℚCommRing a)


scalarMulᶜ-neg-real :
  (a : ℚ) (x : ℝᶜ) →
  scalarMulᶜ a (-ᶜ x) ≡ -ᶜ (scalarMulᶜ a x)
scalarMulᶜ-neg-real a =
  continuous-equal
    (λ x → scalarMulᶜ a (-ᶜ x))
    (λ x → -ᶜ (scalarMulᶜ a x))
    (comp-continuous (scalarMulᶜ-continuous a) neg-continuous)
    (comp-continuous neg-continuous (scalarMulᶜ-continuous a))
    (λ q → cong rational (SolverHelpers.scale-neg-right ℚCommRing a q))


scalarMulᶜ-neg-scalar :
  (a : ℚ) (x : ℝᶜ) →
  scalarMulᶜ (ℚ.- a) x ≡ -ᶜ (scalarMulᶜ a x)
scalarMulᶜ-neg-scalar a =
  continuous-equal
    (scalarMulᶜ (ℚ.- a))
    (λ x → -ᶜ (scalarMulᶜ a x))
    (scalarMulᶜ-continuous (ℚ.- a))
    (comp-continuous neg-continuous (scalarMulᶜ-continuous a))
    (λ q → cong rational (SolverHelpers.scale-neg-left ℚCommRing a q))


scalarMulᶜ-assoc :
  (a b : ℚ) (x : ℝᶜ) →
  scalarMulᶜ a (scalarMulᶜ b x) ≡ scalarMulᶜ (a ℚ.· b) x
scalarMulᶜ-assoc a b =
  continuous-equal
    (λ x → scalarMulᶜ a (scalarMulᶜ b x))
    (scalarMulᶜ (a ℚ.· b))
    (comp-continuous (scalarMulᶜ-continuous a) (scalarMulᶜ-continuous b))
    (scalarMulᶜ-continuous (a ℚ.· b))
    (λ q → cong rational (ℚ.·Assoc a b q))


scalarMulᶜ-distrib-scalar-add :
  (a b : ℚ) (x : ℝᶜ) →
  scalarMulᶜ (a ℚ.+ b) x ≡ scalarMulᶜ a x +ᶜ scalarMulᶜ b x
scalarMulᶜ-distrib-scalar-add a b =
  continuous-equal
    (scalarMulᶜ (a ℚ.+ b))
    (λ x → scalarMulᶜ a x +ᶜ scalarMulᶜ b x)
    (scalarMulᶜ-continuous (a ℚ.+ b))
    (pointwise-sum-continuous (scalarMulᶜ-continuous a) (scalarMulᶜ-continuous b))
    (λ q → cong rational (ℚ.·DistR+ a b q))


scalarMulᶜ-distrib-real-add-rational-left :
  (a q : ℚ) (y : ℝᶜ) →
  scalarMulᶜ a (rational q +ᶜ y) ≡
  scalarMulᶜ a (rational q) +ᶜ scalarMulᶜ a y
scalarMulᶜ-distrib-real-add-rational-left a q =
  continuous-equal
    (λ y → scalarMulᶜ a (rational q +ᶜ y))
    (λ y → scalarMulᶜ a (rational q) +ᶜ scalarMulᶜ a y)
    (comp-continuous (scalarMulᶜ-continuous a) (add-continuous-right (rational q)))
    (comp-continuous (add-continuous-right (scalarMulᶜ a (rational q))) (scalarMulᶜ-continuous a))
    (λ r → cong rational (ℚ.·DistL+ a q r))


scalarMulᶜ-distrib-real-add :
  (a : ℚ) (x y : ℝᶜ) →
  scalarMulᶜ a (x +ᶜ y) ≡ scalarMulᶜ a x +ᶜ scalarMulᶜ a y
scalarMulᶜ-distrib-real-add a x y =
  continuous-equal
    (λ z → scalarMulᶜ a (z +ᶜ y))
    (λ z → scalarMulᶜ a z +ᶜ scalarMulᶜ a y)
    (comp-continuous (scalarMulᶜ-continuous a) (add-continuous-left y))
    (comp-continuous (add-continuous-left (scalarMulᶜ a y)) (scalarMulᶜ-continuous a))
    (λ q → scalarMulᶜ-distrib-real-add-rational-left a q y)
    x
