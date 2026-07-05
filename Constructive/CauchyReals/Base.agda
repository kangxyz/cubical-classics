{-

HoTT-style Cauchy reals

The real numbers and their rational-indexed closeness relation are defined
simultaneously, following the higher inductive-inductive construction in the
HoTT book.

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Int using (pos)
open import Cubical.Data.Nat using (zero)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma


0ℚ : ℚ
0ℚ = [ pos zero / 1+ zero ]


positive-sum :
  {p q : ℚ} →
  0ℚ ℚOrder.< p →
  0ℚ ℚOrder.< q →
  0ℚ ℚOrder.< p ℚ.+ q
positive-sum {p = p} {q = q} 0<p 0<q =
  subst
    (λ r → r ℚOrder.< p ℚ.+ q)
    (ℚ.+IdR 0ℚ)
    (ℚOrder.<Monotone+ 0ℚ p 0ℚ q 0<p 0<q)


ℚ⁺ : Type₀
ℚ⁺ = Σ[ q ∈ ℚ ] 0ℚ ℚOrder.< q


radius : ℚ⁺ → ℚ
radius ε = ε .fst


infixl 6 _+⁺_
infix 4 _<⁺_

_+⁺_ : ℚ⁺ → ℚ⁺ → ℚ⁺
ε +⁺ δ =
  radius ε ℚ.+ radius δ ,
  positive-sum {p = radius ε} {q = radius δ} (ε .snd) (δ .snd)


_<⁺_ : ℚ⁺ → ℚ⁺ → Type₀
ε <⁺ δ = radius ε ℚOrder.< radius δ


difference-positive :
  (ε δ : ℚ⁺) → δ <⁺ ε → 0ℚ ℚOrder.< radius ε ℚ.- radius δ
difference-positive ε δ δ<ε =
  subst
    (λ q → q ℚOrder.< radius ε ℚ.- radius δ)
    (ℚ.+InvR (radius δ))
    (ℚOrder.<-+o (radius δ) (radius ε) (ℚ.- radius δ) δ<ε)


_⊖_[_] : (ε δ : ℚ⁺) → δ <⁺ ε → ℚ⁺
(ε ⊖ δ [ δ<ε ]) =
  radius ε ℚ.- radius δ ,
  difference-positive ε δ δ<ε


Closeℚ : ℚ → ℚ⁺ → ℚ → Type₀
Closeℚ q ε r =
  (q ℚ.- r ℚOrder.< radius ε) ×
  (r ℚ.- q ℚOrder.< radius ε)


isPropCloseℚ : (q : ℚ) (ε : ℚ⁺) (r : ℚ) → isProp (Closeℚ q ε r)
isPropCloseℚ q ε r =
  isProp×
    (ℚOrder.isProp< (q ℚ.- r) (radius ε))
    (ℚOrder.isProp< (r ℚ.- q) (radius ε))


mutual
  data ℝᴴ : Type₀ where
    rational : ℚ → ℝᴴ
    limit : CauchyApproximation → ℝᴴ
    path : (x y : ℝᴴ) → ((ε : ℚ⁺) → x ∼[ ε ] y) → x ≡ y
    isSetℝᴴ : isSet ℝᴴ

  record CauchyApproximation : Type₀ where
    inductive
    no-eta-equality
    constructor cauchy-approximation

    field
      approximate : ℚ⁺ → ℝᴴ
      isRegular :
        (ε δ : ℚ⁺) →
        approximate ε ∼[ ε +⁺ δ ] approximate δ

  data _∼[_]_ : ℝᴴ → ℚ⁺ → ℝᴴ → Type₀ where
    rational-rational-close :
      (q r : ℚ) (ε : ℚ⁺) →
      Closeℚ q ε r →
      rational q ∼[ ε ] rational r

    rational-limit-close :
      (q : ℚ) (ε δ : ℚ⁺) →
      (δ<ε : δ <⁺ ε) →
      (y : CauchyApproximation) →
      rational q ∼[ ε ⊖ δ [ δ<ε ] ] CauchyApproximation.approximate y δ →
      rational q ∼[ ε ] limit y

    limit-rational-close :
      (x : CauchyApproximation) →
      (r : ℚ) (ε δ : ℚ⁺) →
      (δ<ε : δ <⁺ ε) →
      CauchyApproximation.approximate x δ ∼[ ε ⊖ δ [ δ<ε ] ] rational r →
      limit x ∼[ ε ] rational r

    limit-limit-close :
      (x y : CauchyApproximation) →
      (ε δ η : ℚ⁺) →
      (δ+η<ε : δ +⁺ η <⁺ ε) →
      CauchyApproximation.approximate x δ
        ∼[ ε ⊖ (δ +⁺ η) [ δ+η<ε ] ]
        CauchyApproximation.approximate y η →
      limit x ∼[ ε ] limit y

    isProp∼ : {x y : ℝᴴ} {ε : ℚ⁺} → isProp (x ∼[ ε ] y)


open CauchyApproximation public


CauchyReals : Type₀
CauchyReals = ℝᴴ


ℚ→ℝᴴ : ℚ → ℝᴴ
ℚ→ℝᴴ = rational
