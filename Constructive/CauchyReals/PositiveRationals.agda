{-

Positive rational precisions

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.PositiveRationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Int using (pos)
open import Cubical.Data.Nat using (zero ; suc)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma

import Constructive.Rationals as Rational
open Rational using (1/2 ; 0<1/2 ; double-half)


0ℚ : ℚ
0ℚ = [ pos zero / 1+ zero ]


1ℚ : ℚ
1ℚ = [ pos (suc zero) / 1+ zero ]


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


Q+ : Type₀
Q+ = ℚ⁺


radius : ℚ⁺ → ℚ
radius ε = ε .fst


isPropPositive : (q : ℚ) → isProp (0ℚ ℚOrder.< q)
isPropPositive q = ℚOrder.isProp< 0ℚ q


ℚ⁺Path : {ε δ : ℚ⁺} → radius ε ≡ radius δ → ε ≡ δ
ℚ⁺Path p = Σ≡Prop isPropPositive p


infixl 6 _+⁺_
infix 4 _<⁺_

_+⁺_ : ℚ⁺ → ℚ⁺ → ℚ⁺
ε +⁺ δ =
  radius ε ℚ.+ radius δ ,
  positive-sum {p = radius ε} {q = radius δ} (ε .snd) (δ .snd)


+⁺-comm : (ε δ : ℚ⁺) → ε +⁺ δ ≡ δ +⁺ ε
+⁺-comm ε δ =
  ℚ⁺Path (ℚ.+Comm (radius ε) (radius δ))


+⁺-assoc : (ε δ η : ℚ⁺) → (ε +⁺ δ) +⁺ η ≡ ε +⁺ (δ +⁺ η)
+⁺-assoc ε δ η =
  ℚ⁺Path (sym (ℚ.+Assoc (radius ε) (radius δ) (radius η)))


_<⁺_ : ℚ⁺ → ℚ⁺ → Type₀
ε <⁺ δ = radius ε ℚOrder.< radius δ


<⁺-trans : {ε δ η : ℚ⁺} → ε <⁺ δ → δ <⁺ η → ε <⁺ η
<⁺-trans {ε = ε} {δ = δ} {η = η} =
  ℚOrder.isTrans< (radius ε) (radius δ) (radius η)


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


summand-left<sum : (ε δ : ℚ⁺) → ε <⁺ ε +⁺ δ
summand-left<sum ε δ =
  subst
    (λ q → q ℚOrder.< radius (ε +⁺ δ))
    (ℚ.+IdR (radius ε))
    (ℚOrder.<-o+ 0ℚ (radius δ) (radius ε) (δ .snd))


min⁺ : ℚ⁺ → ℚ⁺ → ℚ⁺
min⁺ ε δ =
  ℚ.min (radius ε) (radius δ) ,
  Rational.<min
    {q = 0ℚ}
    {r = radius ε}
    {s = radius δ}
    (ε .snd)
    (δ .snd)


min⁺≤left : (ε δ : ℚ⁺) → radius (min⁺ ε δ) ℚOrder.≤ radius ε
min⁺≤left ε δ =
  ℚOrder.min≤ (radius ε) (radius δ)


min⁺≤right : (ε δ : ℚ⁺) → radius (min⁺ ε δ) ℚOrder.≤ radius δ
min⁺≤right ε δ =
  Rational.min≤r (radius ε) (radius δ)


summand-right<sum : (ε δ : ℚ⁺) → δ <⁺ ε +⁺ δ
summand-right<sum ε δ =
  subst
    (λ q → radius δ ℚOrder.< q)
    (ℚ.+Comm (radius δ) (radius ε))
    (summand-left<sum δ ε)


sum-difference-cancel-left :
  (ε δ : ℚ⁺) →
  radius δ ℚ.+ (radius ε ℚ.- radius δ) ≡ radius ε
sum-difference-cancel-left ε δ =
  ℚ.+Assoc (radius δ) (radius ε) (ℚ.- radius δ) ∙
  cong (λ q → q ℚ.+ (ℚ.- radius δ)) (ℚ.+Comm (radius δ) (radius ε)) ∙
  sym (ℚ.+Assoc (radius ε) (radius δ) (ℚ.- radius δ)) ∙
  cong (radius ε ℚ.+_) (ℚ.+InvR (radius δ)) ∙
  ℚ.+IdR (radius ε)


sum<from-difference :
  (ε δ κ : ℚ⁺) →
  (δ<ε : δ <⁺ ε) →
  κ <⁺ (ε ⊖ δ [ δ<ε ]) →
  δ +⁺ κ <⁺ ε
sum<from-difference ε δ κ δ<ε κ<ε-δ =
  subst
    (λ q → radius (δ +⁺ κ) ℚOrder.< q)
    (sum-difference-cancel-left ε δ)
    (ℚOrder.<-o+ (radius κ) (radius (ε ⊖ δ [ δ<ε ])) (radius δ) κ<ε-δ)


sum-difference-left :
  (δ κ : ℚ⁺) →
  (δ<δ+κ : δ <⁺ δ +⁺ κ) →
  (δ +⁺ κ) ⊖ δ [ δ<δ+κ ] ≡ κ
sum-difference-left δ κ δ<δ+κ =
  ℚ⁺Path
    (cong (λ q → q ℚ.+ (ℚ.- radius δ)) (ℚ.+Comm (radius δ) (radius κ)) ∙
     sym (ℚ.+Assoc (radius κ) (radius δ) (ℚ.- radius δ)) ∙
     cong (radius κ ℚ.+_) (ℚ.+InvR (radius δ)) ∙
     ℚ.+IdR (radius κ))


difference-mono-left :
  (ε ζ δ : ℚ⁺) →
  (δ<ε : δ <⁺ ε) →
  (δ<ζ : δ <⁺ ζ) →
  ε <⁺ ζ →
  (ε ⊖ δ [ δ<ε ]) <⁺ (ζ ⊖ δ [ δ<ζ ])
difference-mono-left ε ζ δ δ<ε δ<ζ ε<ζ =
  ℚOrder.<-+o (radius ε) (radius ζ) (ℚ.- radius δ) ε<ζ


half : ℚ → ℚ
half q = q ℚ.· 1/2


half-positive : {q : ℚ} → 0ℚ ℚOrder.< q → 0ℚ ℚOrder.< half q
half-positive {q = q} 0<q =
  subst
    (λ r → r ℚOrder.< half q)
    (ℚ.·AnnihilL 1/2)
    (ℚOrder.<-·o 0ℚ q 1/2 0<1/2 0<q)


half⁺ : ℚ⁺ → ℚ⁺
half⁺ ε = half (radius ε) , half-positive {q = radius ε} (ε .snd)


half+half≡ : (q : ℚ) → half q ℚ.+ half q ≡ q
half+half≡ q =
  sym (ℚ.·DistR+ q q 1/2) ∙ double-half q


half⁺+half⁺≡ : (ε : ℚ⁺) → half⁺ ε +⁺ half⁺ ε ≡ ε
half⁺+half⁺≡ ε =
  ℚ⁺Path (half+half≡ (radius ε))


half< : (ε : ℚ⁺) → half⁺ ε <⁺ ε
half< ε =
  subst2
    ℚOrder._<_
    (ℚ.+IdR (half (radius ε)))
    (half+half≡ (radius ε))
    (ℚOrder.<-o+ 0ℚ (half (radius ε)) (half (radius ε))
      (half⁺ ε .snd))


half-min⁺<left : (ε δ : ℚ⁺) → half⁺ (min⁺ ε δ) <⁺ ε
half-min⁺<left ε δ =
  ℚOrder.isTrans<≤
    (radius (half⁺ (min⁺ ε δ)))
    (radius (min⁺ ε δ))
    (radius ε)
    (half< (min⁺ ε δ))
    (min⁺≤left ε δ)


half-min⁺<right : (ε δ : ℚ⁺) → half⁺ (min⁺ ε δ) <⁺ δ
half-min⁺<right ε δ =
  ℚOrder.isTrans<≤
    (radius (half⁺ (min⁺ ε δ)))
    (radius (min⁺ ε δ))
    (radius δ)
    (half< (min⁺ ε δ))
    (min⁺≤right ε δ)


quarter⁺ : ℚ⁺ → ℚ⁺
quarter⁺ ε = half⁺ (half⁺ ε)


quarter< : (ε : ℚ⁺) → quarter⁺ ε <⁺ ε
quarter< ε =
  <⁺-trans
    {ε = quarter⁺ ε}
    {δ = half⁺ ε}
    {η = ε}
    (half< (half⁺ ε))
    (half< ε)


quarter-sum≡half : (ε : ℚ⁺) → radius (quarter⁺ ε +⁺ quarter⁺ ε) ≡ radius (half⁺ ε)
quarter-sum≡half ε = half+half≡ (radius (half⁺ ε))


quarter-sum< : (ε : ℚ⁺) → quarter⁺ ε +⁺ quarter⁺ ε <⁺ ε
quarter-sum< ε =
  subst
    (λ q → q ℚOrder.< radius ε)
    (sym (quarter-sum≡half ε))
    (half< ε)


half-difference≡half : (q : ℚ) → q ℚ.- half q ≡ half q
half-difference≡half q =
  cong (λ r → r ℚ.+ (ℚ.- half q)) (sym (half+half≡ q)) ∙
  sym (ℚ.+Assoc (half q) (half q) (ℚ.- half q)) ∙
  cong (half q ℚ.+_) (ℚ.+InvR (half q)) ∙
  ℚ.+IdR (half q)


quarter-sum-difference≡ :
  (ε : ℚ⁺) →
  (p : quarter⁺ ε +⁺ quarter⁺ ε <⁺ ε) →
  ε ⊖ (quarter⁺ ε +⁺ quarter⁺ ε) [ p ] ≡ quarter⁺ ε +⁺ quarter⁺ ε
quarter-sum-difference≡ ε p =
  ℚ⁺Path
    (cong (λ q → radius ε ℚ.- q) (quarter-sum≡half ε) ∙
     half-difference≡half (radius ε) ∙
     sym (quarter-sum≡half ε))


three-quarter< :
  (ε : ℚ⁺) →
  (quarter⁺ ε +⁺ quarter⁺ ε) +⁺ quarter⁺ ε <⁺ ε
three-quarter< ε =
  sum<from-difference ε δ κ δ<ε κ<ε-δ
  where
  δ κ : ℚ⁺
  δ = quarter⁺ ε +⁺ quarter⁺ ε
  κ = quarter⁺ ε

  δ<ε : δ <⁺ ε
  δ<ε = quarter-sum< ε

  κ<ε-δ : κ <⁺ ε ⊖ δ [ δ<ε ]
  κ<ε-δ =
    subst
      (λ ρ → κ <⁺ ρ)
      (sym (quarter-sum-difference≡ ε δ<ε))
      (summand-left<sum (quarter⁺ ε) (quarter⁺ ε))
