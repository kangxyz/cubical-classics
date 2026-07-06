{-

Closeness of rational approximants

-}
{-# OPTIONS --safe #-}
module Constructive.Data.Rationals.Closeness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁)

open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

private
  negative-sum :
    (q r : ℚ) →
    ℚ.- (q ℚ.+ r) ≡ (ℚ.- q) ℚ.+ (ℚ.- r)
  negative-sum q r =
    ℚ.·DistL+ -1 q r

  negative-difference :
    (q r : ℚ) →
    (ℚ.- q) ℚ.- (ℚ.- r) ≡ r ℚ.- q
  negative-difference q r =
    cong ((ℚ.- q) ℚ.+_) (ℚ.-Invol r) ∙
    ℚ.+Comm (ℚ.- q) r

  translate-difference :
    (q r s : ℚ) →
    (q ℚ.+ s) ℚ.- (r ℚ.+ s) ≡ q ℚ.- r
  translate-difference q r s =
    ℚ.+CancelR
      ((q ℚ.+ s) ℚ.- (r ℚ.+ s))
      s
      (q ℚ.- r)
      (sym (ℚ.+Assoc (q ℚ.+ s) (ℚ.- (r ℚ.+ s)) s) ∙
       cong ((q ℚ.+ s) ℚ.+_)
         (cong (λ t → t ℚ.+ s) (negative-sum r s) ∙
          sym (ℚ.+Assoc (ℚ.- r) (ℚ.- s) s) ∙
          cong ((ℚ.- r) ℚ.+_) (ℚ.+InvL s) ∙
          ℚ.+IdR (ℚ.- r)) ∙
       sym (ℚ.+Assoc q s (ℚ.- r)) ∙
       cong (q ℚ.+_) (ℚ.+Comm s (ℚ.- r)) ∙
       ℚ.+Assoc q (ℚ.- r) s)

  difference-triangle :
    (q r s : ℚ) →
    q ℚ.- s ≡ (q ℚ.- r) ℚ.+ (r ℚ.- s)
  difference-triangle q r s =
    sym
      (sym (ℚ.+Assoc q (ℚ.- r) (r ℚ.- s)) ∙
       cong (q ℚ.+_)
         (ℚ.+Assoc (ℚ.- r) r (ℚ.- s) ∙
          cong (λ t → t ℚ.+ (ℚ.- s)) (ℚ.+InvL r) ∙
          ℚ.+IdL (ℚ.- s)))


Closeℚ : ℚ → ℚ⁺ → ℚ → Type₀
Closeℚ q ε r =
  (q ℚ.- r ℚOrder.< radius ε) ×
  (r ℚ.- q ℚOrder.< radius ε)


isPropCloseℚ : (q : ℚ) (ε : ℚ⁺) (r : ℚ) → isProp (Closeℚ q ε r)
isPropCloseℚ q ε r =
  isProp×
    (ℚOrder.isProp< (q ℚ.- r) (radius ε))
    (ℚOrder.isProp< (r ℚ.- q) (radius ε))


rational-close-refl : (q : ℚ) (ε : ℚ⁺) → Closeℚ q ε q
rational-close-refl q ε =
  subst (λ r → r ℚOrder.< radius ε) (sym (ℚ.+InvR q)) (ε .snd) ,
  subst (λ r → r ℚOrder.< radius ε) (sym (ℚ.+InvR q)) (ε .snd)


rational-close-sym :
  (q r : ℚ) (ε : ℚ⁺) →
  Closeℚ q ε r →
  Closeℚ r ε q
rational-close-sym q r ε q∼r =
  q∼r .snd , q∼r .fst


rational-close-mono :
  (q r : ℚ) (ε δ : ℚ⁺) →
  ε <⁺ δ →
  Closeℚ q ε r →
  Closeℚ q δ r
rational-close-mono q r ε δ ε<δ q∼r =
  ℚOrder.isTrans< (q ℚ.- r) (radius ε) (radius δ) (q∼r .fst) ε<δ ,
  ℚOrder.isTrans< (r ℚ.- q) (radius ε) (radius δ) (q∼r .snd) ε<δ


rational-close-triangle :
  (q r s : ℚ) (ε δ : ℚ⁺) →
  Closeℚ q ε r →
  Closeℚ r δ s →
  Closeℚ q (ε +⁺ δ) s
rational-close-triangle q r s ε δ q∼r r∼s =
  subst
    (λ t → t ℚOrder.< radius (ε +⁺ δ))
    (sym (difference-triangle q r s))
    (ℚOrder.<Monotone+ (q ℚ.- r) (radius ε) (r ℚ.- s) (radius δ)
      (q∼r .fst)
      (r∼s .fst)) ,
  subst
    (λ t → t ℚOrder.< radius (ε +⁺ δ))
    (sym (difference-triangle s r q))
    (subst
      ((s ℚ.- r) ℚ.+ (r ℚ.- q) ℚOrder.<_)
      (ℚ.+Comm (radius δ) (radius ε))
      (ℚOrder.<Monotone+ (s ℚ.- r) (radius δ) (r ℚ.- q) (radius ε)
        (r∼s .snd)
        (q∼r .snd)))


rational-close-rounded :
  (q r : ℚ) (ε : ℚ⁺) →
  Closeℚ q ε r →
  ∥ Σ[ δ ∈ ℚ⁺ ] (δ <⁺ ε) × Closeℚ q δ r ∥₁
rational-close-rounded q r ε q∼r =
  Prop.map rounded (Rational.dense {p = lowerBound} {q = radius ε} lower<ε)
  where
  a b m lowerBound : ℚ
  a = q ℚ.- r
  b = r ℚ.- q
  m = ℚ.max a b
  lowerBound = ℚ.max 0ℚ m

  m<ε : m ℚOrder.< radius ε
  m<ε = Rational.max< {r = a} {s = b} {q = radius ε} (q∼r .fst) (q∼r .snd)

  lower<ε : lowerBound ℚOrder.< radius ε
  lower<ε = Rational.max< {r = 0ℚ} {s = m} {q = radius ε} (ε .snd) m<ε

  0≤lower : 0ℚ ℚOrder.≤ lowerBound
  0≤lower = ℚOrder.≤max 0ℚ m

  a≤lower : a ℚOrder.≤ lowerBound
  a≤lower =
    ℚOrder.isTrans≤ a m lowerBound
      (ℚOrder.≤max a b)
      (Rational.≤max-r 0ℚ m)

  b≤lower : b ℚOrder.≤ lowerBound
  b≤lower =
    ℚOrder.isTrans≤ b m lowerBound
      (Rational.≤max-r a b)
      (Rational.≤max-r 0ℚ m)

  rounded :
    Σ[ δ ∈ ℚ ] (lowerBound ℚOrder.< δ) × (δ ℚOrder.< radius ε) →
    Σ[ δ ∈ ℚ⁺ ] (δ <⁺ ε) × Closeℚ q δ r
  rounded (δ , lower<δ , δ<ε) =
    (δ , ℚOrder.isTrans≤< 0ℚ lowerBound δ 0≤lower lower<δ)
    , δ<ε
    , ℚOrder.isTrans≤< a lowerBound δ a≤lower lower<δ
    , ℚOrder.isTrans≤< b lowerBound δ b≤lower lower<δ


rational-close-neg :
  (q r : ℚ) (ε : ℚ⁺) →
  Closeℚ q ε r →
  Closeℚ (ℚ.- q) ε (ℚ.- r)
rational-close-neg q r ε q∼r =
  subst
    (λ s → s ℚOrder.< radius ε)
    (sym (negative-difference q r))
    (q∼r .snd) ,
  subst
    (λ s → s ℚOrder.< radius ε)
    (sym (negative-difference r q))
    (q∼r .fst)


rational-close-translate :
  (q r s : ℚ) (ε : ℚ⁺) →
  Closeℚ q ε r →
  Closeℚ (q ℚ.+ s) ε (r ℚ.+ s)
rational-close-translate q r s ε q∼r =
  subst
    (λ t → t ℚOrder.< radius ε)
    (sym (translate-difference q r s))
    (q∼r .fst) ,
  subst
    (λ t → t ℚOrder.< radius ε)
    (sym (translate-difference r q s))
    (q∼r .snd)
