{-

Part of Constructive.Analysis.Reals.PowerSeries.CauchyProduct

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Algebra where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( addPowerSeries
    ; constantPowerSeries
    ; negPowerSeries
    ; rationalScalePowerSeries
    ; shiftPowerSeries
    ; subPowerSeries
    ; zeroPowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Core

cauchyProductPowerSeries-zero :
  (a b : PowerSeries) →
  cauchyProductPowerSeries a b zero ≡ a zero ·ᶜ b zero
cauchyProductPowerSeries-zero a b =
  refl


cauchyProductPowerSeries-suc :
  (a b : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a b (suc n) ≡
  a zero ·ᶜ b (suc n) +ᶜ
  cauchyProductPowerSeries (shiftPowerSeries a) b n
cauchyProductPowerSeries-suc a b n =
  refl


cauchyProductPowerSeries-suc-right :
  (a b : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a b (suc n) ≡
  cauchyProductPowerSeries a (shiftPowerSeries b) n +ᶜ
  a (suc n) ·ᶜ b zero
cauchyProductPowerSeries-suc-right a b zero =
  refl
cauchyProductPowerSeries-suc-right a b (suc n) =
  cong
    (a zero ·ᶜ b (suc (suc n)) +ᶜ_)
    (cauchyProductPowerSeries-suc-right (shiftPowerSeries a) b n) ∙
  add-assoc
    (a zero ·ᶜ b (suc (suc n)))
    (cauchyProductPowerSeries (shiftPowerSeries a) (shiftPowerSeries b) n)
    (a (suc (suc n)) ·ᶜ b zero)


cauchyProductPowerSeries-cong :
  {a b c d : PowerSeries} →
  ((n : ℕ) → a n ≡ c n) →
  ((n : ℕ) → b n ≡ d n) →
  (n : ℕ) →
  cauchyProductPowerSeries a b n ≡
  cauchyProductPowerSeries c d n
cauchyProductPowerSeries-cong a≡c b≡d zero =
  cong₂ _·ᶜ_ (a≡c zero) (b≡d zero)
cauchyProductPowerSeries-cong {a = a} {b = b} {c = c} {d = d} a≡c b≡d (suc n) =
  cong₂
    _+ᶜ_
    (cong₂ _·ᶜ_ (a≡c zero) (b≡d (suc n)))
    (cauchyProductPowerSeries-cong
      (λ k → a≡c (suc k))
      b≡d
      n)


cauchyProductPowerSeries-cong-left :
  {a b c : PowerSeries} →
  ((n : ℕ) → a n ≡ c n) →
  (n : ℕ) →
  cauchyProductPowerSeries a b n ≡
  cauchyProductPowerSeries c b n
cauchyProductPowerSeries-cong-left a≡c =
  cauchyProductPowerSeries-cong a≡c (λ _ → refl)


cauchyProductPowerSeries-cong-right :
  {a b d : PowerSeries} →
  ((n : ℕ) → b n ≡ d n) →
  (n : ℕ) →
  cauchyProductPowerSeries a b n ≡
  cauchyProductPowerSeries a d n
cauchyProductPowerSeries-cong-right b≡d =
  cauchyProductPowerSeries-cong (λ _ → refl) b≡d


cauchyProductPowerSeries-zero-left :
  (b : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries zeroPowerSeries b n ≡ 0ᶜ
cauchyProductPowerSeries-zero-left b zero =
  mulᶜ-zero-left (b zero)
cauchyProductPowerSeries-zero-left b (suc n) =
  cong₂
    _+ᶜ_
    (mulᶜ-zero-left (b (suc n)))
    (cauchyProductPowerSeries-cong-left
      (λ _ → refl)
      n ∙
    cauchyProductPowerSeries-zero-left b n) ∙
  add-zero-left 0ᶜ


cauchyProductPowerSeries-zero-right :
  (a : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a zeroPowerSeries n ≡ 0ᶜ
cauchyProductPowerSeries-zero-right a zero =
  mulᶜ-zero-right (a zero)
cauchyProductPowerSeries-zero-right a (suc n) =
  cong₂
    _+ᶜ_
    (mulᶜ-zero-right (a zero))
    (cauchyProductPowerSeries-zero-right (shiftPowerSeries a) n) ∙
  add-zero-left 0ᶜ


cauchyProductPowerSeries-constant-left :
  (c : ℝᶜ) →
  (a : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries (constantPowerSeries c) a n ≡ c ·ᶜ a n
cauchyProductPowerSeries-constant-left c a zero =
  refl
cauchyProductPowerSeries-constant-left c a (suc n) =
  cong
    (c ·ᶜ a (suc n) +ᶜ_)
    (cauchyProductPowerSeries-cong-left
      {a = shiftPowerSeries (constantPowerSeries c)}
      {b = a}
      {c = zeroPowerSeries}
      (λ _ → refl)
      n ∙
    cauchyProductPowerSeries-zero-left a n) ∙
  add-zero-right (c ·ᶜ a (suc n))


cauchyProductPowerSeries-one-left :
  (a : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries (constantPowerSeries 1ᶜ) a n ≡ a n
cauchyProductPowerSeries-one-left a n =
  cauchyProductPowerSeries-constant-left 1ᶜ a n ∙
  mulᶜ-one-left (a n)


private
  mulᶜ-neg-left :
    (x y : ℝᶜ) →
    (-ᶜ x) ·ᶜ y ≡ -ᶜ (x ·ᶜ y)
  mulᶜ-neg-left x y =
    mulᶜ-comm (-ᶜ x) y ∙
    mulᶜ-neg-right y x ∙
    cong -ᶜ_ (mulᶜ-comm y x)


cauchyProductPowerSeries-comm :
  (a b : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a b n ≡
  cauchyProductPowerSeries b a n
cauchyProductPowerSeries-comm a b zero =
  mulᶜ-comm (a zero) (b zero)
cauchyProductPowerSeries-comm a b (suc n) =
  cauchyProductPowerSeries-suc-right a b n ∙
  cong₂
    _+ᶜ_
    (cauchyProductPowerSeries-comm a (shiftPowerSeries b) n)
    (mulᶜ-comm (a (suc n)) (b zero)) ∙
  add-comm
    (cauchyProductPowerSeries (shiftPowerSeries b) a n)
    (b zero ·ᶜ a (suc n))


cauchyProductPowerSeries-constant-right :
  (c : ℝᶜ) →
  (a : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a (constantPowerSeries c) n ≡ a n ·ᶜ c
cauchyProductPowerSeries-constant-right c a n =
  cauchyProductPowerSeries-comm a (constantPowerSeries c) n ∙
  cauchyProductPowerSeries-constant-left c a n ∙
  mulᶜ-comm c (a n)


cauchyProductPowerSeries-one-right :
  (a : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a (constantPowerSeries 1ᶜ) n ≡ a n
cauchyProductPowerSeries-one-right a n =
  cauchyProductPowerSeries-constant-right 1ᶜ a n ∙
  mulᶜ-one-right (a n)


cauchyProductPowerSeries-add-left :
  (a b c : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries (addPowerSeries a b) c n ≡
  cauchyProductPowerSeries a c n +ᶜ
  cauchyProductPowerSeries b c n
cauchyProductPowerSeries-add-left a b c zero =
  mulᶜ-distrib-left (a zero) (b zero) (c zero)
cauchyProductPowerSeries-add-left a b c (suc n) =
  cong₂
    _+ᶜ_
    (mulᶜ-distrib-left (a zero) (b zero) (c (suc n)))
    (cauchyProductPowerSeries-cong-left
      (λ _ → refl)
      n ∙
    cauchyProductPowerSeries-add-left
      (shiftPowerSeries a)
      (shiftPowerSeries b)
      c
      n) ∙
  add-interchange
    (a zero ·ᶜ c (suc n))
    (b zero ·ᶜ c (suc n))
    (cauchyProductPowerSeries (shiftPowerSeries a) c n)
    (cauchyProductPowerSeries (shiftPowerSeries b) c n)


cauchyProductPowerSeries-add-right :
  (a b c : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a (addPowerSeries b c) n ≡
  cauchyProductPowerSeries a b n +ᶜ
  cauchyProductPowerSeries a c n
cauchyProductPowerSeries-add-right a b c n =
  cauchyProductPowerSeries-comm a (addPowerSeries b c) n ∙
  cauchyProductPowerSeries-add-left b c a n ∙
  cong₂
    _+ᶜ_
    (cauchyProductPowerSeries-comm b a n)
    (cauchyProductPowerSeries-comm c a n)


cauchyProductPowerSeries-neg-left :
  (a b : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries (negPowerSeries a) b n ≡
  negPowerSeries (cauchyProductPowerSeries a b) n
cauchyProductPowerSeries-neg-left a b zero =
  mulᶜ-neg-left (a zero) (b zero)
cauchyProductPowerSeries-neg-left a b (suc n) =
  cong₂
    _+ᶜ_
    (mulᶜ-neg-left (a zero) (b (suc n)))
    (cauchyProductPowerSeries-cong-left
      (λ _ → refl)
      n ∙
    cauchyProductPowerSeries-neg-left (shiftPowerSeries a) b n) ∙
  sym
    (neg-add
      (a zero ·ᶜ b (suc n))
      (cauchyProductPowerSeries (shiftPowerSeries a) b n))


cauchyProductPowerSeries-neg-right :
  (a b : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a (negPowerSeries b) n ≡
  negPowerSeries (cauchyProductPowerSeries a b) n
cauchyProductPowerSeries-neg-right a b n =
  cauchyProductPowerSeries-comm a (negPowerSeries b) n ∙
  cauchyProductPowerSeries-neg-left b a n ∙
  cong -ᶜ_ (cauchyProductPowerSeries-comm b a n)


cauchyProductPowerSeries-sub-left :
  (a b c : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries (subPowerSeries a b) c n ≡
  subPowerSeries
    (cauchyProductPowerSeries a c)
    (cauchyProductPowerSeries b c)
    n
cauchyProductPowerSeries-sub-left a b c n =
  cauchyProductPowerSeries-add-left a (negPowerSeries b) c n ∙
  cong
    (cauchyProductPowerSeries a c n +ᶜ_)
    (cauchyProductPowerSeries-neg-left b c n)


cauchyProductPowerSeries-sub-right :
  (a b c : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a (subPowerSeries b c) n ≡
  subPowerSeries
    (cauchyProductPowerSeries a b)
    (cauchyProductPowerSeries a c)
    n
cauchyProductPowerSeries-sub-right a b c n =
  cauchyProductPowerSeries-add-right a b (negPowerSeries c) n ∙
  cong
    (cauchyProductPowerSeries a b n +ᶜ_)
    (cauchyProductPowerSeries-neg-right a c n)


cauchyProductPowerSeries-rationalScale-left :
  (q : ℚ) →
  (a b : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries (rationalScalePowerSeries q a) b n ≡
  rationalScalePowerSeries q (cauchyProductPowerSeries a b) n
cauchyProductPowerSeries-rationalScale-left q a b zero =
  sym (mulᶜ-assoc-rational-left q (a zero) (b zero))
cauchyProductPowerSeries-rationalScale-left q a b (suc n) =
  cong₂
    _+ᶜ_
    (sym (mulᶜ-assoc-rational-left q (a zero) (b (suc n))))
    (cauchyProductPowerSeries-cong-left
      (λ _ → refl)
      n ∙
    cauchyProductPowerSeries-rationalScale-left
      q
      (shiftPowerSeries a)
      b
      n) ∙
  sym
    (mulᶜ-distrib-rational-left
      q
      (a zero ·ᶜ b (suc n))
      (cauchyProductPowerSeries (shiftPowerSeries a) b n))


cauchyProductPowerSeries-rationalScale-right :
  (q : ℚ) →
  (a b : PowerSeries) →
  (n : ℕ) →
  cauchyProductPowerSeries a (rationalScalePowerSeries q b) n ≡
  rationalScalePowerSeries q (cauchyProductPowerSeries a b) n
cauchyProductPowerSeries-rationalScale-right q a b n =
  cauchyProductPowerSeries-comm a (rationalScalePowerSeries q b) n ∙
  cauchyProductPowerSeries-rationalScale-left q b a n ∙
  cong
    (rational q ·ᶜ_)
    (cauchyProductPowerSeries-comm b a n)
