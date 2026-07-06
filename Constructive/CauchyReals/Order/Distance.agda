{-# OPTIONS --safe #-}

module Constructive.CauchyReals.Order.Distance where

open import Cubical.Foundations.Prelude

open import Constructive.CauchyReals.Arithmetic.Addition
open import Constructive.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.CauchyReals.Arithmetic.Base
open import Constructive.CauchyReals.Arithmetic.Negation
open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Order.Base
open import Constructive.CauchyReals.Order.Magnitude


diffᶜ : ℝᶜ → ℝᶜ → ℝᶜ
diffᶜ x y = x +ᶜ (-ᶜ y)


distᶜ : ℝᶜ → ℝᶜ → ℝᶜ
distᶜ x y = absᶜ (diffᶜ x y)


diffᶜ-self : (x : ℝᶜ) → diffᶜ x x ≡ 0ᶜ
diffᶜ-self =
  add-inverse-right


distᶜ-self : (x : ℝᶜ) → distᶜ x x ≡ 0ᶜ
distᶜ-self x =
  cong absᶜ (diffᶜ-self x) ∙
  absᶜ-zero


diffᶜ-zero-right : (x : ℝᶜ) → diffᶜ x 0ᶜ ≡ x
diffᶜ-zero-right x =
  cong (x +ᶜ_) neg-zeroᶜ ∙
  add-zero-right x


distᶜ-zero-right : (x : ℝᶜ) → distᶜ x 0ᶜ ≡ absᶜ x
distᶜ-zero-right x =
  cong absᶜ (diffᶜ-zero-right x)


diffᶜ-zero-left : (x : ℝᶜ) → diffᶜ 0ᶜ x ≡ -ᶜ x
diffᶜ-zero-left x =
  add-zero-left (-ᶜ x)


distᶜ-zero-left : (x : ℝᶜ) → distᶜ 0ᶜ x ≡ absᶜ x
distᶜ-zero-left x =
  cong absᶜ (diffᶜ-zero-left x) ∙
  absᶜ-neg x


diffᶜ-sym-neg :
  (x y : ℝᶜ) →
  diffᶜ x y ≡ -ᶜ diffᶜ y x
diffᶜ-sym-neg x y =
  add-comm x (-ᶜ y) ∙
  cong ((-ᶜ y) +ᶜ_) (sym (neg-involutive x)) ∙
  sym (neg-add y (-ᶜ x))


distᶜ-sym : (x y : ℝᶜ) → distᶜ x y ≡ distᶜ y x
distᶜ-sym x y =
  cong absᶜ (diffᶜ-sym-neg x y) ∙
  absᶜ-neg (diffᶜ y x)


distᶜ-nonnegative : (x y : ℝᶜ) → 0ᶜ ≤ᶜ distᶜ x y
distᶜ-nonnegative x y =
  absᶜ-nonnegative (diffᶜ x y)


distᶜ-eq-zero :
  {x y : ℝᶜ} →
  x ≡ y →
  distᶜ x y ≡ 0ᶜ
distᶜ-eq-zero {x = x} p =
  cong (distᶜ x) (sym p) ∙
  distᶜ-self x


diffᶜ-composite :
  (x y z : ℝᶜ) →
  diffᶜ x z ≡ diffᶜ x y +ᶜ diffᶜ y z
diffᶜ-composite x y z =
  sym
    (add-assoc (x +ᶜ (-ᶜ y)) y (-ᶜ z) ∙
     cong (_+ᶜ (-ᶜ z)) (minus-plus-cancel-right x y))


diffᶜ-zero→eq :
  (x y : ℝᶜ) →
  diffᶜ x y ≡ 0ᶜ →
  x ≡ y
diffᶜ-zero→eq x y diff≡0 =
  sym (minus-plus-cancel-right x y) ∙
  cong (_+ᶜ y) diff≡0 ∙
  add-zero-left y


distᶜ-zero→eq :
  {x y : ℝᶜ} →
  distᶜ x y ≡ 0ᶜ →
  x ≡ y
distᶜ-zero→eq {x = x} {y = y} dist≡0 =
  diffᶜ-zero→eq x y
    (absᶜ-zero→zero (diffᶜ x y) dist≡0)


distᶜ-triangle :
  (x y z : ℝᶜ) →
  distᶜ x z ≤ᶜ (distᶜ x y +ᶜ distᶜ y z)
distᶜ-triangle x y z =
  subst
    (λ w → w ≤ᶜ (distᶜ x y +ᶜ distᶜ y z))
    (sym (cong absᶜ (diffᶜ-composite x y z)))
    (absᶜ-triangle (diffᶜ x y) (diffᶜ y z))
