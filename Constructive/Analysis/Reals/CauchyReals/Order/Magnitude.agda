{-# OPTIONS --safe #-}

module Constructive.Analysis.Reals.CauchyReals.Order.Magnitude where

open import Cubical.Foundations.Prelude

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Lattice
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive


Nonnegativeᶜ : ℝᶜ → Type₀
Nonnegativeᶜ x = 0ᶜ ≤ᶜ x


Nonpositiveᶜ : ℝᶜ → Type₀
Nonpositiveᶜ x = x ≤ᶜ 0ᶜ


Positiveᶜ : ℝᶜ → Type₀
Positiveᶜ x = 0ᶜ <ᶜ x


Negativeᶜ : ℝᶜ → Type₀
Negativeᶜ x = x <ᶜ 0ᶜ


neg-zeroᶜ : -ᶜ 0ᶜ ≡ 0ᶜ
neg-zeroᶜ =
  inverse-unique-right 0ᶜ 0ᶜ (add-zero-right 0ᶜ)


raw-absᶜ : ℝᶜ → ℝᶜ
raw-absᶜ x = x ⊔ᶜ (-ᶜ x)


absᶜ : ℝᶜ → ℝᶜ
absᶜ x = 0ᶜ ⊔ᶜ raw-absᶜ x


absᶜ-nonnegative : (x : ℝᶜ) → Nonnegativeᶜ (absᶜ x)
absᶜ-nonnegative x =
  left≤ᶜ⊔ᶜ 0ᶜ (raw-absᶜ x)


left≤ᶜraw-absᶜ : (x : ℝᶜ) → x ≤ᶜ raw-absᶜ x
left≤ᶜraw-absᶜ x =
  left≤ᶜ⊔ᶜ x (-ᶜ x)


right≤ᶜraw-absᶜ : (x : ℝᶜ) → -ᶜ x ≤ᶜ raw-absᶜ x
right≤ᶜraw-absᶜ x =
  right≤ᶜ⊔ᶜ x (-ᶜ x)


≤ᶜabsᶜ-left : (x : ℝᶜ) → x ≤ᶜ absᶜ x
≤ᶜabsᶜ-left x =
  ≤ᶜ-trans
    {x = x}
    {y = raw-absᶜ x}
    {z = absᶜ x}
    (left≤ᶜraw-absᶜ x)
    (right≤ᶜ⊔ᶜ 0ᶜ (raw-absᶜ x))


≤ᶜabsᶜ-right : (x : ℝᶜ) → -ᶜ x ≤ᶜ absᶜ x
≤ᶜabsᶜ-right x =
  ≤ᶜ-trans
    {x = -ᶜ x}
    {y = raw-absᶜ x}
    {z = absᶜ x}
    (right≤ᶜraw-absᶜ x)
    (right≤ᶜ⊔ᶜ 0ᶜ (raw-absᶜ x))


absᶜ-least :
  (x u : ℝᶜ) →
  0ᶜ ≤ᶜ u →
  x ≤ᶜ u →
  -ᶜ x ≤ᶜ u →
  absᶜ x ≤ᶜ u
absᶜ-least x u 0≤u x≤u -x≤u =
  ⊔ᶜ≤ᶜ
    {x = 0ᶜ}
    {y = raw-absᶜ x}
    {z = u}
    0≤u
    (⊔ᶜ≤ᶜ {x = x} {y = -ᶜ x} {z = u} x≤u -x≤u)


raw-absᶜ-neg : (x : ℝᶜ) → raw-absᶜ (-ᶜ x) ≡ raw-absᶜ x
raw-absᶜ-neg x =
  cong ((-ᶜ x) ⊔ᶜ_) (neg-involutive x) ∙
  max-comm (-ᶜ x) x


absᶜ-neg : (x : ℝᶜ) → absᶜ (-ᶜ x) ≡ absᶜ x
absᶜ-neg x =
  cong (0ᶜ ⊔ᶜ_) (raw-absᶜ-neg x)


absᶜ-zero : absᶜ 0ᶜ ≡ 0ᶜ
absᶜ-zero =
  cong (λ x → 0ᶜ ⊔ᶜ (0ᶜ ⊔ᶜ x)) neg-zeroᶜ ∙
  cong (0ᶜ ⊔ᶜ_) (max-idem 0ᶜ) ∙
  max-idem 0ᶜ


nonnegativeᶜ-add :
  {x y : ℝᶜ} →
  Nonnegativeᶜ x →
  Nonnegativeᶜ y →
  Nonnegativeᶜ (x +ᶜ y)
nonnegativeᶜ-add {x = x} {y = y} 0≤x 0≤y =
  subst
    (λ w → w ≤ᶜ (x +ᶜ y))
    (add-zero-right 0ᶜ)
    (≤ᶜ-add
      {a = 0ᶜ}
      {b = x}
      {c = 0ᶜ}
      {d = y}
      0≤x
      0≤y)


absᶜ-triangle :
  (x y : ℝᶜ) →
  absᶜ (x +ᶜ y) ≤ᶜ (absᶜ x +ᶜ absᶜ y)
absᶜ-triangle x y =
  absᶜ-least
    (x +ᶜ y)
    (absᶜ x +ᶜ absᶜ y)
    (nonnegativeᶜ-add
      {x = absᶜ x}
      {y = absᶜ y}
      (absᶜ-nonnegative x)
      (absᶜ-nonnegative y))
    (≤ᶜ-add
      {a = x}
      {b = absᶜ x}
      {c = y}
      {d = absᶜ y}
      (≤ᶜabsᶜ-left x)
      (≤ᶜabsᶜ-left y))
    (subst
      (λ w → w ≤ᶜ (absᶜ x +ᶜ absᶜ y))
      (sym (neg-add x y))
      (≤ᶜ-add
        {a = -ᶜ x}
        {b = absᶜ x}
        {c = -ᶜ y}
        {d = absᶜ y}
        (≤ᶜabsᶜ-right x)
        (≤ᶜabsᶜ-right y)))


absᶜ-zero→zero :
  (x : ℝᶜ) →
  absᶜ x ≡ 0ᶜ →
  x ≡ 0ᶜ
absᶜ-zero→zero x absx≡0 =
  ≤ᶜ-antisym x≤0 0≤x
  where
  absx≤0 : absᶜ x ≤ᶜ 0ᶜ
  absx≤0 =
    subst
      (λ w → w ≤ᶜ 0ᶜ)
      (sym absx≡0)
      (≤ᶜ-refl 0ᶜ)

  x≤0 : x ≤ᶜ 0ᶜ
  x≤0 =
    ≤ᶜ-trans
      {x = x}
      {y = absᶜ x}
      {z = 0ᶜ}
      (≤ᶜabsᶜ-left x)
      absx≤0

  -x≤0 : -ᶜ x ≤ᶜ 0ᶜ
  -x≤0 =
    ≤ᶜ-trans
      {x = -ᶜ x}
      {y = absᶜ x}
      {z = 0ᶜ}
      (≤ᶜabsᶜ-right x)
      absx≤0

  0≤x : 0ᶜ ≤ᶜ x
  0≤x =
    subst2
      _≤ᶜ_
      neg-zeroᶜ
      (neg-involutive x)
      (negᶜ-pres≤ᶜ {x = -ᶜ x} {y = 0ᶜ} -x≤0)


distᶜ : ℝᶜ → ℝᶜ → ℝᶜ
distᶜ x y =
  absᶜ (x +ᶜ (-ᶜ y))


private
  difference-self :
    (x : ℝᶜ) →
    x +ᶜ (-ᶜ x) ≡ 0ᶜ
  difference-self =
    add-inverse-right

  difference-zero-right :
    (x : ℝᶜ) →
    x +ᶜ (-ᶜ 0ᶜ) ≡ x
  difference-zero-right x =
    cong (x +ᶜ_) neg-zeroᶜ ∙
    add-zero-right x

  difference-zero-left :
    (x : ℝᶜ) →
    0ᶜ +ᶜ (-ᶜ x) ≡ -ᶜ x
  difference-zero-left x =
    add-zero-left (-ᶜ x)

  difference-sym-neg :
    (x y : ℝᶜ) →
    x +ᶜ (-ᶜ y) ≡ -ᶜ (y +ᶜ (-ᶜ x))
  difference-sym-neg x y =
    add-comm x (-ᶜ y) ∙
    cong ((-ᶜ y) +ᶜ_) (sym (neg-involutive x)) ∙
    sym (neg-add y (-ᶜ x))

  difference-composite :
    (x y z : ℝᶜ) →
    x +ᶜ (-ᶜ z) ≡
    (x +ᶜ (-ᶜ y)) +ᶜ (y +ᶜ (-ᶜ z))
  difference-composite x y z =
    sym
      (add-assoc (x +ᶜ (-ᶜ y)) y (-ᶜ z) ∙
       cong (_+ᶜ (-ᶜ z)) (minus-plus-cancel-right x y))

  difference-zero→eq :
    (x y : ℝᶜ) →
    x +ᶜ (-ᶜ y) ≡ 0ᶜ →
    x ≡ y
  difference-zero→eq x y diff≡0 =
    sym (minus-plus-cancel-right x y) ∙
    cong (_+ᶜ y) diff≡0 ∙
    add-zero-left y


distᶜ-self :
  (x : ℝᶜ) →
  distᶜ x x ≡ 0ᶜ
distᶜ-self x =
  cong absᶜ (difference-self x) ∙
  absᶜ-zero


distᶜ-zero-right :
  (x : ℝᶜ) →
  distᶜ x 0ᶜ ≡ absᶜ x
distᶜ-zero-right x =
  cong absᶜ (difference-zero-right x)


distᶜ-zero-left :
  (x : ℝᶜ) →
  distᶜ 0ᶜ x ≡ absᶜ x
distᶜ-zero-left x =
  cong absᶜ (difference-zero-left x) ∙
  absᶜ-neg x


distᶜ-sym :
  (x y : ℝᶜ) →
  distᶜ x y ≡ distᶜ y x
distᶜ-sym x y =
  cong absᶜ (difference-sym-neg x y) ∙
  absᶜ-neg (y +ᶜ (-ᶜ x))


distᶜ-nonnegative :
  (x y : ℝᶜ) →
  0ᶜ ≤ᶜ distᶜ x y
distᶜ-nonnegative x y =
  absᶜ-nonnegative (x +ᶜ (-ᶜ y))


distᶜ-eq-zero :
  {x y : ℝᶜ} →
  x ≡ y →
  distᶜ x y ≡ 0ᶜ
distᶜ-eq-zero {x = x} p =
  cong (distᶜ x) (sym p) ∙
  distᶜ-self x


distᶜ-zero→eq :
  {x y : ℝᶜ} →
  distᶜ x y ≡ 0ᶜ →
  x ≡ y
distᶜ-zero→eq {x = x} {y = y} dist≡0 =
  difference-zero→eq x y
    (absᶜ-zero→zero (x +ᶜ (-ᶜ y)) dist≡0)


distᶜ-triangle :
  (x y z : ℝᶜ) →
  distᶜ x z ≤ᶜ (distᶜ x y +ᶜ distᶜ y z)
distᶜ-triangle x y z =
  subst
    (λ w → w ≤ᶜ (distᶜ x y +ᶜ distᶜ y z))
    (sym (cong absᶜ (difference-composite x y z)))
    (absᶜ-triangle (x +ᶜ (-ᶜ y)) (y +ᶜ (-ᶜ z)))
