{-# OPTIONS --safe #-}

module Constructive.Analysis.Reals.CauchyReals.Order.Magnitude where

open import Cubical.Foundations.Prelude

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Lattice
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
