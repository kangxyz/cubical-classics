{-# OPTIONS --safe #-}

module Constructive.CauchyReals.Order.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Pseudolattice

open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Arithmetic.Base
open import Constructive.CauchyReals.Arithmetic.Lattice
open import Constructive.CauchyReals.Closeness

infix 4 _≤ᶜ_ _≥ᶜ_

_≤ᶜ_ : ℝᶜ → ℝᶜ → Type₀
x ≤ᶜ y = x ⊓ᶜ y ≡ x

_≥ᶜ_ : ℝᶜ → ℝᶜ → Type₀
x ≥ᶜ y = y ≤ᶜ x

isProp≤ᶜ : (x y : ℝᶜ) → isProp (x ≤ᶜ y)
isProp≤ᶜ x y = isSetℝᶜ (x ⊓ᶜ y) x

≤ᶜ-refl : (x : ℝᶜ) → x ≤ᶜ x
≤ᶜ-refl = min-idem

≤ᶜ-antisym : {x y : ℝᶜ} → x ≤ᶜ y → y ≤ᶜ x → x ≡ y
≤ᶜ-antisym {x = x} {y = y} x≤y y≤x =
  sym x≤y ∙ min-comm x y ∙ y≤x

≤ᶜ-trans : {x y z : ℝᶜ} → x ≤ᶜ y → y ≤ᶜ z → x ≤ᶜ z
≤ᶜ-trans {x = x} {y = y} {z = z} x≤y y≤z =
  cong (_⊓ᶜ z) (sym x≤y) ∙
  sym (min-assoc x y z) ∙
  cong (x ⊓ᶜ_) y≤z ∙
  x≤y

≤ᶜ→maxᶜ : {x y : ℝᶜ} → x ≤ᶜ y → x ⊔ᶜ y ≡ y
≤ᶜ→maxᶜ {x = x} {y = y} x≤y =
  max-comm x y ∙
  cong (y ⊔ᶜ_) (sym (min-comm y x ∙ x≤y)) ∙
  max-absorb-min y x

maxᶜ→≤ᶜ : {x y : ℝᶜ} → x ⊔ᶜ y ≡ y → x ≤ᶜ y
maxᶜ→≤ᶜ {x = x} {y = y} x⊔y≡y =
  cong (x ⊓ᶜ_) (sym x⊔y≡y) ∙
  min-absorb-max x y

⊓ᶜ≤left : (x y : ℝᶜ) → (x ⊓ᶜ y) ≤ᶜ x
⊓ᶜ≤left x y =
  sym (min-assoc x y x) ∙
  cong (x ⊓ᶜ_) (min-comm y x) ∙
  min-assoc x x y ∙
  cong (_⊓ᶜ y) (min-idem x)

⊓ᶜ≤right : (x y : ℝᶜ) → (x ⊓ᶜ y) ≤ᶜ y
⊓ᶜ≤right x y =
  cong (_⊓ᶜ y) (min-comm x y) ∙
  ⊓ᶜ≤left y x ∙
  sym (min-comm x y)

≤ᶜ⊓ᶜ : {x y z : ℝᶜ} → z ≤ᶜ x → z ≤ᶜ y → z ≤ᶜ (x ⊓ᶜ y)
≤ᶜ⊓ᶜ {x = x} {y = y} {z = z} z≤x z≤y =
  min-assoc z x y ∙
  cong (_⊓ᶜ y) z≤x ∙
  z≤y

left≤ᶜ⊔ᶜ : (x y : ℝᶜ) → x ≤ᶜ (x ⊔ᶜ y)
left≤ᶜ⊔ᶜ = min-absorb-max

right≤ᶜ⊔ᶜ : (x y : ℝᶜ) → y ≤ᶜ (x ⊔ᶜ y)
right≤ᶜ⊔ᶜ x y =
  cong (y ⊓ᶜ_) (max-comm x y) ∙
  min-absorb-max y x

⊔ᶜ≤ᶜ : {x y z : ℝᶜ} → x ≤ᶜ z → y ≤ᶜ z → (x ⊔ᶜ y) ≤ᶜ z
⊔ᶜ≤ᶜ {x = x} {y = y} {z = z} x≤z y≤z =
  maxᶜ→≤ᶜ {x = x ⊔ᶜ y} {y = z}
    (sym (max-assoc x y z) ∙
     cong (x ⊔ᶜ_) (≤ᶜ→maxᶜ {x = y} {y = z} y≤z) ∙
     ≤ᶜ→maxᶜ {x = x} {y = z} x≤z)

CauchyReals≤Poset : Poset ℓ-zero ℓ-zero
CauchyReals≤Poset =
  poset ℝᶜ _≤ᶜ_
    (isposet isSetℝᶜ isProp≤ᶜ ≤ᶜ-refl
      (λ x y z → ≤ᶜ-trans {x = x} {y = y} {z = z})
      (λ x y → ≤ᶜ-antisym {x = x} {y = y}))

CauchyReals≤Pseudolattice : Pseudolattice ℓ-zero ℓ-zero
CauchyReals≤Pseudolattice =
  makePseudolatticeFromPoset CauchyReals≤Poset _⊓ᶜ_ _⊔ᶜ_
    (λ {a} {b} → ⊓ᶜ≤left a b)
    (λ {a} {b} → ⊓ᶜ≤right a b)
    (λ {a} {b} {c} → ≤ᶜ⊓ᶜ {x = a} {y = b} {z = c})
    (λ {a} {b} → left≤ᶜ⊔ᶜ a b)
    (λ {a} {b} → right≤ᶜ⊔ᶜ a b)
    (λ {a} {b} {c} → ⊔ᶜ≤ᶜ {x = a} {y = b} {z = c})
