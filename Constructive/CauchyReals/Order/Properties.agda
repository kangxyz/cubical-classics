{-# OPTIONS --safe #-}

module Constructive.CauchyReals.Order.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.CauchyReals.Arithmetic.Addition
open import Constructive.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.CauchyReals.Arithmetic.Lattice
open import Constructive.CauchyReals.Arithmetic.Negation
open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Closeness.Properties
open import Constructive.CauchyReals.Continuity
open import Constructive.CauchyReals.Extension.Properties
open import Constructive.CauchyReals.Order.Base
open import Constructive.CauchyReals.PositiveRationals


private
  min-right-path :
    (q r : ℚ) →
    r ℚOrder.≤ q →
    ℚ.min q r ≡ r
  min-right-path q r r≤q =
    ℚ.minComm q r ∙
    ℚOrder.≤→min r q r≤q

  min-translate-right :
    (q r s : ℚ) →
    ℚ.min q r ℚ.+ s ≡ ℚ.min (q ℚ.+ s) (r ℚ.+ s)
  min-translate-right q r s with q ℚOrder.≟ r
  ... | ℚOrder.lt q<r =
    cong (ℚ._+ s) (ℚOrder.≤→min q r (ℚOrder.<Weaken≤ q r q<r)) ∙
    sym
      (ℚOrder.≤→min
        (q ℚ.+ s)
        (r ℚ.+ s)
        (ℚOrder.≤-+o q r s (ℚOrder.<Weaken≤ q r q<r)))
  ... | ℚOrder.eq q≡r =
    cong (ℚ._+ s) (ℚOrder.≤→min q r (ℚOrder.≡Weaken≤ q r q≡r)) ∙
    sym
      (ℚOrder.≤→min
        (q ℚ.+ s)
        (r ℚ.+ s)
        (ℚOrder.≤-+o q r s (ℚOrder.≡Weaken≤ q r q≡r)))
  ... | ℚOrder.gt r<q =
    cong (ℚ._+ s) (min-right-path q r (ℚOrder.<Weaken≤ r q r<q)) ∙
    sym
      (min-right-path
        (q ℚ.+ s)
        (r ℚ.+ s)
        (ℚOrder.≤-+o r q s (ℚOrder.<Weaken≤ r q r<q)))

  translated-min-continuous :
    (q r : ℚ) →
    IsContinuous
      (λ z → (rational q +ᶜ z) ⊓ᶜ (rational r +ᶜ z))
  translated-min-continuous q r ε =
    δ , closeAt
    where
    δ : ℚ⁺
    δ = half⁺ ε

    closeAt :
      {x y : ℝᶜ} →
      x ∼[ δ ] y →
      ((rational q +ᶜ x) ⊓ᶜ (rational r +ᶜ x))
        ∼[ ε ]
      ((rational q +ᶜ y) ⊓ᶜ (rational r +ᶜ y))
    closeAt {x = x} {y = y} x∼y =
      subst
        (λ ρ →
          ((rational q +ᶜ x) ⊓ᶜ (rational r +ᶜ x))
            ∼[ ρ ]
          ((rational q +ᶜ y) ⊓ᶜ (rational r +ᶜ y)))
        (half⁺+half⁺≡ ε)
        (min-close
          (add-close-right (rational q) x∼y)
          (add-close-right (rational r) x∼y))

  add-min-distrib-rational-rational-right :
    (q r : ℚ) (z : ℝᶜ) →
    (rational q ⊓ᶜ rational r) +ᶜ z ≡
    (rational q +ᶜ z) ⊓ᶜ (rational r +ᶜ z)
  add-min-distrib-rational-rational-right q r =
    continuous-equal
      (λ z → (rational q ⊓ᶜ rational r) +ᶜ z)
      (λ z → (rational q +ᶜ z) ⊓ᶜ (rational r +ᶜ z))
      (add-continuous-right (rational q ⊓ᶜ rational r))
      (translated-min-continuous q r)
      (λ s → cong rational (min-translate-right q r s))

  add-min-distrib-rational-left :
    (q : ℚ) (y z : ℝᶜ) →
    (rational q ⊓ᶜ y) +ᶜ z ≡
    (rational q +ᶜ z) ⊓ᶜ (y +ᶜ z)
  add-min-distrib-rational-left q y z =
    nonexpanding-equal
      (λ w → (rational q ⊓ᶜ w) +ᶜ z)
      (λ w → (rational q +ᶜ z) ⊓ᶜ (w +ᶜ z))
      (comp-nonexpanding
        (add-nonexpanding-left z)
        (min-nonexpanding-right (rational q)))
      (comp-nonexpanding
        (min-nonexpanding-right (rational q +ᶜ z))
        (add-nonexpanding-left z))
      (λ r → add-min-distrib-rational-rational-right q r z)
      y


add-min-distrib-right :
  (x y z : ℝᶜ) →
  (x ⊓ᶜ y) +ᶜ z ≡ (x +ᶜ z) ⊓ᶜ (y +ᶜ z)
add-min-distrib-right x y z =
  nonexpanding-equal
    (λ w → (w ⊓ᶜ y) +ᶜ z)
    (λ w → (w +ᶜ z) ⊓ᶜ (y +ᶜ z))
    (comp-nonexpanding
      (add-nonexpanding-left z)
      (min-nonexpanding-left y))
    (comp-nonexpanding
      (min-nonexpanding-left (y +ᶜ z))
      (add-nonexpanding-left z))
    (λ q → add-min-distrib-rational-left q y z)
    x


addᶜ-pres≤ᶜ-right :
  {x y : ℝᶜ} →
  (z : ℝᶜ) →
  x ≤ᶜ y →
  (x +ᶜ z) ≤ᶜ (y +ᶜ z)
addᶜ-pres≤ᶜ-right {x = x} {y = y} z x≤y =
  sym (add-min-distrib-right x y z) ∙
  cong (_+ᶜ z) x≤y


addᶜ-pres≤ᶜ-left :
  {x y : ℝᶜ} →
  (z : ℝᶜ) →
  x ≤ᶜ y →
  (z +ᶜ x) ≤ᶜ (z +ᶜ y)
addᶜ-pres≤ᶜ-left {x = x} {y = y} z x≤y =
  subst2 _≤ᶜ_
    (add-comm x z)
    (add-comm y z)
    (addᶜ-pres≤ᶜ-right {x = x} {y = y} z x≤y)


addᶜ-reflect≤ᶜ-right :
  {x y : ℝᶜ} →
  (z : ℝᶜ) →
  (x +ᶜ z) ≤ᶜ (y +ᶜ z) →
  x ≤ᶜ y
addᶜ-reflect≤ᶜ-right {x = x} {y = y} z x+z≤y+z =
  subst2 _≤ᶜ_
    (plus-minus-cancel-right x z)
    (plus-minus-cancel-right y z)
    (addᶜ-pres≤ᶜ-right {x = x +ᶜ z} {y = y +ᶜ z} (-ᶜ z) x+z≤y+z)


addᶜ-reflect≤ᶜ-left :
  {x y : ℝᶜ} →
  (z : ℝᶜ) →
  (z +ᶜ x) ≤ᶜ (z +ᶜ y) →
  x ≤ᶜ y
addᶜ-reflect≤ᶜ-left {x = x} {y = y} z z+x≤z+y =
  addᶜ-reflect≤ᶜ-right {x = x} {y = y} z
    (subst2 _≤ᶜ_
      (add-comm z x)
      (add-comm z y)
      z+x≤z+y)
