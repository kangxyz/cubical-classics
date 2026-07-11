{-# OPTIONS --safe #-}

module Constructive.Analysis.Reals.CauchyReals.Order.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Lattice
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Instances.Rationals
open ClosenessOf RationalsMetricSpace
open ComputedOf RationalsMetricSpace
open RoundedOf RationalsMetricSpace
open import Constructive.Analysis.Metric.Map
open import Constructive.Analysis.Reals.CauchyReals.Metric
open import Constructive.Analysis.Reals.CauchyReals.Extension
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Data.PositiveRationals


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
    IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace
      (λ z → (rational q +ᶜ z) ⊓ᶜ (rational r +ᶜ z))
  translated-min-continuous q r =
    (λ ε → half⁺ ε) , closeAt
    where
    closeAt :
      (ε : ℚ⁺) →
      {x y : ℝᶜ} →
      x ∼[ half⁺ ε ] y →
      ((rational q +ᶜ x) ⊓ᶜ (rational r +ᶜ x))
        ∼[ ε ]
      ((rational q +ᶜ y) ⊓ᶜ (rational r +ᶜ y))
    closeAt ε {x = x} {y = y} x∼y =
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
      (comp-nonexpanding {𝓧 = CauchyRealsMetricSpace} {𝓨 = CauchyRealsMetricSpace} {𝓩 = CauchyRealsMetricSpace}
        (add-nonexpanding-left z)
        (min-nonexpanding-right (rational q)))
      (comp-nonexpanding {𝓧 = CauchyRealsMetricSpace} {𝓨 = CauchyRealsMetricSpace} {𝓩 = CauchyRealsMetricSpace}
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
    (comp-nonexpanding {𝓧 = CauchyRealsMetricSpace} {𝓨 = CauchyRealsMetricSpace} {𝓩 = CauchyRealsMetricSpace}
      (add-nonexpanding-left z)
      (min-nonexpanding-left y))
    (comp-nonexpanding {𝓧 = CauchyRealsMetricSpace} {𝓨 = CauchyRealsMetricSpace} {𝓩 = CauchyRealsMetricSpace}
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
