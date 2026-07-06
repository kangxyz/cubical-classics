{-

Order interaction for rational scalar multiplication

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Arithmetic.ScalarOrder where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.CauchyReals.Arithmetic.Lattice
open import Constructive.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Continuity
open import Constructive.CauchyReals.Extension
open import Constructive.CauchyReals.Order.Base
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


private
  min-right-path :
    (q r : ℚ) →
    r ℚOrder.≤ q →
    ℚ.min q r ≡ r
  min-right-path q r r≤q =
    ℚ.minComm q r ∙
    ℚOrder.≤→min r q r≤q

  scale-left-nonnegative-≤ :
    (a q r : ℚ) →
    0ℚ ℚOrder.≤ a →
    q ℚOrder.≤ r →
    a ℚ.· q ℚOrder.≤ a ℚ.· r
  scale-left-nonnegative-≤ a q r 0≤a q≤r =
    subst2
      ℚOrder._≤_
      (ℚ.·Comm q a)
      (ℚ.·Comm r a)
      (ℚOrder.≤-·o q r a 0≤a q≤r)

  scale-min-nonnegative :
    (a q r : ℚ) →
    0ℚ ℚOrder.≤ a →
    a ℚ.· ℚ.min q r ≡ ℚ.min (a ℚ.· q) (a ℚ.· r)
  scale-min-nonnegative a q r 0≤a with q ℚOrder.≟ r
  ... | ℚOrder.lt q<r =
    cong (a ℚ.·_) (ℚOrder.≤→min q r (Rational.<→≤ {p = q} {q = r} q<r)) ∙
    sym
      (ℚOrder.≤→min
        (a ℚ.· q)
        (a ℚ.· r)
        (scale-left-nonnegative-≤ a q r 0≤a
          (Rational.<→≤ {p = q} {q = r} q<r)))
  ... | ℚOrder.eq q≡r =
    cong (a ℚ.·_) (ℚOrder.≤→min q r (ℚOrder.≡Weaken≤ q r q≡r)) ∙
    sym
      (ℚOrder.≤→min
        (a ℚ.· q)
        (a ℚ.· r)
        (ℚOrder.≡Weaken≤
          (a ℚ.· q)
          (a ℚ.· r)
          (cong (a ℚ.·_) q≡r)))
  ... | ℚOrder.gt r<q =
    cong (a ℚ.·_) (min-right-path q r (Rational.<→≤ {p = r} {q = q} r<q)) ∙
    sym
      (min-right-path
        (a ℚ.· q)
        (a ℚ.· r)
        (scale-left-nonnegative-≤ a r q 0≤a
          (Rational.<→≤ {p = r} {q = q} r<q)))


scalarMulᶜ-min-nonnegative-rational-left :
  (a q : ℚ) →
  0ℚ ℚOrder.≤ a →
  (y : ℝᶜ) →
  scalarMulᶜ a (rational q ⊓ᶜ y) ≡
  scalarMulᶜ a (rational q) ⊓ᶜ scalarMulᶜ a y
scalarMulᶜ-min-nonnegative-rational-left a q 0≤a =
  continuous-equal
    (λ y → scalarMulᶜ a (rational q ⊓ᶜ y))
    (λ y → scalarMulᶜ a (rational q) ⊓ᶜ scalarMulᶜ a y)
    (comp-continuous
      (scalarMulᶜ-continuous a)
      (min-continuous-right (rational q)))
    (comp-continuous
      (min-continuous-right (scalarMulᶜ a (rational q)))
      (scalarMulᶜ-continuous a))
    (λ r → cong rational (scale-min-nonnegative a q r 0≤a))


scalarMulᶜ-min-nonnegative :
  (a : ℚ) →
  0ℚ ℚOrder.≤ a →
  (x y : ℝᶜ) →
  scalarMulᶜ a (x ⊓ᶜ y) ≡
  scalarMulᶜ a x ⊓ᶜ scalarMulᶜ a y
scalarMulᶜ-min-nonnegative a 0≤a x y =
  continuous-equal
    (λ z → scalarMulᶜ a (z ⊓ᶜ y))
    (λ z → scalarMulᶜ a z ⊓ᶜ scalarMulᶜ a y)
    (comp-continuous
      (scalarMulᶜ-continuous a)
      (min-continuous-left y))
    (comp-continuous
      (min-continuous-left (scalarMulᶜ a y))
      (scalarMulᶜ-continuous a))
    (λ q → scalarMulᶜ-min-nonnegative-rational-left a q 0≤a y)
    x


scalarMulᶜ-pres≤ᶜ-nonnegative :
  (a : ℚ) →
  0ℚ ℚOrder.≤ a →
  {x y : ℝᶜ} →
  x ≤ᶜ y →
  scalarMulᶜ a x ≤ᶜ scalarMulᶜ a y
scalarMulᶜ-pres≤ᶜ-nonnegative a 0≤a {x = x} {y = y} x≤y =
  sym (scalarMulᶜ-min-nonnegative a 0≤a x y) ∙
  cong (scalarMulᶜ a) x≤y
