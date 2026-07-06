{-

Addition on HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Arithmetic.Addition where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals as ℚ using (ℚ)

open import Constructive.CauchyReals.Arithmetic.Base
open import Constructive.CauchyReals.Arithmetic.Negation
open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Closeness
open import Constructive.CauchyReals.Continuity
open import Constructive.CauchyReals.Extension
open import Constructive.CauchyReals.Induction


private
  rational-add : ℚ → ℚ → ℝᶜ
  rational-add q r =
    rational (q ℚ.+ r)

  rational-close-translate-left :
    (q r s : ℚ) (ε : ℚ⁺) →
    Closeℚ r ε s →
    Closeℚ (q ℚ.+ r) ε (q ℚ.+ s)
  rational-close-translate-left q r s ε r∼s =
    subst2
      (λ a b → Closeℚ a ε b)
      (ℚ.+Comm r q)
      (ℚ.+Comm s q)
      (rational-close-translate r s q ε r∼s)

  add-left-ne : IsBinaryRationalNonexpandingLeft rational-add
  add-left-ne q r s ε q∼r =
    point-point-close
      (q ℚ.+ s)
      (r ℚ.+ s)
      ε
      (rational-close-translate q r s ε q∼r)

  add-right-ne : IsBinaryRationalNonexpandingRight rational-add
  add-right-ne q r s ε r∼s =
    point-point-close
      (q ℚ.+ r)
      (q ℚ.+ s)
      ε
      (rational-close-translate-left q r s ε r∼s)


infixl 6 _+ᶜ_

_+ᶜ_ : ℝᶜ → ℝᶜ → ℝᶜ
_+ᶜ_ =
  extendBinaryNonexpanding rational-add add-left-ne add-right-ne


add-rational :
  (q r : ℚ) →
  rational q +ᶜ rational r ≡ rational (q ℚ.+ r)
add-rational q r =
  refl


add-rational-left :
  (q : ℚ) (y : ℝᶜ) →
  rational q +ᶜ y ≡
  extendNonexpanding (rational-add q) (add-right-ne q) y
add-rational-left q y =
  refl


add-rational-right :
  (x : ℝᶜ) (r : ℚ) →
  x +ᶜ rational r ≡
  extendNonexpanding
    (λ q → rational-add q r)
    (λ q s ε q∼s → add-left-ne q s r ε q∼s)
    x
add-rational-right =
  extendBinaryNonexpanding-rational-right
    rational-add
    add-left-ne
    add-right-ne


add-close-left :
  {x y : ℝᶜ} {ε : ℚ⁺} →
  x ∼[ ε ] y →
  (z : ℝᶜ) →
  (x +ᶜ z) ∼[ ε ] (y +ᶜ z)
add-close-left =
  extendBinaryNonexpanding-close-left
    rational-add
    add-left-ne
    add-right-ne


add-close-right :
  (x : ℝᶜ) →
  {y z : ℝᶜ} {ε : ℚ⁺} →
  y ∼[ ε ] z →
  (x +ᶜ y) ∼[ ε ] (x +ᶜ z)
add-close-right =
  extendBinaryNonexpanding-close-right
    rational-add
    add-left-ne
    add-right-ne


add-close :
  {x y z w : ℝᶜ} {η ε : ℚ⁺} →
  x ∼[ η ] y →
  z ∼[ ε ] w →
  (x +ᶜ z) ∼[ η +⁺ ε ] (y +ᶜ w)
add-close =
  extendBinaryNonexpanding-close
    rational-add
    add-left-ne
    add-right-ne


add-nonexpanding-left :
  (z : ℝᶜ) →
  IsNonexpanding (λ x → x +ᶜ z)
add-nonexpanding-left z x∼y =
  add-close-left x∼y z


add-nonexpanding-right :
  (x : ℝᶜ) →
  IsNonexpanding (λ y → x +ᶜ y)
add-nonexpanding-right x =
  add-close-right x


add-continuous-left :
  (z : ℝᶜ) →
  IsContinuous (λ x → x +ᶜ z)
add-continuous-left z =
  nonexpanding→continuous (add-nonexpanding-left z)


add-continuous-right :
  (x : ℝᶜ) →
  IsContinuous (λ y → x +ᶜ y)
add-continuous-right x =
  nonexpanding→continuous (add-nonexpanding-right x)


private
  addZeroRightKit : PropInductionKit ℓ-zero
  addZeroRightKit .PropInductionKit.A x =
    x +ᶜ 0ᶜ ≡ x
  addZeroRightKit .PropInductionKit.isPropA x =
    isSetℝᶜ (x +ᶜ 0ᶜ) x
  addZeroRightKit .PropInductionKit.point* q =
    cong rational (ℚ.+IdR q)
  addZeroRightKit .PropInductionKit.limit* x add0At =
    path
      (limit (cauchy-approximation f fCauchy))
      (limit x)
      closeAt
    where
    f : ℚ⁺ → ℝᶜ
    f ε = approximate x ε +ᶜ 0ᶜ

    fCauchy : (ε δ : ℚ⁺) → f ε ∼[ ε +⁺ δ ] f δ
    fCauchy ε δ =
      add-close-left (isRegular x ε δ) 0ᶜ

    closeAt :
      (ε : ℚ⁺) →
      limit (cauchy-approximation f fCauchy) ∼[ ε ] limit x
    closeAt ε =
      limit-limit-intro
        (cauchy-approximation f fCauchy)
        x
        ε δ δ δ+δ<ε
        (subst
          (λ z → z ∼[ ε ⊖ (δ +⁺ δ) [ δ+δ<ε ] ] approximate x δ)
          (sym (add0At δ))
          (close-refl (approximate x δ)
            (ε ⊖ (δ +⁺ δ) [ δ+δ<ε ])))
      where
      δ : ℚ⁺
      δ = quarter⁺ ε

      δ+δ<ε : δ +⁺ δ <⁺ ε
      δ+δ<ε = quarter-sum< ε

  module AddZeroRightInduction = PropInduction addZeroRightKit


add-zero-right : (x : ℝᶜ) → x +ᶜ 0ᶜ ≡ x
add-zero-right =
  AddZeroRightInduction.ind


private
  addZeroLeftKit : PropInductionKit ℓ-zero
  addZeroLeftKit .PropInductionKit.A x =
    0ᶜ +ᶜ x ≡ x
  addZeroLeftKit .PropInductionKit.isPropA x =
    isSetℝᶜ (0ᶜ +ᶜ x) x
  addZeroLeftKit .PropInductionKit.point* q =
    cong rational (ℚ.+IdL q)
  addZeroLeftKit .PropInductionKit.limit* x add0At =
    path
      (limit (cauchy-approximation f fCauchy))
      (limit x)
      closeAt
    where
    f : ℚ⁺ → ℝᶜ
    f ε = 0ᶜ +ᶜ approximate x ε

    fCauchy : (ε δ : ℚ⁺) → f ε ∼[ ε +⁺ δ ] f δ
    fCauchy ε δ =
      add-close-right 0ᶜ (isRegular x ε δ)

    closeAt :
      (ε : ℚ⁺) →
      limit (cauchy-approximation f fCauchy) ∼[ ε ] limit x
    closeAt ε =
      limit-limit-intro
        (cauchy-approximation f fCauchy)
        x
        ε δ δ δ+δ<ε
        (subst
          (λ z → z ∼[ ε ⊖ (δ +⁺ δ) [ δ+δ<ε ] ] approximate x δ)
          (sym (add0At δ))
          (close-refl (approximate x δ)
            (ε ⊖ (δ +⁺ δ) [ δ+δ<ε ])))
      where
      δ : ℚ⁺
      δ = quarter⁺ ε

      δ+δ<ε : δ +⁺ δ <⁺ ε
      δ+δ<ε = quarter-sum< ε

  module AddZeroLeftInduction = PropInduction addZeroLeftKit


add-zero-left : (x : ℝᶜ) → 0ᶜ +ᶜ x ≡ x
add-zero-left =
  AddZeroLeftInduction.ind


add-comm-rational-left :
  (q : ℚ) (y : ℝᶜ) →
  rational q +ᶜ y ≡ y +ᶜ rational q
add-comm-rational-left q =
  nonexpanding-equal
    (λ y → rational q +ᶜ y)
    (λ y → y +ᶜ rational q)
    (add-nonexpanding-right (rational q))
    (add-nonexpanding-left (rational q))
    (λ r → cong rational (ℚ.+Comm q r))


add-comm :
  (x y : ℝᶜ) →
  x +ᶜ y ≡ y +ᶜ x
add-comm x y =
  nonexpanding-equal
    (λ z → z +ᶜ y)
    (λ z → y +ᶜ z)
    (add-nonexpanding-left y)
    (add-nonexpanding-right y)
    (λ q → add-comm-rational-left q y)
    x


add-assoc-rational-rational-left :
  (q r : ℚ) (z : ℝᶜ) →
  rational q +ᶜ (rational r +ᶜ z) ≡
  (rational q +ᶜ rational r) +ᶜ z
add-assoc-rational-rational-left q r =
  nonexpanding-equal
    (λ z → rational q +ᶜ (rational r +ᶜ z))
    (λ z → (rational q +ᶜ rational r) +ᶜ z)
    (comp-nonexpanding
      (add-nonexpanding-right (rational q))
      (add-nonexpanding-right (rational r)))
    (add-nonexpanding-right (rational q +ᶜ rational r))
    (λ s → cong rational (ℚ.+Assoc q r s))


add-assoc-rational-left :
  (q : ℚ) (y z : ℝᶜ) →
  rational q +ᶜ (y +ᶜ z) ≡
  (rational q +ᶜ y) +ᶜ z
add-assoc-rational-left q y z =
  nonexpanding-equal
    (λ w → rational q +ᶜ (w +ᶜ z))
    (λ w → (rational q +ᶜ w) +ᶜ z)
    (comp-nonexpanding
      (add-nonexpanding-right (rational q))
      (add-nonexpanding-left z))
    (comp-nonexpanding
      (add-nonexpanding-left z)
      (add-nonexpanding-right (rational q)))
    (λ r → add-assoc-rational-rational-left q r z)
    y


add-assoc :
  (x y z : ℝᶜ) →
  x +ᶜ (y +ᶜ z) ≡ (x +ᶜ y) +ᶜ z
add-assoc x y z =
  nonexpanding-equal
    (λ w → w +ᶜ (y +ᶜ z))
    (λ w → (w +ᶜ y) +ᶜ z)
    (add-nonexpanding-left (y +ᶜ z))
    (comp-nonexpanding
      (add-nonexpanding-left z)
      (add-nonexpanding-left y))
    (λ q → add-assoc-rational-left q y z)
    x


add-inverse-right-continuous :
  IsContinuous (λ x → x +ᶜ (-ᶜ x))
add-inverse-right-continuous ε =
  δ , closeAt
  where
  δ : ℚ⁺
  δ = half⁺ ε

  closeAt :
    {x y : ℝᶜ} →
    x ∼[ δ ] y →
    (x +ᶜ (-ᶜ x)) ∼[ ε ] (y +ᶜ (-ᶜ y))
  closeAt {x = x} {y = y} x∼y =
    subst
      (λ ρ → (x +ᶜ (-ᶜ x)) ∼[ ρ ] (y +ᶜ (-ᶜ y)))
      (half⁺+half⁺≡ ε)
      (add-close x∼y (neg-close x∼y))


add-inverse-right :
  (x : ℝᶜ) →
  x +ᶜ (-ᶜ x) ≡ 0ᶜ
add-inverse-right =
  continuous-constant-equal
    (λ x → x +ᶜ (-ᶜ x))
    0ᶜ
    add-inverse-right-continuous
    (λ q → cong rational (ℚ.+InvR q))


add-inverse-left :
  (x : ℝᶜ) →
  (-ᶜ x) +ᶜ x ≡ 0ᶜ
add-inverse-left x =
  add-comm (-ᶜ x) x ∙
  add-inverse-right x
