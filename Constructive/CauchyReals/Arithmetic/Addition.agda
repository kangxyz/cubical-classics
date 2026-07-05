{-

Addition on HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Arithmetic.Addition where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals as ℚ using (ℚ)

open import Constructive.CauchyReals.Arithmetic.Base
open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Closeness.Properties
open import Constructive.CauchyReals.Continuity
open import Constructive.CauchyReals.Extension.Properties
open import Constructive.CauchyReals.Induction


private
  rational-add : ℚ → ℚ → ℝᴴ
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
    rational-rational-close
      (q ℚ.+ s)
      (r ℚ.+ s)
      ε
      (rational-close-translate q r s ε q∼r)

  add-right-ne : IsBinaryRationalNonexpandingRight rational-add
  add-right-ne q r s ε r∼s =
    rational-rational-close
      (q ℚ.+ r)
      (q ℚ.+ s)
      ε
      (rational-close-translate-left q r s ε r∼s)


infixl 6 _+ᴴ_

_+ᴴ_ : ℝᴴ → ℝᴴ → ℝᴴ
_+ᴴ_ =
  extendBinaryNonexpanding rational-add add-left-ne add-right-ne


add-rational :
  (q r : ℚ) →
  rational q +ᴴ rational r ≡ rational (q ℚ.+ r)
add-rational q r =
  refl


add-rational-left :
  (q : ℚ) (y : ℝᴴ) →
  rational q +ᴴ y ≡
  extendNonexpanding (rational-add q) (add-right-ne q) y
add-rational-left q y =
  refl


add-rational-right :
  (x : ℝᴴ) (r : ℚ) →
  x +ᴴ rational r ≡
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
  {x y : ℝᴴ} {ε : ℚ⁺} →
  x ∼[ ε ] y →
  (z : ℝᴴ) →
  (x +ᴴ z) ∼[ ε ] (y +ᴴ z)
add-close-left =
  extendBinaryNonexpanding-close-left
    rational-add
    add-left-ne
    add-right-ne


add-close-right :
  (x : ℝᴴ) →
  {y z : ℝᴴ} {ε : ℚ⁺} →
  y ∼[ ε ] z →
  (x +ᴴ y) ∼[ ε ] (x +ᴴ z)
add-close-right =
  extendBinaryNonexpanding-close-right
    rational-add
    add-left-ne
    add-right-ne


add-close :
  {x y z w : ℝᴴ} {η ε : ℚ⁺} →
  x ∼[ η ] y →
  z ∼[ ε ] w →
  (x +ᴴ z) ∼[ η +⁺ ε ] (y +ᴴ w)
add-close =
  extendBinaryNonexpanding-close
    rational-add
    add-left-ne
    add-right-ne


add-nonexpanding-left :
  (z : ℝᴴ) →
  IsNonexpanding (λ x → x +ᴴ z)
add-nonexpanding-left z x∼y =
  add-close-left x∼y z


add-nonexpanding-right :
  (x : ℝᴴ) →
  IsNonexpanding (λ y → x +ᴴ y)
add-nonexpanding-right x =
  add-close-right x


add-continuous-left :
  (z : ℝᴴ) →
  IsContinuous (λ x → x +ᴴ z)
add-continuous-left z =
  nonexpanding→continuous (add-nonexpanding-left z)


add-continuous-right :
  (x : ℝᴴ) →
  IsContinuous (λ y → x +ᴴ y)
add-continuous-right x =
  nonexpanding→continuous (add-nonexpanding-right x)


private
  addZeroRightKit : PropInductionKit ℓ-zero
  addZeroRightKit .PropInductionKit.A x =
    x +ᴴ 0ᴴ ≡ x
  addZeroRightKit .PropInductionKit.isPropA x =
    isSetℝᴴ (x +ᴴ 0ᴴ) x
  addZeroRightKit .PropInductionKit.rational* q =
    cong rational (ℚ.+IdR q)
  addZeroRightKit .PropInductionKit.limit* x add0At =
    path
      (limit (cauchy-approximation f fCauchy))
      (limit x)
      closeAt
    where
    f : ℚ⁺ → ℝᴴ
    f ε = approximate x ε +ᴴ 0ᴴ

    fCauchy : (ε δ : ℚ⁺) → f ε ∼[ ε +⁺ δ ] f δ
    fCauchy ε δ =
      add-close-left (isRegular x ε δ) 0ᴴ

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


add-zero-right : (x : ℝᴴ) → x +ᴴ 0ᴴ ≡ x
add-zero-right =
  AddZeroRightInduction.ind


private
  addZeroLeftKit : PropInductionKit ℓ-zero
  addZeroLeftKit .PropInductionKit.A x =
    0ᴴ +ᴴ x ≡ x
  addZeroLeftKit .PropInductionKit.isPropA x =
    isSetℝᴴ (0ᴴ +ᴴ x) x
  addZeroLeftKit .PropInductionKit.rational* q =
    cong rational (ℚ.+IdL q)
  addZeroLeftKit .PropInductionKit.limit* x add0At =
    path
      (limit (cauchy-approximation f fCauchy))
      (limit x)
      closeAt
    where
    f : ℚ⁺ → ℝᴴ
    f ε = 0ᴴ +ᴴ approximate x ε

    fCauchy : (ε δ : ℚ⁺) → f ε ∼[ ε +⁺ δ ] f δ
    fCauchy ε δ =
      add-close-right 0ᴴ (isRegular x ε δ)

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


add-zero-left : (x : ℝᴴ) → 0ᴴ +ᴴ x ≡ x
add-zero-left =
  AddZeroLeftInduction.ind
