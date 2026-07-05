{-

Translation of HoTT Cauchy reals by rational constants

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Arithmetic.RationalTranslation where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals as ℚ using (ℚ)

open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Closeness.Properties
open import Constructive.CauchyReals.Continuity
open import Constructive.CauchyReals.Induction
open import Constructive.CauchyReals.Lipschitz.Base
open import Constructive.CauchyReals.Recursion


private
  translationKit : ℚ → RecursionKit ℓ-zero ℓ-zero
  translationKit s .RecursionKit.A = ℝᴴ
  translationKit s .RecursionKit.B ε x y = x ∼[ ε ] y
  translationKit s .RecursionKit.isPropB ε x y = squash
  translationKit s .RecursionKit.separated x y = path x y
  translationKit s .RecursionKit.rational* q = rational (q ℚ.+ s)
  translationKit s .RecursionKit.limit* x f fCauchy =
    limit (cauchy-approximation f fCauchy)
  translationKit s .RecursionKit.rational-rational* q r ε q∼r =
    rational-rational-close (q ℚ.+ s) (r ℚ.+ s) ε
      (rational-close-translate q r s ε q∼r)
  translationKit s .RecursionKit.rational-limit* q ε δ δ<ε y g gCauchy q∼gδ =
    rational-limit-close (q ℚ.+ s) ε δ δ<ε
      (cauchy-approximation g gCauchy)
      q∼gδ
  translationKit s .RecursionKit.limit-rational* x f fCauchy r ε δ δ<ε fδ∼r =
    limit-rational-close
      (cauchy-approximation f fCauchy)
      (r ℚ.+ s) ε δ δ<ε
      fδ∼r
  translationKit s .RecursionKit.limit-limit* x y f g fCauchy gCauchy ε δ η δ+η<ε fδ∼gη =
    limit-limit-close
      (cauchy-approximation f fCauchy)
      (cauchy-approximation g gCauchy)
      ε δ η δ+η<ε
      fδ∼gη

  module TranslationRecursion (s : ℚ) = Recursion (translationKit s)


_+ᴴℚ_ : ℝᴴ → ℚ → ℝᴴ
x +ᴴℚ s = TranslationRecursion.rec s x

infixl 6 _+ᴴℚ_


translate-rational : (q s : ℚ) → rational q +ᴴℚ s ≡ rational (q ℚ.+ s)
translate-rational q s = refl


translate-close :
  {x y : ℝᴴ} {ε : ℚ⁺} →
  (s : ℚ) →
  x ∼[ ε ] y →
  (x +ᴴℚ s) ∼[ ε ] (y +ᴴℚ s)
translate-close s =
  TranslationRecursion.rec-close s


translate-nonexpanding : (s : ℚ) → IsNonexpanding (λ x → x +ᴴℚ s)
translate-nonexpanding s =
  translate-close s


translate-lipschitz : (s : ℚ) → IsLipschitz (λ x → x +ᴴℚ s)
translate-lipschitz s =
  (λ ε → ε) , λ ε → translate-close s


translate-continuous : (s : ℚ) → IsContinuous (λ x → x +ᴴℚ s)
translate-continuous s =
  lipschitz→continuous (translate-lipschitz s)


private
  translateZeroKit : PropInductionKit ℓ-zero
  translateZeroKit .PropInductionKit.A x = x +ᴴℚ 0ℚ ≡ x
  translateZeroKit .PropInductionKit.isPropA x =
    isSetℝᴴ (x +ᴴℚ 0ℚ) x
  translateZeroKit .PropInductionKit.rational* q =
    cong rational (ℚ.+IdR q)
  translateZeroKit .PropInductionKit.limit* x x+0≡x =
    path (limit (cauchy-approximation f fCauchy)) (limit x)
      closeAt
    where
    f : ℚ⁺ → ℝᴴ
    f ε = approximate x ε +ᴴℚ 0ℚ

    fCauchy : (ε δ : ℚ⁺) → f ε ∼[ ε +⁺ δ ] f δ
    fCauchy ε δ = translate-close 0ℚ (isRegular x ε δ)

    closeAt :
      (ε : ℚ⁺) →
      limit (cauchy-approximation f fCauchy) ∼[ ε ] limit x
    closeAt ε =
      limit-limit-close
        (cauchy-approximation f fCauchy)
        x
        ε δ δ δ+δ<ε
        (subst
          (λ z → z ∼[ ε ⊖ (δ +⁺ δ) [ δ+δ<ε ] ] approximate x δ)
          (sym (x+0≡x δ))
          (close-refl (approximate x δ)
            (ε ⊖ (δ +⁺ δ) [ δ+δ<ε ])))
      where
      δ : ℚ⁺
      δ = quarter⁺ ε

      δ+δ<ε : δ +⁺ δ <⁺ ε
      δ+δ<ε = quarter-sum< ε

  module TranslateZeroInduction = PropInduction translateZeroKit


translate-zero : (x : ℝᴴ) → x +ᴴℚ 0ℚ ≡ x
translate-zero =
  TranslateZeroInduction.ind


private
  translateCombineKit : (q s : ℚ) → PropInductionKit ℓ-zero
  translateCombineKit q s .PropInductionKit.A x =
    (x +ᴴℚ q) +ᴴℚ s ≡ x +ᴴℚ (q ℚ.+ s)
  translateCombineKit q s .PropInductionKit.isPropA x =
    isSetℝᴴ ((x +ᴴℚ q) +ᴴℚ s) (x +ᴴℚ (q ℚ.+ s))
  translateCombineKit q s .PropInductionKit.rational* r =
    cong rational (sym (ℚ.+Assoc r q s))
  translateCombineKit q s .PropInductionKit.limit* x assocAt =
    path
      (limit (cauchy-approximation f fCauchy))
      (limit (cauchy-approximation g gCauchy))
      closeAt
    where
    f g : ℚ⁺ → ℝᴴ
    f ε = (approximate x ε +ᴴℚ q) +ᴴℚ s
    g ε = approximate x ε +ᴴℚ (q ℚ.+ s)

    fCauchy : (ε δ : ℚ⁺) → f ε ∼[ ε +⁺ δ ] f δ
    fCauchy ε δ =
      translate-close s (translate-close q (isRegular x ε δ))

    gCauchy : (ε δ : ℚ⁺) → g ε ∼[ ε +⁺ δ ] g δ
    gCauchy ε δ =
      translate-close (q ℚ.+ s) (isRegular x ε δ)

    closeAt :
      (ε : ℚ⁺) →
      limit (cauchy-approximation f fCauchy)
        ∼[ ε ]
      limit (cauchy-approximation g gCauchy)
    closeAt ε =
      limit-limit-close
        (cauchy-approximation f fCauchy)
        (cauchy-approximation g gCauchy)
        ε δ δ δ+δ<ε
        (subst
          (λ z → z ∼[ ε ⊖ (δ +⁺ δ) [ δ+δ<ε ] ] g δ)
          (sym (assocAt δ))
          (close-refl (g δ)
            (ε ⊖ (δ +⁺ δ) [ δ+δ<ε ])))
      where
      δ : ℚ⁺
      δ = quarter⁺ ε

      δ+δ<ε : δ +⁺ δ <⁺ ε
      δ+δ<ε = quarter-sum< ε

  module TranslateCombineInduction (q s : ℚ) =
    PropInduction (translateCombineKit q s)


translate-combine :
  (q s : ℚ) →
  (x : ℝᴴ) →
  (x +ᴴℚ q) +ᴴℚ s ≡ x +ᴴℚ (q ℚ.+ s)
translate-combine q s =
  TranslateCombineInduction.ind q s


translate-cancelR :
  (q : ℚ) →
  (x : ℝᴴ) →
  (x +ᴴℚ q) +ᴴℚ (ℚ.- q) ≡ x
translate-cancelR q x =
  translate-combine q (ℚ.- q) x ∙
  cong (λ r → x +ᴴℚ r) (ℚ.+InvR q) ∙
  translate-zero x


translate-cancelL :
  (q : ℚ) →
  (x : ℝᴴ) →
  (x +ᴴℚ (ℚ.- q)) +ᴴℚ q ≡ x
translate-cancelL q x =
  translate-combine (ℚ.- q) q x ∙
  cong (λ r → x +ᴴℚ r) (ℚ.+InvL q) ∙
  translate-zero x
