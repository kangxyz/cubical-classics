{-

Translation of HoTT Cauchy reals by rational constants

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Arithmetic.RationalTranslation where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals as ℚ using (ℚ)

open import Constructive.Analysis.CauchyCompletion.Closeness
open import Constructive.Analysis.CauchyCompletion.Induction
open import Constructive.Analysis.CauchyCompletion.Recursion
open import Constructive.Analysis.Metric.Map
open import Constructive.Analysis.Metric.Instances.CauchyReals
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.CauchyReals.Base
open ClosenessOf RationalsMetricSpace
open ComputedOf RationalsMetricSpace
open RoundedOf RationalsMetricSpace
open InductionOf RationalsMetricSpace
open RecursionOf RationalsMetricSpace


private
  translationKit : ℚ → RecursionKit ℓ-zero ℓ-zero
  translationKit s .RecursionKit.A = ℝᶜ
  translationKit s .RecursionKit.B ε x y = x ∼[ ε ] y
  translationKit s .RecursionKit.isPropB ε x y = squash
  translationKit s .RecursionKit.separated x y = path x y
  translationKit s .RecursionKit.point* q = rational (q ℚ.+ s)
  translationKit s .RecursionKit.limit* x f fCauchy =
    limit (cauchy-approximation f fCauchy)
  translationKit s .RecursionKit.point-point* q r ε q∼r =
    point-point-close (q ℚ.+ s) (r ℚ.+ s) ε
      (rational-close-translate q r s ε q∼r)
  translationKit s .RecursionKit.point-limit* q ε δ δ<ε y g gCauchy q∼gδ =
    point-limit-close (q ℚ.+ s) ε δ δ<ε
      (cauchy-approximation g gCauchy)
      q∼gδ
  translationKit s .RecursionKit.limit-point* x f fCauchy r ε δ δ<ε fδ∼r =
    limit-point-close
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


_+ᶜℚ_ : ℝᶜ → ℚ → ℝᶜ
x +ᶜℚ s = TranslationRecursion.rec s x

infixl 6 _+ᶜℚ_


translate-rational : (q s : ℚ) → rational q +ᶜℚ s ≡ rational (q ℚ.+ s)
translate-rational q s = refl


translate-close :
  {x y : ℝᶜ} {ε : ℚ⁺} →
  (s : ℚ) →
  x ∼[ ε ] y →
  (x +ᶜℚ s) ∼[ ε ] (y +ᶜℚ s)
translate-close s =
  TranslationRecursion.rec-close s


translate-nonexpanding : (s : ℚ) → IsNonexpanding CauchyRealsMetricSpace CauchyRealsMetricSpace (λ x → x +ᶜℚ s)
translate-nonexpanding s =
  translate-close s


translate-lipschitz : (s : ℚ) → IsLipschitz CauchyRealsMetricSpace CauchyRealsMetricSpace (λ x → x +ᶜℚ s)
translate-lipschitz s =
  (λ ε → ε) , λ ε → translate-close s


translate-continuous : (s : ℚ) → IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace (λ x → x +ᶜℚ s)
translate-continuous s =
  lipschitz→uniformlyContinuous {𝓧 = CauchyRealsMetricSpace} {𝓨 = CauchyRealsMetricSpace} (translate-lipschitz s)


private
  translateZeroKit : PropInductionKit ℓ-zero
  translateZeroKit .PropInductionKit.A x = x +ᶜℚ 0ℚ ≡ x
  translateZeroKit .PropInductionKit.isPropA x =
    isSetCompletion (x +ᶜℚ 0ℚ) x
  translateZeroKit .PropInductionKit.point* q =
    cong rational (ℚ.+IdR q)
  translateZeroKit .PropInductionKit.limit* x x+0≡x =
    path (limit (cauchy-approximation f fCauchy)) (limit x)
      closeAt
    where
    f : ℚ⁺ → ℝᶜ
    f ε = approximate x ε +ᶜℚ 0ℚ

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


translate-zero : (x : ℝᶜ) → x +ᶜℚ 0ℚ ≡ x
translate-zero =
  TranslateZeroInduction.ind


private
  translateCombineKit : (q s : ℚ) → PropInductionKit ℓ-zero
  translateCombineKit q s .PropInductionKit.A x =
    (x +ᶜℚ q) +ᶜℚ s ≡ x +ᶜℚ (q ℚ.+ s)
  translateCombineKit q s .PropInductionKit.isPropA x =
    isSetCompletion ((x +ᶜℚ q) +ᶜℚ s) (x +ᶜℚ (q ℚ.+ s))
  translateCombineKit q s .PropInductionKit.point* r =
    cong rational (sym (ℚ.+Assoc r q s))
  translateCombineKit q s .PropInductionKit.limit* x assocAt =
    path
      (limit (cauchy-approximation f fCauchy))
      (limit (cauchy-approximation g gCauchy))
      closeAt
    where
    f g : ℚ⁺ → ℝᶜ
    f ε = (approximate x ε +ᶜℚ q) +ᶜℚ s
    g ε = approximate x ε +ᶜℚ (q ℚ.+ s)

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
  (x : ℝᶜ) →
  (x +ᶜℚ q) +ᶜℚ s ≡ x +ᶜℚ (q ℚ.+ s)
translate-combine q s =
  TranslateCombineInduction.ind q s


translate-cancelR :
  (q : ℚ) →
  (x : ℝᶜ) →
  (x +ᶜℚ q) +ᶜℚ (ℚ.- q) ≡ x
translate-cancelR q x =
  translate-combine q (ℚ.- q) x ∙
  cong (λ r → x +ᶜℚ r) (ℚ.+InvR q) ∙
  translate-zero x


translate-cancelL :
  (q : ℚ) →
  (x : ℝᶜ) →
  (x +ᶜℚ (ℚ.- q)) +ᶜℚ q ≡ x
translate-cancelL q x =
  translate-combine (ℚ.- q) q x ∙
  cong (λ r → x +ᶜℚ r) (ℚ.+InvL q) ∙
  translate-zero x
