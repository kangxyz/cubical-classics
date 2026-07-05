{-

HoTT-style Cauchy reals

The real numbers and their rational-indexed closeness relation are defined
simultaneously, following the higher inductive-inductive construction in the
HoTT book.

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals using (ℚ)

open import Constructive.CauchyReals.PositiveRationals public
open import Constructive.CauchyReals.RationalCloseness public


mutual
  data ℝᶜ : Type₀ where
    rational : ℚ → ℝᶜ
    limit : CauchyApproximation → ℝᶜ
    path : (x y : ℝᶜ) → ((ε : ℚ⁺) → x ∼[ ε ] y) → x ≡ y

  record CauchyApproximation : Type₀ where
    inductive
    no-eta-equality
    constructor cauchy-approximation

    field
      approximate : ℚ⁺ → ℝᶜ
      isRegular :
        (ε δ : ℚ⁺) →
        approximate ε ∼[ ε +⁺ δ ] approximate δ

  data _∼[_]_ : ℝᶜ → ℚ⁺ → ℝᶜ → Type₀ where
    rational-rational-close :
      (q r : ℚ) (ε : ℚ⁺) →
      Closeℚ q ε r →
      rational q ∼[ ε ] rational r

    rational-limit-close :
      (q : ℚ) (ε δ : ℚ⁺) →
      (δ<ε : δ <⁺ ε) →
      (y : CauchyApproximation) →
      rational q ∼[ ε ⊖ δ [ δ<ε ] ] CauchyApproximation.approximate y δ →
      rational q ∼[ ε ] limit y

    limit-rational-close :
      (x : CauchyApproximation) →
      (r : ℚ) (ε δ : ℚ⁺) →
      (δ<ε : δ <⁺ ε) →
      CauchyApproximation.approximate x δ ∼[ ε ⊖ δ [ δ<ε ] ] rational r →
      limit x ∼[ ε ] rational r

    limit-limit-close :
      (x y : CauchyApproximation) →
      (ε δ η : ℚ⁺) →
      (δ+η<ε : δ +⁺ η <⁺ ε) →
      CauchyApproximation.approximate x δ
        ∼[ ε ⊖ (δ +⁺ η) [ δ+η<ε ] ]
        CauchyApproximation.approximate y η →
      limit x ∼[ ε ] limit y

    squash : {x y : ℝᶜ} {ε : ℚ⁺} → isProp (x ∼[ ε ] y)


open CauchyApproximation public


CauchyReals : Type₀
CauchyReals = ℝᶜ


ℚ→ℝᶜ : ℚ → ℝᶜ
ℚ→ℝᶜ = rational
