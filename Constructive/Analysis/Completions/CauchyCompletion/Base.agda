{-

Cauchy completion of a precision-indexed metric space

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Completions.CauchyCompletion.Base where

open import Cubical.Foundations.Prelude

open import Constructive.Analysis.Metric.Base
open import Constructive.Data.PositiveRationals

private
  variable
    ℓ ℓ' : Level


module CompletionOf (𝓜 : MetricSpace ℓ ℓ') where
  private
    A : Type ℓ
    A = MetricSpace.Carrier 𝓜

  infix 4 _≈[_]_ _∼[_]_

  _≈[_]_ : A → ℚ⁺ → A → Type ℓ'
  x ≈[ ε ] y = MetricSpace.Close 𝓜 x ε y

  mutual
    data Completion : Type (ℓ-max ℓ ℓ') where
      point : A → Completion
      limit : CauchyApproximation → Completion
      path :
        (x y : Completion) →
        ((ε : ℚ⁺) → x ∼[ ε ] y) →
        x ≡ y

    record CauchyApproximation : Type (ℓ-max ℓ ℓ') where
      inductive
      no-eta-equality
      constructor cauchy-approximation

      field
        approximate : ℚ⁺ → Completion
        isRegular :
          (ε δ : ℚ⁺) →
          approximate ε ∼[ ε +⁺ δ ] approximate δ

    data _∼[_]_ : Completion → ℚ⁺ → Completion → Type (ℓ-max ℓ ℓ') where
      point-point-close :
        (a b : A) (ε : ℚ⁺) →
        a ≈[ ε ] b →
        point a ∼[ ε ] point b

      point-limit-close :
        (a : A) (ε δ : ℚ⁺) →
        (δ<ε : δ <⁺ ε) →
        (y : CauchyApproximation) →
        point a ∼[ ε ⊖ δ [ δ<ε ] ] CauchyApproximation.approximate y δ →
        point a ∼[ ε ] limit y

      limit-point-close :
        (x : CauchyApproximation) →
        (b : A) (ε δ : ℚ⁺) →
        (δ<ε : δ <⁺ ε) →
        CauchyApproximation.approximate x δ ∼[ ε ⊖ δ [ δ<ε ] ] point b →
        limit x ∼[ ε ] point b

      limit-limit-close :
        (x y : CauchyApproximation) →
        (ε δ η : ℚ⁺) →
        (δ+η<ε : δ +⁺ η <⁺ ε) →
        CauchyApproximation.approximate x δ
          ∼[ ε ⊖ (δ +⁺ η) [ δ+η<ε ] ]
          CauchyApproximation.approximate y η →
        limit x ∼[ ε ] limit y

      squash : {x y : Completion} {ε : ℚ⁺} → isProp (x ∼[ ε ] y)

  open CauchyApproximation public


CauchyCompletion : MetricSpace ℓ ℓ' → Type (ℓ-max ℓ ℓ')
CauchyCompletion 𝓜 =
  CompletionOf.Completion 𝓜
