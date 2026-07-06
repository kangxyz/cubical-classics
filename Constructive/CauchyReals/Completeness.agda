{-

Cauchy completeness for precision-indexed Cauchy approximations

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Completeness where

open import Cubical.Foundations.Prelude

open import Constructive.CauchyReals.Base
open import Constructive.CauchyReals.Closeness
open import Constructive.CauchyReals.Extension

private
  variable
    ℓ : Level


record CauchyStructure (A : Type ℓ) : Type (ℓ-suc ℓ) where
  no-eta-equality
  field
    Close : A → ℚ⁺ → A → Type ℓ


record CauchyApproximationIn
  (A : Type ℓ) {{S : CauchyStructure A}} : Type ℓ where
  constructor cauchy-approximation-in
  field
    approximate : ℚ⁺ → A
    isRegular :
      (ε δ : ℚ⁺) →
      CauchyStructure.Close S (approximate ε) (ε +⁺ δ) (approximate δ)


record CauchyLimitIn
  {A : Type ℓ} {{S : CauchyStructure A}}
  (x : CauchyApproximationIn A) : Type ℓ where
  constructor cauchy-limit-in
  field
    limitPoint : A
    converges :
      (ε δ : ℚ⁺) →
      (δ<ε : δ <⁺ ε) →
      CauchyStructure.Close S
        limitPoint
        ε
        (CauchyApproximationIn.approximate x δ)


isCauchyComplete :
  (A : Type ℓ) →
  {{S : CauchyStructure A}} →
  Type ℓ
isCauchyComplete A {{S}} =
  (x : CauchyApproximationIn A) → CauchyLimitIn x


isCauchyCompleteWith :
  (A : Type ℓ) →
  CauchyStructure A →
  Type ℓ
isCauchyCompleteWith A S =
  (x : CauchyApproximationIn A {{S}}) → CauchyLimitIn {{S}} x


instance
  CauchyRealsCauchyStructure : CauchyStructure CauchyReals
  CauchyRealsCauchyStructure .CauchyStructure.Close x ε y =
    x ∼[ ε ] y


toCauchyApproximationᶜ :
  CauchyApproximationIn CauchyReals →
  CauchyApproximation
toCauchyApproximationᶜ x =
  cauchy-approximation
    (CauchyApproximationIn.approximate x)
    (CauchyApproximationIn.isRegular x)


isCauchyComplete-CauchyReals :
  isCauchyComplete CauchyReals
isCauchyComplete-CauchyReals x =
  cauchy-limit-in
    (limit xᶜ)
    λ ε δ δ<ε →
      limit-close-intro xᶜ (approximate xᶜ δ) ε δ δ<ε
        (close-refl
          (approximate xᶜ δ)
          (ε ⊖ δ [ δ<ε ]))
  where
  xᶜ : CauchyApproximation
  xᶜ = toCauchyApproximationᶜ x


CauchyRealsIsCauchyComplete :
  isCauchyComplete CauchyReals
CauchyRealsIsCauchyComplete =
  isCauchyComplete-CauchyReals
