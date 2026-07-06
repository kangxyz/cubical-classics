{-

Precision-indexed metric spaces

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Metric.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
  using (∥_∥₁)

open import Constructive.Data.PositiveRationals

private
  variable
    ℓ ℓ' : Level


record MetricSpace (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  no-eta-equality

  field
    Carrier : Type ℓ
    isSetCarrier : isSet Carrier

    Close : Carrier → ℚ⁺ → Carrier → Type ℓ'
    isPropClose : (x y : Carrier) (ε : ℚ⁺) → isProp (Close x ε y)

    close-refl : (x : Carrier) (ε : ℚ⁺) → Close x ε x
    close-sym : {x y : Carrier} {ε : ℚ⁺} → Close x ε y → Close y ε x
    close-mono :
      {x y : Carrier} {ε δ : ℚ⁺} →
      ε <⁺ δ →
      Close x ε y →
      Close x δ y
    close-triangle :
      {x y z : Carrier} {ε δ : ℚ⁺} →
      Close x ε y →
      Close y δ z →
      Close x (ε +⁺ δ) z
    close-rounded :
      {x y : Carrier} {ε : ℚ⁺} →
      Close x ε y →
      ∥ Σ[ δ ∈ ℚ⁺ ] (δ <⁺ ε) × Close x δ y ∥₁

    close-separated :
      (x y : Carrier) →
      ((ε : ℚ⁺) → Close x ε y) →
      x ≡ y


module MetricSpaceStr (𝓜 : MetricSpace ℓ ℓ') where
  open MetricSpace 𝓜 public


CarrierOf : MetricSpace ℓ ℓ' → Type ℓ
CarrierOf = MetricSpace.Carrier
