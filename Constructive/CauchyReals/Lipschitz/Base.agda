{-

Lipschitz-style predicates for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Lipschitz.Base where

open import Cubical.Foundations.Prelude

open import Constructive.CauchyReals.Base


PrecisionModulus : Type₀
PrecisionModulus = ℚ⁺ → ℚ⁺


IsLipschitzWith :
  PrecisionModulus →
  (ℝᴴ → ℝᴴ) →
  Type₀
IsLipschitzWith μ f =
  (ε : ℚ⁺) →
  {x y : ℝᴴ} →
  x ∼[ μ ε ] y →
  f x ∼[ ε ] f y


IsLipschitz : (ℝᴴ → ℝᴴ) → Type₀
IsLipschitz f = Σ[ μ ∈ PrecisionModulus ] IsLipschitzWith μ f


id-lipschitz : IsLipschitz (λ x → x)
id-lipschitz =
  (λ ε → ε) , λ ε x∼y → x∼y


comp-lipschitz :
  {f g : ℝᴴ → ℝᴴ} →
  IsLipschitz f →
  IsLipschitz g →
  IsLipschitz (λ x → f (g x))
comp-lipschitz (μ , f-lip) (ν , g-lip) =
  (λ ε → ν (μ ε)) , λ ε x∼y → f-lip ε (g-lip (μ ε) x∼y)
