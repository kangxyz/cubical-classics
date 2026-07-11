{-

Negation on HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals as ℚ using (ℚ)

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Map
open import Constructive.Analysis.Reals.CauchyReals.Metric
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Extension
open ClosenessOf RationalsMetricSpace


private
  rationalNegation : ℚ → ℝᶜ
  rationalNegation q =
    rational (ℚ.- q)

  rationalNegation-nonexpanding :
    IsRationalNonexpanding rationalNegation
  rationalNegation-nonexpanding q r ε q∼r =
    point-point-close (ℚ.- q) (ℚ.- r) ε
      (rational-close-neg q r ε q∼r)


-ᶜ_ : ℝᶜ → ℝᶜ
-ᶜ_ =
  extendNonexpanding rationalNegation rationalNegation-nonexpanding


neg-rational : (q : ℚ) → -ᶜ rational q ≡ rational (ℚ.- q)
neg-rational =
  extendNonexpanding-rational rationalNegation rationalNegation-nonexpanding


neg-close : {x y : ℝᶜ} {ε : ℚ⁺} → x ∼[ ε ] y → (-ᶜ x) ∼[ ε ] (-ᶜ y)
neg-close =
  extendNonexpanding-close rationalNegation rationalNegation-nonexpanding


neg-nonexpanding : IsNonexpanding CauchyRealsMetricSpace CauchyRealsMetricSpace -ᶜ_
neg-nonexpanding = neg-close


neg-lipschitz : IsLipschitz CauchyRealsMetricSpace CauchyRealsMetricSpace -ᶜ_
neg-lipschitz =
  nonexpanding→lipschitz
    {𝓧 = CauchyRealsMetricSpace}
    {𝓨 = CauchyRealsMetricSpace}
    {f = -ᶜ_}
    neg-nonexpanding


neg-continuous : IsUniformlyContinuous CauchyRealsMetricSpace CauchyRealsMetricSpace -ᶜ_
neg-continuous =
  lipschitz→uniformlyContinuous
    {𝓧 = CauchyRealsMetricSpace}
    {𝓨 = CauchyRealsMetricSpace}
    {f = -ᶜ_}
    neg-lipschitz


neg-involutive : (x : ℝᶜ) → -ᶜ (-ᶜ x) ≡ x
neg-involutive =
  nonexpanding-equal
    (λ x → -ᶜ (-ᶜ x))
    (λ x → x)
    (comp-nonexpanding
      {𝓧 = CauchyRealsMetricSpace}
      {𝓨 = CauchyRealsMetricSpace}
      {𝓩 = CauchyRealsMetricSpace}
      {f = -ᶜ_}
      {g = -ᶜ_}
      neg-nonexpanding
      neg-nonexpanding)
    (id-nonexpanding CauchyRealsMetricSpace)
    λ q →
      cong -ᶜ_ (neg-rational q) ∙
      neg-rational (ℚ.- q) ∙
      cong rational (ℚ.-Invol q)
