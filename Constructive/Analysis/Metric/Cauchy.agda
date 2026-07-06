{-

Cauchy approximations in precision-indexed metric spaces

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Metric.Cauchy where

open import Cubical.Foundations.Prelude

import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as Prop

open import Constructive.Data.PositiveRationals
open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Map

private
  variable
    ℓ ℓ' ℓᵃ ℓᵃ' ℓᵇ ℓᵇ' : Level


record CauchyApproximation (𝓜 : MetricSpace ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor cauchy-approximation
  no-eta-equality

  field
    approximate : ℚ⁺ → MetricSpace.Carrier 𝓜
    isRegular :
      (ε δ : ℚ⁺) →
      MetricSpace.Close 𝓜 (approximate ε) (ε +⁺ δ) (approximate δ)


open CauchyApproximation public


ConvergesTo :
  {𝓜 : MetricSpace ℓ ℓ'} →
  CauchyApproximation 𝓜 →
  MetricSpace.Carrier 𝓜 →
  Type ℓ'
ConvergesTo {𝓜 = 𝓜} x a =
  (ε δ : ℚ⁺) →
  δ <⁺ ε →
  MetricSpace.Close 𝓜 a ε (approximate x δ)


record CauchyLimit
  {𝓜 : MetricSpace ℓ ℓ'}
  (x : CauchyApproximation 𝓜) : Type (ℓ-max ℓ ℓ') where
  constructor cauchy-limit
  no-eta-equality

  field
    limitPoint : MetricSpace.Carrier 𝓜
    converges : ConvergesTo x limitPoint


open CauchyLimit public


IsComplete : MetricSpace ℓ ℓ' → Type (ℓ-max ℓ ℓ')
IsComplete 𝓜 =
  (x : CauchyApproximation 𝓜) → CauchyLimit x


close-mono-≤ :
  (𝓜 : MetricSpace ℓ ℓ') →
  {x y : MetricSpace.Carrier 𝓜} {ε δ : ℚ⁺} →
  radius ε ℚOrder.≤ radius δ →
  MetricSpace.Close 𝓜 x ε y →
  MetricSpace.Close 𝓜 x δ y
close-mono-≤ 𝓜 {x = x} {y = y} {ε = ε} {δ = δ} ε≤δ x∼y =
  Prop.rec
    (MetricSpace.isPropClose 𝓜 x y δ)
    (λ (ζ , ζ<ε , x∼ζ) →
      MetricSpace.close-mono 𝓜
        (ℚOrder.isTrans<≤ (radius ζ) (radius ε) (radius δ) ζ<ε ε≤δ)
        x∼ζ)
    (MetricSpace.close-rounded 𝓜 x∼y)


mapNonexpandingCauchyApproximation :
  {𝓧 : MetricSpace ℓᵃ ℓᵃ'} →
  {𝓨 : MetricSpace ℓᵇ ℓᵇ'} →
  {f : MetricSpace.Carrier 𝓧 → MetricSpace.Carrier 𝓨} →
  IsNonexpanding 𝓧 𝓨 f →
  CauchyApproximation 𝓧 →
  CauchyApproximation 𝓨
mapNonexpandingCauchyApproximation {f = f} f-ne x =
  cauchy-approximation
    (λ ε → f (approximate x ε))
    (λ ε δ → f-ne (isRegular x ε δ))


mapUniformlyContinuousCauchyApproximation :
  {𝓧 : MetricSpace ℓᵃ ℓᵃ'} →
  {𝓨 : MetricSpace ℓᵇ ℓᵇ'} →
  {f : MetricSpace.Carrier 𝓧 → MetricSpace.Carrier 𝓨} →
  {μ : PrecisionModulus} →
  IsUniformlyContinuousWith 𝓧 𝓨 μ f →
  (x : ℚ⁺ → MetricSpace.Carrier 𝓧) →
  ((ε δ : ℚ⁺) → MetricSpace.Close 𝓧 (x ε) (μ (ε +⁺ δ)) (x δ)) →
  CauchyApproximation 𝓨
mapUniformlyContinuousCauchyApproximation {f = f} {μ = μ} f-cont x x-regular =
  cauchy-approximation
    (λ ε → f (x ε))
    (λ ε δ → f-cont (ε +⁺ δ) (x-regular ε δ))


mapRegularUniformlyContinuousCauchyApproximation :
  {𝓧 : MetricSpace ℓᵃ ℓᵃ'} →
  {𝓨 : MetricSpace ℓᵇ ℓᵇ'} →
  {f : MetricSpace.Carrier 𝓧 → MetricSpace.Carrier 𝓨} →
  {μ : PrecisionModulus} →
  IsRegularPrecisionModulus μ →
  IsUniformlyContinuousWith 𝓧 𝓨 μ f →
  CauchyApproximation 𝓧 →
  CauchyApproximation 𝓨
mapRegularUniformlyContinuousCauchyApproximation
  {𝓧 = 𝓧} {𝓨 = 𝓨} {f = f} {μ = μ} μ-regular f-cont x =
  cauchy-approximation
    (λ ε → f (approximate x (μ ε)))
    (λ ε δ →
      f-cont (ε +⁺ δ)
        (close-mono-≤ 𝓧 (μ-regular ε δ) (isRegular x (μ ε) (μ δ))))
