{-

Maps with located Cauchy-real values

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Locator.Map where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Sigma using (Σ-syntax)

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.Locator.Base
open import Constructive.Data.PositiveRationals

open ClosenessOf RationalsMetricSpace

private
  variable
    ℓ : Level


ApproxEvaluable :
  {A : Type ℓ} →
  (A → ℝᶜ) →
  Type ℓ
ApproxEvaluable f =
  (x : _) →
  (ε : ℚ⁺) →
  Σ[ q ∈ ℚ ] f x ∼[ ε ] rational q


record LocatedMap {A : Type ℓ} (f : A → ℝᶜ) : Type ℓ where
  no-eta-equality

  field
    locatorAt : (x : A) → Locator (f x)


locatedMap→ApproxEvaluable :
  {A : Type ℓ} {f : A → ℝᶜ} →
  LocatedMap f →
  ApproxEvaluable f
locatedMap→ApproxEvaluable located x =
  Locator.approximate (LocatedMap.locatorAt located x)
