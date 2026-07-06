{-

Located HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Locator.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax)
open import Cubical.Data.Sum using (_⊎_)

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
open import Constructive.Data.PositiveRationals

open ClosenessOf RationalsMetricSpace


record Locator (x : ℝᶜ) : Type₀ where
  no-eta-equality

  field
    compare :
      (q r : ℚ) →
      q ℚOrder.< r →
      (rational q <ᶜ x) ⊎ (x <ᶜ rational r)

    approximate :
      (ε : ℚ⁺) →
      Σ[ q ∈ ℚ ] x ∼[ ε ] rational q


LocatedReal : Type₀
LocatedReal =
  Σ[ x ∈ ℝᶜ ] Locator x
