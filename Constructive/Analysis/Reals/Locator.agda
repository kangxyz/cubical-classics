{-

Located Cauchy-real structure

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Locator where

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

private
  variable
    ℓ : Level


{-

A locator is chosen representation data for an abstract HoTT Cauchy real.
Its approximation field supplies a Bishop-style rational name, while compare
supplies located order data against rational intervals.

-}
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


open Locator public


ApproxEvaluable :
  {A : Type ℓ} →
  (A → ℝᶜ) →
  Type ℓ
ApproxEvaluable f =
  (x : _) →
  (ε : ℚ⁺) →
  Σ[ q ∈ ℚ ] f x ∼[ ε ] rational q


LocatedMap :
  {A : Type ℓ} →
  (A → ℝᶜ) →
  Type ℓ
LocatedMap f =
  (x : _) → Locator (f x)


locatedMap→ApproxEvaluable :
  {A : Type ℓ} {f : A → ℝᶜ} →
  LocatedMap f →
  ApproxEvaluable f
locatedMap→ApproxEvaluable located x =
  approximate (located x)
