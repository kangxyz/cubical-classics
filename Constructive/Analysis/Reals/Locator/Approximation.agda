{-

Rational approximation data for located Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Locator.Approximation where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Data.Sum using (inl ; inr)

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
open import Constructive.Analysis.Reals.Locator.Base
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open ClosenessOf RationalsMetricSpace


approximateLocated :
  (x : ℝᶜ) →
  Locator x →
  (ε : ℚ⁺) →
  Σ[ q ∈ ℚ ] x ∼[ ε ] rational q
approximateLocated x loc =
  Locator.approximate loc


rationalLocator : (p : ℚ) → Locator (rational p)
rationalLocator p .Locator.compare q r q<r with q ℚOrder.≟ p
... | ℚOrder.lt q<p =
  inl (<ℚ→<ᶜ {q = q} {r = p} q<p)
... | ℚOrder.eq q≡p =
  inr (<ℚ→<ᶜ {q = p} {r = r} (subst (λ t → t ℚOrder.< r) q≡p q<r))
... | ℚOrder.gt p<q =
  inr (<ℚ→<ᶜ {q = p} {r = r} (ℚOrder.isTrans< p q r p<q q<r))
rationalLocator p .Locator.approximate ε =
  p , close-refl (rational p) ε


rationalLocated : ℚ → LocatedReal
rationalLocated p =
  rational p , rationalLocator p
