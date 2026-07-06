{-

Coverage predicates for finite interval grids

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Interval.Grid.Cover where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Sigma using (Σ-syntax)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.TotallyBounded
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.Interval
open import Constructive.Analysis.Reals.Interval.Grid
open import Constructive.Data.PositiveRationals


GridCovers :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {n : ℕ} →
  Grid a b a≤b n →
  ℚ⁺ →
  Type₀
GridCovers {a = a} {b = b} {n = n} G ε =
  (x : [ a , b ]ᶜ) →
  ∥ Σ[ i ∈ Fin (suc n) ]
      MetricSpace.Close (IntervalMetric a b) (Grid.point G i) ε x ∥₁


gridFiniteNet :
  {a b : ℝᶜ} {a≤b : a ≤ᶜ b} {n : ℕ} →
  (G : Grid a b a≤b n) →
  (ε : ℚ⁺) →
  GridCovers G ε →
  FiniteNet (IntervalMetric a b) ε
gridFiniteNet {n = n} G ε covers =
  finite-net
    (suc n)
    (Grid.point G)
    covers
