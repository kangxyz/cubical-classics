{-

Total boundedness interfaces for closed intervals

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Interval.TotallyBounded where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (Σ-syntax)
open import Cubical.HITs.PropositionalTruncation as Prop using (∥_∥₁)

open import Constructive.Analysis.Metric.TotallyBounded
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.Interval.Base
open import Constructive.Analysis.Reals.Interval.Grid.Base
open import Constructive.Analysis.Reals.Interval.Grid.Affine using (locatedGapBound)
open import Constructive.Analysis.Reals.Interval.Grid.Cover
open import Constructive.Analysis.Reals.Interval.Grid.Offset
open import Constructive.Analysis.Reals.Interval.Order
open import Constructive.Analysis.Reals.Locator.Base
open import Constructive.Data.PositiveRationals


IntervalFiniteNetData :
  {a b : ℝᶜ} →
  (a≤b : a ≤ᶜ b) →
  ℚ⁺ →
  Type₀
IntervalFiniteNetData {a = a} {b = b} a≤b ε =
  Σ[ n ∈ ℕ ] Σ[ G ∈ Grid a b a≤b n ]
    GridCovers {a = a} {b = b} {a≤b = a≤b} {n = n} G ε


intervalTotallyBoundedFromGridCovers :
  {a b : ℝᶜ} →
  (a≤b : a ≤ᶜ b) →
  ((ε : ℚ⁺) → IntervalFiniteNetData a≤b ε) →
  IsTotallyBounded (IntervalMetric a b)
intervalTotallyBoundedFromGridCovers {a = a} {b = b} a≤b gridData ε =
  gridFiniteNet {a = a} {b = b} {a≤b = a≤b} {n = netData .fst} G ε gridCovers
  where
  netData : IntervalFiniteNetData a≤b ε
  netData =
    gridData ε

  G : Grid a b a≤b (netData .fst)
  G =
    netData .snd .fst

  gridCovers :
    GridCovers
      {a = a}
      {b = b}
      {a≤b = a≤b}
      {n = netData .fst}
      G
      ε
  gridCovers =
    netData .snd .snd


intervalTotallyBoundedWithGapBound :
  {a b : ℝᶜ} →
  a ≤ᶜ b →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (gapᶜ a b) →
  IsTotallyBounded (IntervalMetric a b)
intervalTotallyBoundedWithGapBound {a = a} {b = b} a≤b κ gap-bound =
  intervalTotallyBoundedFromGridCovers
    {a = a}
    {b = b}
    a≤b
    (boundedOffsetGridCoverData {a = a} {b = b} a≤b κ gap-bound)


locatedIntervalTotallyBounded :
  {a b : ℝᶜ} →
  Locator a →
  Locator b →
  a ≤ᶜ b →
  IsTotallyBounded (IntervalMetric a b)
locatedIntervalTotallyBounded {a = a} {b = b} loc-a loc-b a≤b =
  intervalTotallyBoundedWithGapBound
    a≤b
    (gapData .fst)
    (gapData .snd)
  where
  gapData :
    Σ[ κ ∈ ℚ⁺ ] BoundedByᶜ κ (gapᶜ a b)
  gapData =
    locatedGapBound a b loc-a loc-b


intervalTotallyBounded∥∥ :
  {a b : ℝᶜ} →
  a ≤ᶜ b →
  (ε : ℚ⁺) →
  ∥ FiniteNet (IntervalMetric a b) ε ∥₁
intervalTotallyBounded∥∥ {a = a} {b = b} a≤b ε =
  Prop.map
    (λ gapData →
      intervalTotallyBoundedWithGapBound
        a≤b
        (gapData .fst)
        (gapData .snd)
        ε)
    (merely-boundedᶜ (gapᶜ a b))
