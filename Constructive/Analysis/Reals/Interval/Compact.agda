{-

Compactness data for closed intervals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Interval.Compact where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation as Prop using (∥_∥₁)

import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Metric.TotallyBounded
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.Interval.Base
open import Constructive.Analysis.Reals.Interval.Completeness
open import Constructive.Analysis.Reals.Interval.Order
open import Constructive.Analysis.Reals.Interval.TotallyBounded
open import Constructive.Analysis.Reals.Locator.Base
open import Constructive.Data.PositiveRationals


record IsCompactInterval (a b : ℝᶜ) : Type₀ where
  constructor compact-interval
  no-eta-equality

  field
    complete : MetricCauchy.IsCauchyComplete (IntervalMetric a b)
    totallyBounded : IsTotallyBounded (IntervalMetric a b)


open IsCompactInterval public


intervalCompactFromTotallyBounded :
  {a b : ℝᶜ} →
  a ≤ᶜ b →
  IsTotallyBounded (IntervalMetric a b) →
  IsCompactInterval a b
intervalCompactFromTotallyBounded a≤b tb =
  compact-interval
    (intervalComplete a≤b)
    tb


intervalCompactFromGridCovers :
  {a b : ℝᶜ} →
  (a≤b : a ≤ᶜ b) →
  ((ε : ℚ⁺) → IntervalFiniteNetData a≤b ε) →
  IsCompactInterval a b
intervalCompactFromGridCovers a≤b gridData =
  intervalCompactFromTotallyBounded
    a≤b
    (intervalTotallyBoundedFromGridCovers a≤b gridData)


intervalCompactWithGapBound :
  {a b : ℝᶜ} →
  a ≤ᶜ b →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (gapᶜ a b) →
  IsCompactInterval a b
intervalCompactWithGapBound a≤b κ gap-bound =
  intervalCompactFromTotallyBounded
    a≤b
    (intervalTotallyBoundedWithGapBound a≤b κ gap-bound)


locatedIntervalCompact :
  {a b : ℝᶜ} →
  Locator a →
  Locator b →
  a ≤ᶜ b →
  IsCompactInterval a b
locatedIntervalCompact loc-a loc-b a≤b =
  intervalCompactFromTotallyBounded
    a≤b
    (locatedIntervalTotallyBounded loc-a loc-b a≤b)


intervalCompact∥∥ :
  {a b : ℝᶜ} →
  a ≤ᶜ b →
  ∥ IsCompactInterval a b ∥₁
intervalCompact∥∥ {a = a} {b = b} a≤b =
  Prop.map
    (λ gapData →
      intervalCompactWithGapBound
        a≤b
        (gapData .fst)
        (gapData .snd))
    (merely-boundedᶜ (gapᶜ a b))
