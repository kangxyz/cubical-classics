{-

Tail bounds from finite strip approximants.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Recenter.StripTail where

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat.Order as NatOrder

open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.Series
  using (TailBound)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Base
open import Constructive.Analysis.Reals.PowerSeries.Recenter.FiniteLimits
  using
    ( boundedByClosedFromConvergentApproximants
    ; recenterOuterTailApprox
    ; recenterOuterTailApproxConvergesToTail
    )
open import Constructive.Data.PositiveRationals
  using (ℚ⁺)


recenterTailBoundFromOuterApproxBounds :
  {a : PowerSeries} →
  {d h : ℝᶜ} →
  {τ : ℚ⁺} →
  {ν : ℚ⁺ → ℕ} →
  (recenterData : RecenterPowerSeriesData a d) →
  BoundedByᶜ τ h →
  ((ε : ℚ⁺) →
    (m k N : ℕ) →
    NatOrder._≤_ (ν ε) m →
    BoundedByᶜ ε (recenterOuterTailApprox a d h m k N)) →
  TailBound
    (powerSeriesTerm (recenterPowerSeriesWith a d recenterData) h)
    ν
recenterTailBoundFromOuterApproxBounds
    {a = a}
    {d = d}
    {h = h}
    recenterData
    h-bound
    approxBound
    ε
    m
    k
    ν≤m =
  boundedByClosedFromConvergentApproximants
    ε
    (recenterOuterTailApproxConvergesToTail
      recenterData
      h-bound
      m
      k)
    (λ N → approxBound ε m k N ν≤m)
