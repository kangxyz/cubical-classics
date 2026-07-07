{-

Internal helpers for strict-subball analytic continuity consequences

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Analytic.Consequences.SubballContinuity.Internal where

open import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using (bounded-byᶜ-monotone)
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals


inPowerSeriesSubball→largerBall :
    {c x : ℝᶜ} →
    {ρ σ : ℚ⁺} →
    radius ρ ℚOrder.< radius σ →
    InPowerSeriesBall c ρ x →
    InPowerSeriesBall c σ x
inPowerSeriesSubball→largerBall
  {ρ = ρ}
  {σ = σ}
  ρ<σ
  x-inBall =
    record
      { displacementBound =
          bounded-byᶜ-monotone
            (ℚOrder.<Weaken≤ (radius ρ) (radius σ) ρ<σ)
            (InPowerSeriesBall.displacementBound x-inBall)
      }


