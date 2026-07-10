{-

Uniform continuity on strict subballs

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Continuity.Subball where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Bounds
  using (PowerSeriesCoefficientBounds)
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Continuity.Theorem
  using
    ( centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonical
    ; powerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonical
    )
open import Constructive.Data.PositiveRationals


hasPowerSeriesOnBallWith→uniformlyContinuousOnSubball :
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a σ μ} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  PowerSeriesCoefficientBounds a →
  PowerSeriesSumUniformlyContinuousOnBall
    a
    ρ
    μ
    (hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ convergence)
hasPowerSeriesOnBallWith→uniformlyContinuousOnSubball
  {ρ = ρ}
  {σ = σ}
  {convergence = convergence}
  ρ<σ
  bounds =
  powerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonical
    { ρ = ρ }
    { convergence =
        hasPowerSeriesOnSmallerBallWith
          { ρ = ρ }
          { σ = σ }
          ρ<σ
          convergence
    }
    bounds


centeredPowerSeriesSumUniformlyContinuousOnSubball :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a σ μ} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  PowerSeriesCoefficientBounds a →
  CenteredPowerSeriesSumUniformlyContinuousOnBall
    a
    c
    ρ
    μ
    (hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ convergence)
centeredPowerSeriesSumUniformlyContinuousOnSubball
  {ρ = ρ}
  {σ = σ}
  {convergence = convergence}
  ρ<σ
  bounds =
  centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonical
    { ρ = ρ }
    { convergence =
        hasPowerSeriesOnSmallerBallWith
          { ρ = ρ }
          { σ = σ }
          ρ<σ
          convergence
    }
    bounds
