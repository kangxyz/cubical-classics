{-

Continuity of power-series sums from coefficient bounds

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Continuity.Theorem where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Sigma using (_,_)

open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
  using (add-close-left)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
  using (-ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Bounds
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Continuity.PartialSums
  using
    ( powerSeriesPartialSumsModulusFromCoefficientBounds
    ; powerSeriesPartialSumsUniformlyContinuousOnBallFromCoefficientBoundsWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Continuity.Limit
  using
    ( powerSeriesLimitApproximationIndex
    ; powerSeriesSumUniformlyContinuousFromPartialSums
    )
open import Constructive.Data.PositiveRationals


private
  powerSeriesSumUniformlyContinuousFromCoefficientBoundsWith :
    {a : PowerSeries} →
    {ρ : ℚ⁺} →
    {μ : ℚ⁺ → ℕ} →
    {convergence : HasPowerSeriesOnBallWith a ρ μ} →
    {κ : ℕ → ℚ⁺} →
    PowerSeriesCoefficientBoundsWith a κ →
    PowerSeriesSumUniformlyContinuousOnBallWith
      a
      ρ
      μ
      convergence
      (powerSeriesPartialSumsModulusFromCoefficientBounds
        κ
        ρ
        (powerSeriesLimitApproximationIndex μ))
  powerSeriesSumUniformlyContinuousFromCoefficientBoundsWith
    {μ = μ}
    coeffBounds =
    powerSeriesSumUniformlyContinuousFromPartialSums
      {χ = powerSeriesLimitApproximationIndex μ}
      (λ _ → NatOrder.≤-refl)
      (powerSeriesPartialSumsUniformlyContinuousOnBallFromCoefficientBoundsWith
        coeffBounds)


  centeredPowerSeriesSumUniformlyContinuousFromDisplacement :
    {a : PowerSeries} →
    {c : ℝᶜ} →
    {ρ : ℚ⁺} →
    {μ : ℚ⁺ → ℕ} →
    {convergence : HasPowerSeriesOnBallWith a ρ μ} →
    {ν : PrecisionModulus} →
    PowerSeriesSumUniformlyContinuousOnBallWith a ρ μ convergence ν →
    CenteredPowerSeriesSumUniformlyContinuousOnBallWith a c ρ μ convergence ν
  centeredPowerSeriesSumUniformlyContinuousFromDisplacement
    {c = c}
    uniform
    ε
    {x = x}
    {y = y}
    x-inBall
    y-inBall
    x∼y =
    uniform
      ε
      (InPowerSeriesBall.displacementBound x-inBall)
      (InPowerSeriesBall.displacementBound y-inBall)
      (add-close-left x∼y (-ᶜ c))


powerSeriesSumUniformlyContinuousFromCoefficientBounds :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  PowerSeriesCoefficientBounds a →
  PowerSeriesSumUniformlyContinuousOnBall a ρ μ convergence
powerSeriesSumUniformlyContinuousFromCoefficientBounds
  {ρ = ρ}
  {μ = μ}
  (κ , coeffBounds) =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    κ
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  powerSeriesSumUniformlyContinuousFromCoefficientBoundsWith
    coeffBounds


centeredPowerSeriesSumUniformlyContinuousFromCoefficientBounds :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a ρ μ} →
  PowerSeriesCoefficientBounds a →
  CenteredPowerSeriesSumUniformlyContinuousOnBall a c ρ μ convergence
centeredPowerSeriesSumUniformlyContinuousFromCoefficientBounds
  {a = a}
  {c = c}
  {ρ = ρ}
  {μ = μ}
  {convergence = convergence}
  bounds =
  ordinary .fst ,
  centeredPowerSeriesSumUniformlyContinuousFromDisplacement (ordinary .snd)
  where
  ordinary :
    PowerSeriesSumUniformlyContinuousOnBall a ρ μ convergence
  ordinary =
    powerSeriesSumUniformlyContinuousFromCoefficientBounds bounds
