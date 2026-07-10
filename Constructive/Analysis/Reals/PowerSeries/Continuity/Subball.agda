{-

Strict-subball continuity wrappers for power-series sums

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Continuity.Subball where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)

open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.Series using (SeriesMajorizedBy)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Bounds
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Continuity.Core
open import Constructive.Data.PositiveRationals


hasPowerSeriesOnBallWith→uniformlyContinuousOnSubballFromCoefficientBoundsWith :
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a σ μ} →
  {κ : ℕ → ℚ⁺} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  PowerSeriesCoefficientBoundsWith a κ →
  PowerSeriesSumUniformlyContinuousOnBallWith
    a
    ρ
    μ
    (hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ convergence)
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      κ
      ρ
      (powerSeriesLimitApproximationIndex μ))
hasPowerSeriesOnBallWith→uniformlyContinuousOnSubballFromCoefficientBoundsWith
  {ρ = ρ}
  {σ = σ}
  {convergence = convergence}
  ρ<σ
  coeffBounds =
  powerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonicalWith
    {ρ = ρ}
    {convergence =
      hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ convergence}
    coeffBounds


hasPowerSeriesOnBallWith→uniformlyContinuousOnSubballFromCoefficientBounds :
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
hasPowerSeriesOnBallWith→uniformlyContinuousOnSubballFromCoefficientBounds
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {convergence = convergence}
  ρ<σ
  (κ , coeffBounds) =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    κ
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  hasPowerSeriesOnBallWith→uniformlyContinuousOnSubballFromCoefficientBoundsWith
    {ρ = ρ}
    {σ = σ}
    {convergence = convergence}
    ρ<σ
    coeffBounds


centeredPowerSeriesSumUniformlyContinuousOnSubballFromCoefficientBoundsWith :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a σ μ} →
  {κ : ℕ → ℚ⁺} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  PowerSeriesCoefficientBoundsWith a κ →
  CenteredPowerSeriesSumUniformlyContinuousOnBallWith
    a
    c
    ρ
    μ
    (hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ convergence)
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      κ
      ρ
      (powerSeriesLimitApproximationIndex μ))
centeredPowerSeriesSumUniformlyContinuousOnSubballFromCoefficientBoundsWith
  {ρ = ρ}
  {σ = σ}
  {convergence = convergence}
  ρ<σ
  coeffBounds =
  centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonicalWith
    {ρ = ρ}
    {convergence =
      hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ convergence}
    coeffBounds


centeredPowerSeriesSumUniformlyContinuousOnSubballFromCoefficientBounds :
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
centeredPowerSeriesSumUniformlyContinuousOnSubballFromCoefficientBounds
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {convergence = convergence}
  ρ<σ
  (κ , coeffBounds) =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    κ
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  centeredPowerSeriesSumUniformlyContinuousOnSubballFromCoefficientBoundsWith
    {ρ = ρ}
    {σ = σ}
    {convergence = convergence}
    ρ<σ
    coeffBounds


hasPowerSeriesOnBallWith→uniformlyContinuousOnSubballFromBallTermBoundsWith :
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a σ μ} →
  {κ : ℕ → ℚ⁺} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  PowerSeriesSumUniformlyContinuousOnBallWith
    a
    ρ
    μ
    (hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ convergence)
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
      ρ
      (powerSeriesLimitApproximationIndex μ))
hasPowerSeriesOnBallWith→uniformlyContinuousOnSubballFromBallTermBoundsWith
  {ρ = ρ}
  {σ = σ}
  {convergence = convergence}
  ρ<σ
  termBounds =
  powerSeriesSumUniformlyContinuousFromBallTermBoundsCanonicalWith
    {ρ = ρ}
    {convergence =
      hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ convergence}
    termBounds


hasPowerSeriesOnBallWith→uniformlyContinuousOnSubballFromBallTermBounds :
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a σ μ} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  PowerSeriesSumUniformlyContinuousOnBall
    a
    ρ
    μ
    (hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ convergence)
hasPowerSeriesOnBallWith→uniformlyContinuousOnSubballFromBallTermBounds
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {convergence = convergence}
  ρ<σ
  (κ , termBounds) =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  hasPowerSeriesOnBallWith→uniformlyContinuousOnSubballFromBallTermBoundsWith
    {ρ = ρ}
    {σ = σ}
    {convergence = convergence}
    ρ<σ
    termBounds


centeredPowerSeriesSumUniformlyContinuousOnSubballFromBallTermBoundsWith :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a σ μ} →
  {κ : ℕ → ℚ⁺} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  CenteredPowerSeriesSumUniformlyContinuousOnBallWith
    a
    c
    ρ
    μ
    (hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ convergence)
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
      ρ
      (powerSeriesLimitApproximationIndex μ))
centeredPowerSeriesSumUniformlyContinuousOnSubballFromBallTermBoundsWith
  {ρ = ρ}
  {σ = σ}
  {convergence = convergence}
  ρ<σ
  termBounds =
  centeredPowerSeriesSumUniformlyContinuousFromBallTermBoundsCanonicalWith
    {ρ = ρ}
    {convergence =
      hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ convergence}
    termBounds


centeredPowerSeriesSumUniformlyContinuousOnSubballFromBallTermBounds :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a σ μ} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  CenteredPowerSeriesSumUniformlyContinuousOnBall
    a
    c
    ρ
    μ
    (hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ convergence)
centeredPowerSeriesSumUniformlyContinuousOnSubballFromBallTermBounds
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {convergence = convergence}
  ρ<σ
  (κ , termBounds) =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  centeredPowerSeriesSumUniformlyContinuousOnSubballFromBallTermBoundsWith
    {ρ = ρ}
    {σ = σ}
    {convergence = convergence}
    ρ<σ
    termBounds


hasPowerSeriesOnBallWith→uniformlyContinuousOnSubballFromMajorantBoundsWith :
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a σ μ} →
  {v : ℕ → ℝᶜ} →
  {κ : ℕ → ℚ⁺} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    SeriesMajorizedBy (powerSeriesTerm a h) v) →
  ((n : ℕ) → BoundedByᶜ (κ n) (v n)) →
  PowerSeriesSumUniformlyContinuousOnBallWith
    a
    ρ
    μ
    (hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ convergence)
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
      ρ
      (powerSeriesLimitApproximationIndex μ))
hasPowerSeriesOnBallWith→uniformlyContinuousOnSubballFromMajorantBoundsWith
  {ρ = ρ}
  {σ = σ}
  {convergence = convergence}
  ρ<σ
  termMajorized
  majorantBounds =
  powerSeriesSumUniformlyContinuousFromMajorantBoundsCanonicalWith
    {ρ = ρ}
    {convergence =
      hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ convergence}
    termMajorized
    majorantBounds


hasPowerSeriesOnBallWith→uniformlyContinuousOnSubballFromMajorantBounds :
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a σ μ} →
  {v : ℕ → ℝᶜ} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    SeriesMajorizedBy (powerSeriesTerm a h) v) →
  Σ[ κ ∈ (ℕ → ℚ⁺) ] ((n : ℕ) → BoundedByᶜ (κ n) (v n)) →
  PowerSeriesSumUniformlyContinuousOnBall
    a
    ρ
    μ
    (hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ convergence)
hasPowerSeriesOnBallWith→uniformlyContinuousOnSubballFromMajorantBounds
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {convergence = convergence}
  ρ<σ
  termMajorized
  (κ , majorantBounds) =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  hasPowerSeriesOnBallWith→uniformlyContinuousOnSubballFromMajorantBoundsWith
    {ρ = ρ}
    {σ = σ}
    {convergence = convergence}
    ρ<σ
    termMajorized
    majorantBounds


centeredPowerSeriesSumUniformlyContinuousOnSubballFromMajorantBoundsWith :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a σ μ} →
  {v : ℕ → ℝᶜ} →
  {κ : ℕ → ℚ⁺} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    SeriesMajorizedBy (powerSeriesTerm a h) v) →
  ((n : ℕ) → BoundedByᶜ (κ n) (v n)) →
  CenteredPowerSeriesSumUniformlyContinuousOnBallWith
    a
    c
    ρ
    μ
    (hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ convergence)
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
      ρ
      (powerSeriesLimitApproximationIndex μ))
centeredPowerSeriesSumUniformlyContinuousOnSubballFromMajorantBoundsWith
  {ρ = ρ}
  {σ = σ}
  {convergence = convergence}
  ρ<σ
  termMajorized
  majorantBounds =
  centeredPowerSeriesSumUniformlyContinuousFromMajorantBoundsCanonicalWith
    {ρ = ρ}
    {convergence =
      hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ convergence}
    termMajorized
    majorantBounds


centeredPowerSeriesSumUniformlyContinuousOnSubballFromMajorantBounds :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {convergence : HasPowerSeriesOnBallWith a σ μ} →
  {v : ℕ → ℝᶜ} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    SeriesMajorizedBy (powerSeriesTerm a h) v) →
  Σ[ κ ∈ (ℕ → ℚ⁺) ] ((n : ℕ) → BoundedByᶜ (κ n) (v n)) →
  CenteredPowerSeriesSumUniformlyContinuousOnBall
    a
    c
    ρ
    μ
    (hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ convergence)
centeredPowerSeriesSumUniformlyContinuousOnSubballFromMajorantBounds
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {convergence = convergence}
  ρ<σ
  termMajorized
  (κ , majorantBounds) =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  centeredPowerSeriesSumUniformlyContinuousOnSubballFromMajorantBoundsWith
    {ρ = ρ}
    {σ = σ}
    {convergence = convergence}
    ρ<σ
    termMajorized
    majorantBounds
