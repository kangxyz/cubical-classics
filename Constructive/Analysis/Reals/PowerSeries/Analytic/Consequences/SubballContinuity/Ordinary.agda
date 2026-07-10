{-

Strict-subball continuity consequences for ordinary analytic expansions

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Analytic.Consequences.SubballContinuity.Ordinary where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (_,_)

open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Metric
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Continuity.Subball
  using (centeredPowerSeriesSumUniformlyContinuousOnSubball)
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals

open import Constructive.Analysis.Reals.PowerSeries.Analytic.Core
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Continuity
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Consequences.SubballContinuity.Internal
  using (inPowerSeriesSubball→largerBall)


hasPowerSeriesAtWithBounds→uniformlyContinuousOnSubball :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesAtWithBounds f c a σ μ →
  radius ρ ℚOrder.< radius σ →
  HasPowerSeriesAtUniformlyContinuousOnBall f c ρ
hasPowerSeriesAtWithBounds→uniformlyContinuousOnSubball
  {f = f}
  {c = c}
  {a = a}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  ((convergence , agrees) , bounds)
  ρ<σ =
  let
    sum-continuity =
      centeredPowerSeriesSumUniformlyContinuousOnSubball
        {c = c}
        {convergence = convergence}
        ρ<σ
        bounds
  in
  sum-continuity .fst ,
  λ ε {x = x} {y = y} x-inBall y-inBall x∼y →
    let
      smallConvergence =
        hasPowerSeriesOnSmallerBallWith
          {ρ = ρ}
          {σ = σ}
          ρ<σ
          convergence
      x-inLarge = inPowerSeriesSubball→largerBall ρ<σ x-inBall
      y-inLarge = inPowerSeriesSubball→largerBall ρ<σ y-inBall
      x-sum≡f =
        centeredPowerSeriesSumOnBall-data-independent
          smallConvergence
          convergence
          x
          x-inBall
          x-inLarge
        ∙ sym (agrees x x-inLarge)
      y-sum≡f =
        centeredPowerSeriesSumOnBall-data-independent
          smallConvergence
          convergence
          y
          y-inBall
          y-inLarge
        ∙ sym (agrees y y-inLarge)
    in
    subst2
      (λ u v → MetricSpace.Close CauchyRealsMetricSpace u ε v)
      x-sum≡f
      y-sum≡f
      (sum-continuity .snd ε x-inBall y-inBall x∼y)


hasPowerSeriesAtWithBounds→merelyUniformlyContinuousOnSubball :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesAtWithBounds f c a σ μ →
  radius ρ ℚOrder.< radius σ →
  HasPowerSeriesAtMerelyUniformlyContinuousOnBall f c ρ
hasPowerSeriesAtWithBounds→merelyUniformlyContinuousOnSubball expansion ρ<σ =
  hasPowerSeriesAtUniformlyContinuousOnBall→merelyUniformlyContinuousOnBall
    (hasPowerSeriesAtWithBounds→uniformlyContinuousOnSubball expansion ρ<σ)


hasPowerSeriesAtWithBounds→continuousAtOnSubball :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesAtWithBounds f c a σ μ →
  radius ρ ℚOrder.< radius σ →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesAtContinuousAt f c ρ x x-inBall
hasPowerSeriesAtWithBounds→continuousAtOnSubball expansion ρ<σ x x-inBall =
  let
    uniformity =
      hasPowerSeriesAtWithBounds→uniformlyContinuousOnSubball expansion ρ<σ
  in
  uniformity .fst ,
  λ ε y-inBall x∼y → uniformity .snd ε x-inBall y-inBall x∼y


hasPowerSeriesAtWithBounds→merelyContinuousAtOnSubball :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWithBounds f c a σ μ) →
  radius ρ ℚOrder.< radius σ →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesAtMerelyContinuousAt f c ρ x x-inBall
hasPowerSeriesAtWithBounds→merelyContinuousAtOnSubball
  expansion
  ρ<σ
  x
  x-inBall =
  hasPowerSeriesAtContinuousAt→merelyContinuousAt
    {x-inBall = x-inBall}
    (hasPowerSeriesAtWithBounds→continuousAtOnSubball
      expansion
      ρ<σ
      x
      x-inBall)
