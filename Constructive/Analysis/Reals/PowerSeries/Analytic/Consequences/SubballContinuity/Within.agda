{-

Strict-subball continuity consequences for within-domain analytic expansions

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Analytic.Consequences.SubballContinuity.Within where

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


hasPowerSeriesWithinAtWithBounds→uniformlyContinuousOnSubball :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesWithinAtWithBounds {D = D} f c a σ μ →
  radius ρ ℚOrder.< radius σ →
  HasPowerSeriesWithinAtUniformlyContinuousOnBall {D = D} f c ρ
hasPowerSeriesWithinAtWithBounds→uniformlyContinuousOnSubball
  {D = D}
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
  λ ε {x = x} {y = y}
    x-domain y-domain x-inBall y-inBall x∼y →
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
        ∙ sym (agrees x x-domain x-inLarge)
      y-sum≡f =
        centeredPowerSeriesSumOnBall-data-independent
          smallConvergence
          convergence
          y
          y-inBall
          y-inLarge
        ∙ sym (agrees y y-domain y-inLarge)
    in
    subst2
      (λ u v → MetricSpace.Close CauchyRealsMetricSpace u ε v)
      x-sum≡f
      y-sum≡f
      (sum-continuity .snd ε x-inBall y-inBall x∼y)


hasPowerSeriesWithinAtWithBounds→merelyUniformlyContinuousOnSubball :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesWithinAtWithBounds {D = D} f c a σ μ →
  radius ρ ℚOrder.< radius σ →
  HasPowerSeriesWithinAtMerelyUniformlyContinuousOnBall {D = D} f c ρ
hasPowerSeriesWithinAtWithBounds→merelyUniformlyContinuousOnSubball
  expansion
  ρ<σ =
  hasPowerSeriesWithinAtUniformlyContinuousOnBall→merelyUniformlyContinuousOnBall
    (hasPowerSeriesWithinAtWithBounds→uniformlyContinuousOnSubball
      expansion
      ρ<σ)


hasPowerSeriesWithinAtWithBounds→continuousAtOnSubball :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesWithinAtWithBounds {D = D} f c a σ μ →
  radius ρ ℚOrder.< radius σ →
  (x : ℝᶜ) →
  (x-domain : D x) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesWithinAtContinuousAt {D = D} f c ρ x x-domain x-inBall
hasPowerSeriesWithinAtWithBounds→continuousAtOnSubball
  expansion
  ρ<σ
  x
  x-domain
  x-inBall =
  let
    uniformity =
      hasPowerSeriesWithinAtWithBounds→uniformlyContinuousOnSubball
        expansion
        ρ<σ
  in
  uniformity .fst ,
  λ ε y-domain y-inBall x∼y →
    uniformity .snd ε x-domain y-domain x-inBall y-inBall x∼y


hasPowerSeriesWithinAtWithBounds→merelyContinuousAtOnSubball :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWithBounds {D = D} f c a σ μ) →
  radius ρ ℚOrder.< radius σ →
  (x : ℝᶜ) →
  (x-domain : D x) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesWithinAtMerelyContinuousAt {D = D} f c ρ x x-domain x-inBall
hasPowerSeriesWithinAtWithBounds→merelyContinuousAtOnSubball
  {D = D}
  expansion
  ρ<σ
  x
  x-domain
  x-inBall =
  hasPowerSeriesWithinAtContinuousAt→merelyContinuousAt
    {D = D}
    {x-domain = x-domain}
    {x-inBall = x-inBall}
    (hasPowerSeriesWithinAtWithBounds→continuousAtOnSubball
      expansion
      ρ<σ
      x
      x-domain
      x-inBall)
