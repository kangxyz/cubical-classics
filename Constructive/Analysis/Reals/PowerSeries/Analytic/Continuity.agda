{-

Part of Constructive.Analysis.Reals.PowerSeries.Analytic

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Analytic.Continuity where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma using (Σ-syntax ; _,_)

open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Metric
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.PowerSeries.Radius
  using (InPowerSeriesBall)
open import Constructive.Data.PositiveRationals

HasPowerSeriesAtUniformlyContinuousOnBallWith :
  (ℝᶜ → ℝᶜ) →
  ℝᶜ →
  ℚ⁺ →
  PrecisionModulus →
  Type₀
HasPowerSeriesAtUniformlyContinuousOnBallWith f c ρ ν =
  (ε : ℚ⁺) →
  {x y : ℝᶜ} →
  (x-inBall : InPowerSeriesBall c ρ x) →
  (y-inBall : InPowerSeriesBall c ρ y) →
  MetricSpace.Close CauchyRealsMetricSpace x (ν ε) y →
  MetricSpace.Close CauchyRealsMetricSpace (f x) ε (f y)


HasPowerSeriesAtUniformlyContinuousOnBall :
  (ℝᶜ → ℝᶜ) →
  ℝᶜ →
  ℚ⁺ →
  Type₀
HasPowerSeriesAtUniformlyContinuousOnBall f c ρ =
  Σ[ ν ∈ PrecisionModulus ]
    HasPowerSeriesAtUniformlyContinuousOnBallWith f c ρ ν






HasPowerSeriesAtContinuousAtWith :
  (f : ℝᶜ → ℝᶜ) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (x : ℝᶜ) →
  InPowerSeriesBall c ρ x →
  PrecisionModulus →
  Type₀
HasPowerSeriesAtContinuousAtWith f c ρ x x-inBall ν =
  (ε : ℚ⁺) →
  {y : ℝᶜ} →
  (y-inBall : InPowerSeriesBall c ρ y) →
  MetricSpace.Close CauchyRealsMetricSpace x (ν ε) y →
  MetricSpace.Close CauchyRealsMetricSpace (f x) ε (f y)


HasPowerSeriesAtContinuousAt :
  (f : ℝᶜ → ℝᶜ) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (x : ℝᶜ) →
  InPowerSeriesBall c ρ x →
  Type₀
HasPowerSeriesAtContinuousAt f c ρ x x-inBall =
  Σ[ ν ∈ PrecisionModulus ]
    HasPowerSeriesAtContinuousAtWith f c ρ x x-inBall ν






HasPowerSeriesWithinAtUniformlyContinuousOnBallWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  ℝᶜ →
  ℚ⁺ →
  PrecisionModulus →
  Type ℓ
HasPowerSeriesWithinAtUniformlyContinuousOnBallWith {D = D} f c ρ ν =
  (ε : ℚ⁺) →
  {x y : ℝᶜ} →
  (x-domain : D x) →
  (y-domain : D y) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  (y-inBall : InPowerSeriesBall c ρ y) →
  MetricSpace.Close CauchyRealsMetricSpace x (ν ε) y →
  MetricSpace.Close CauchyRealsMetricSpace
    (f x x-domain)
    ε
    (f y y-domain)


HasPowerSeriesWithinAtUniformlyContinuousOnBall :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  ℝᶜ →
  ℚ⁺ →
  Type ℓ
HasPowerSeriesWithinAtUniformlyContinuousOnBall {D = D} f c ρ =
  Σ[ ν ∈ PrecisionModulus ]
    HasPowerSeriesWithinAtUniformlyContinuousOnBallWith {D = D} f c ρ ν






HasPowerSeriesWithinAtContinuousAtWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  (f : (x : ℝᶜ) → D x → ℝᶜ) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (x : ℝᶜ) →
  D x →
  InPowerSeriesBall c ρ x →
  PrecisionModulus →
  Type ℓ
HasPowerSeriesWithinAtContinuousAtWith {D = D} f c ρ x x-domain x-inBall ν =
  (ε : ℚ⁺) →
  {y : ℝᶜ} →
  (y-domain : D y) →
  (y-inBall : InPowerSeriesBall c ρ y) →
  MetricSpace.Close CauchyRealsMetricSpace x (ν ε) y →
  MetricSpace.Close CauchyRealsMetricSpace
    (f x x-domain)
    ε
    (f y y-domain)


HasPowerSeriesWithinAtContinuousAt :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  (f : (x : ℝᶜ) → D x → ℝᶜ) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (x : ℝᶜ) →
  D x →
  InPowerSeriesBall c ρ x →
  Type ℓ
HasPowerSeriesWithinAtContinuousAt {D = D} f c ρ x x-domain x-inBall =
  Σ[ ν ∈ PrecisionModulus ]
    HasPowerSeriesWithinAtContinuousAtWith
      {D = D}
      f
      c
      ρ
      x
      x-domain
      x-inBall
      ν
