{-

Function-level consequences of power-series expansions

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Analytic.Consequences where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)

open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.CauchyReals.Metric
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
  using (_+ᶜ_ ; add-close-left)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
  using (-ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.Calculus.DerivativeData
  using (HasDerivativeAtWith ; hasDerivativeAtWith-local-cong)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Bounds
  using (PowerSeriesCoefficientBounds)
open import Constructive.Analysis.Reals.PowerSeries.Continuity
  using
    ( centeredPowerSeriesSumUniformlyContinuousFromCoefficientBounds
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals

open import Constructive.Analysis.Reals.PowerSeries.Analytic.Base
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Continuity




hasPowerSeriesAtWith→hasDerivativeAtWithFromLocalModel :
  {f g : ℝᶜ → ℝᶜ} →
  {c x d : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {ν : PrecisionModulus} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  ((y : ℝᶜ) →
    (y-inBall : InPowerSeriesBall c ρ y) →
    g y ≡
    centeredPowerSeriesSumOnBall a c ρ μ (fst expansion) y y-inBall) →
  InPowerSeriesBall c ρ x →
  ((ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (ν ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    InPowerSeriesBall c ρ (x +ᶜ h)) →
  HasDerivativeAtWith g x d ν →
  HasDerivativeAtWith f x d ν
hasPowerSeriesAtWith→hasDerivativeAtWithFromLocalModel
  {x = x}
  expansion
  modelPath
  x-inBall
  forward-inBall =
  hasDerivativeAtWith-local-cong
    (snd expansion x x-inBall ∙ sym (modelPath x x-inBall))
    (λ ε η η≤νε h h-bound →
      let x+h-inBall = forward-inBall ε η η≤νε h h-bound
      in
      snd expansion (x +ᶜ h) x+h-inBall ∙
      sym (modelPath (x +ᶜ h) x+h-inBall))


hasPowerSeriesAtWith→hasDerivativeAtWithFromEverywhereModel :
  {f : ℝᶜ → ℝᶜ} →
  {c x d : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {ν : PrecisionModulus} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  InPowerSeriesBall c ρ x →
  ((ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (ν ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    InPowerSeriesBall c ρ (x +ᶜ h)) →
  HasDerivativeAtWith
    (centeredPowerSeriesSumEverywhere a c radiusData)
    x
    d
    ν →
  HasDerivativeAtWith f x d ν
hasPowerSeriesAtWith→hasDerivativeAtWithFromEverywhereModel
  {c = c}
  {a = a}
  {ρ = ρ}
  {μ = μ}
  radiusData
  expansion =
  hasPowerSeriesAtWith→hasDerivativeAtWithFromLocalModel
    expansion
    (λ y y-inBall →
      centeredPowerSeriesSumEverywhere-bound-path a c radiusData ρ y y-inBall ∙
      centeredPowerSeriesSumOnBallFrom-data-independent
        (radiusData ρ)
        (μ , fst expansion)
        y
        y-inBall
        y-inBall)


private
  transportUniformAt :
    {f : ℝᶜ → ℝᶜ} →
    {c : ℝᶜ} →
    {a : PowerSeries} →
    {ρ : ℚ⁺} →
    {μ : ℚ⁺ → ℕ} →
    (expansion : HasPowerSeriesAtWith f c a ρ μ) →
    { ν : PrecisionModulus } →
    CenteredPowerSeriesSumUniformlyContinuousOnBallWith
      a c ρ μ (fst expansion) ν →
    HasPowerSeriesAtUniformlyContinuousOnBallWith f c ρ ν
  transportUniformAt expansion uniform ε
      {x = x} {y = y} x-inBall y-inBall x∼y =
    subst2
      (λ u v → MetricSpace.Close CauchyRealsMetricSpace u ε v)
      (sym (snd expansion x x-inBall))
      (sym (snd expansion y y-inBall))
      (uniform ε x-inBall y-inBall x∼y)

  transportUniformWithin :
    {ℓ : Level} →
    {D : ℝᶜ → Type ℓ} →
    {f : (x : ℝᶜ) → D x → ℝᶜ} →
    {c : ℝᶜ} →
    {a : PowerSeries} →
    {ρ : ℚ⁺} →
    {μ : ℚ⁺ → ℕ} →
    (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
    { ν : PrecisionModulus } →
    CenteredPowerSeriesSumUniformlyContinuousOnBallWith
      a c ρ μ (fst expansion) ν →
    HasPowerSeriesWithinAtUniformlyContinuousOnBallWith {D = D} f c ρ ν
  transportUniformWithin expansion uniform ε
      {x = x} {y = y} x-domain y-domain x-inBall y-inBall x∼y =
    subst2
      (λ u v → MetricSpace.Close CauchyRealsMetricSpace u ε v)
      (sym (snd expansion x x-domain x-inBall))
      (sym (snd expansion y y-domain y-inBall))
      (uniform ε x-inBall y-inBall x∼y)

  transportContinuousAt :
    {f : ℝᶜ → ℝᶜ} →
    {c : ℝᶜ} →
    {a : PowerSeries} →
    {ρ : ℚ⁺} →
    {μ : ℚ⁺ → ℕ} →
    (expansion : HasPowerSeriesAtWith f c a ρ μ) →
    {ν : PrecisionModulus} →
    (x : ℝᶜ) →
    (x-inBall : InPowerSeriesBall c ρ x) →
    PowerSeriesSumContinuousAtWith
      a ρ μ (fst expansion)
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound x-inBall)
      ν →
    HasPowerSeriesAtContinuousAtWith f c ρ x x-inBall ν
  transportContinuousAt {c = c} expansion x x-inBall continuous ε
      {y = y} y-inBall x∼y =
    subst2
      (λ u v → MetricSpace.Close CauchyRealsMetricSpace u ε v)
      (sym (snd expansion x x-inBall))
      (sym (snd expansion y y-inBall))
      (continuous
        ε
        (InPowerSeriesBall.displacementBound y-inBall)
        (add-close-left x∼y (-ᶜ c)))

  transportContinuousWithin :
    {ℓ : Level} →
    {D : ℝᶜ → Type ℓ} →
    {f : (x : ℝᶜ) → D x → ℝᶜ} →
    {c : ℝᶜ} →
    {a : PowerSeries} →
    {ρ : ℚ⁺} →
    {μ : ℚ⁺ → ℕ} →
    (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
    {ν : PrecisionModulus} →
    (x : ℝᶜ) →
    (x-domain : D x) →
    (x-inBall : InPowerSeriesBall c ρ x) →
    PowerSeriesSumContinuousAtWith
      a ρ μ (fst expansion)
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound x-inBall)
      ν →
    HasPowerSeriesWithinAtContinuousAtWith
      {D = D} f c ρ x x-domain x-inBall ν
  transportContinuousWithin {c = c} expansion x x-domain x-inBall continuous ε
      {y = y} y-domain y-inBall x∼y =
    subst2
      (λ u v → MetricSpace.Close CauchyRealsMetricSpace u ε v)
      (sym (snd expansion x x-domain x-inBall))
      (sym (snd expansion y y-domain y-inBall))
      (continuous
        ε
        (InPowerSeriesBall.displacementBound y-inBall)
        (add-close-left x∼y (-ᶜ c)))

  uniformAt→continuousAt :
    {f : ℝᶜ → ℝᶜ} →
    {c x : ℝᶜ} →
    {ρ : ℚ⁺} →
    (x-inBall : InPowerSeriesBall c ρ x) →
    HasPowerSeriesAtUniformlyContinuousOnBall f c ρ →
    HasPowerSeriesAtContinuousAt f c ρ x x-inBall
  uniformAt→continuousAt x-inBall (ν , uniform) =
    ν , λ ε y-inBall x∼y → uniform ε x-inBall y-inBall x∼y

  uniformWithin→continuousAt :
    {ℓ : Level} →
    {D : ℝᶜ → Type ℓ} →
    {f : (x : ℝᶜ) → D x → ℝᶜ} →
    {c x : ℝᶜ} →
    {ρ : ℚ⁺} →
    (x-domain : D x) →
    (x-inBall : InPowerSeriesBall c ρ x) →
    HasPowerSeriesWithinAtUniformlyContinuousOnBall {D = D} f c ρ →
    HasPowerSeriesWithinAtContinuousAt {D = D} f c ρ x x-domain x-inBall
  uniformWithin→continuousAt x-domain x-inBall (ν , uniform) =
    ν ,
    λ ε y-domain y-inBall x∼y →
      uniform ε x-domain y-domain x-inBall y-inBall x∼y


hasPowerSeriesAtWithBounds→uniformlyContinuousOnBall :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesAtWithBounds f c a ρ μ →
  HasPowerSeriesAtUniformlyContinuousOnBall f c ρ
hasPowerSeriesAtWithBounds→uniformlyContinuousOnBall (expansion , bounds) =
  let ν , uniform =
        centeredPowerSeriesSumUniformlyContinuousFromCoefficientBounds
          bounds
  in
  ν , transportUniformAt expansion uniform




hasPowerSeriesWithinAtWithBounds→uniformlyContinuousOnBall :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesWithinAtWithBounds {D = D} f c a ρ μ →
  HasPowerSeriesWithinAtUniformlyContinuousOnBall {D = D} f c ρ
hasPowerSeriesWithinAtWithBounds→uniformlyContinuousOnBall
  (expansion , bounds) =
  let ν , uniform =
        centeredPowerSeriesSumUniformlyContinuousFromCoefficientBounds
          bounds
  in
  ν , transportUniformWithin expansion uniform






hasPowerSeriesAtWithBounds→continuousAt :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesAtWithBounds f c a ρ μ →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesAtContinuousAt f c ρ x x-inBall
hasPowerSeriesAtWithBounds→continuousAt expansion x x-inBall =
  uniformAt→continuousAt
    x-inBall
    (hasPowerSeriesAtWithBounds→uniformlyContinuousOnBall expansion)






hasPowerSeriesWithinAtWithBounds→continuousAt :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesWithinAtWithBounds {D = D} f c a ρ μ →
  (x : ℝᶜ) →
  (x-domain : D x) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesWithinAtContinuousAt {D = D} f c ρ x x-domain x-inBall
hasPowerSeriesWithinAtWithBounds→continuousAt
  expansion x x-domain x-inBall =
  uniformWithin→continuousAt
    x-domain
    x-inBall
    (hasPowerSeriesWithinAtWithBounds→uniformlyContinuousOnBall expansion)
