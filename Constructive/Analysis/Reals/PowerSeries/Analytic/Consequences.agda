{-

Part of Constructive.Analysis.Reals.PowerSeries.Analytic

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Analytic.Consequences where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Rationals using (ℚ)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)

open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Metric.Instances.CauchyReals
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
  using (_+ᶜ_ ; add-close-left)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
  using (_·ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
  using (-ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.Series
  using (AntitoneTailModulus ; TailBound)
open import Constructive.Analysis.Reals.Sequences.Base
  using (maxModulus ; splitModulus)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( addPowerSeries
    ; addPowerSeriesOnBallWithMax
    ; negPowerSeries
    ; negPowerSeriesOnBallWith
    ; powerSeriesSumOnBall-addWithMax
    ; powerSeriesSumOnBall-neg
    ; powerSeriesSumOnBall-rationalScale
    ; powerSeriesSumOnBall-realScale
    ; powerSeriesSumOnBall-subWithMax
    ; rationalScaleModulus
    ; rationalScalePowerSeries
    ; rationalScalePowerSeriesOnBallWith
    ; realScaleModulus
    ; realScalePowerSeries
    ; realScalePowerSeriesOnBallWith
    ; subPowerSeries
    ; subPowerSeriesOnBallWithMax
    )
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct
  using
    ( cauchyProductPowerSeries
    ; cauchyProductPowerSeriesOnBallWithFromMajorants
    ; cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTail
    ; sequenceCauchyProduct
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using
    ( PowerSeriesMajorizedOnBall
    ; majorizedOnBall→hasPowerSeriesOnBallWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals

open import Constructive.Analysis.Reals.PowerSeries.Analytic.Internal
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Core
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Continuity
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Algebra

hasPowerSeriesWithinAtWith-congFunction :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f g : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  ((x : ℝᶜ) → (domain : D x) → f x domain ≡ g x domain) →
  HasPowerSeriesWithinAtWith {D = D} f c a ρ μ →
  HasPowerSeriesWithinAtWith {D = D} g c a ρ μ
hasPowerSeriesWithinAtWith-congFunction f≡g (convergence , sumPath) =
  convergence ,
  λ x domain inBall →
    sym (f≡g x domain) ∙
    sumPath x domain inBall


hasPowerSeriesAtWith→uniformlyContinuousOnBallWith :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  {ν : PrecisionModulus} →
  CenteredPowerSeriesSumUniformlyContinuousOnBallWith
    a
    c
    ρ
    μ
    (fst expansion)
    ν →
  HasPowerSeriesAtUniformlyContinuousOnBallWith f c ρ ν
hasPowerSeriesAtWith→uniformlyContinuousOnBallWith
  expansion
  uniform
  ε
  {x = x}
  {y = y}
  x-inBall
  y-inBall
  x∼y =
  subst2
    (λ u v → MetricSpace.Close CauchyRealsMetricSpace u ε v)
    (sym (snd expansion x x-inBall))
    (sym (snd expansion y y-inBall))
    (uniform ε x-inBall y-inBall x∼y)


hasPowerSeriesAtWith→uniformlyContinuousOnBall :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  CenteredPowerSeriesSumUniformlyContinuousOnBall
    a
    c
    ρ
    μ
    (fst expansion) →
  HasPowerSeriesAtUniformlyContinuousOnBall f c ρ
hasPowerSeriesAtWith→uniformlyContinuousOnBall expansion (ν , uniform) =
  ν ,
  hasPowerSeriesAtWith→uniformlyContinuousOnBallWith expansion uniform


hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  {ν : PrecisionModulus} →
  CenteredPowerSeriesSumUniformlyContinuousOnBallWith
    a
    c
    ρ
    μ
    (fst expansion)
    ν →
  HasPowerSeriesWithinAtUniformlyContinuousOnBallWith {D = D} f c ρ ν
hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallWith
  expansion
  uniform
  ε
  {x = x}
  {y = y}
  x-domain
  y-domain
  x-inBall
  y-inBall
  x∼y =
  subst2
    (λ u v → MetricSpace.Close CauchyRealsMetricSpace u ε v)
    (sym (snd expansion x x-domain x-inBall))
    (sym (snd expansion y y-domain y-inBall))
    (uniform ε x-inBall y-inBall x∼y)


hasPowerSeriesWithinAtWith→uniformlyContinuousOnBall :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  CenteredPowerSeriesSumUniformlyContinuousOnBall
    a
    c
    ρ
    μ
    (fst expansion) →
  HasPowerSeriesWithinAtUniformlyContinuousOnBall {D = D} f c ρ
hasPowerSeriesWithinAtWith→uniformlyContinuousOnBall expansion (ν , uniform) =
  ν ,
  hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallWith expansion uniform


hasPowerSeriesAtWith→continuousAtWith :
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
    a
    ρ
    μ
    (fst expansion)
    (centeredDisplacement c x)
    (InPowerSeriesBall.displacementBound x-inBall)
    ν →
  HasPowerSeriesAtContinuousAtWith f c ρ x x-inBall ν
hasPowerSeriesAtWith→continuousAtWith
  {c = c}
  expansion
  x
  x-inBall
  continuous
  ε
  {y = y}
  y-inBall
  x∼y =
  subst2
    (λ u v → MetricSpace.Close CauchyRealsMetricSpace u ε v)
    (sym (snd expansion x x-inBall))
    (sym (snd expansion y y-inBall))
    (continuous
      ε
      (InPowerSeriesBall.displacementBound y-inBall)
      (add-close-left x∼y (-ᶜ c)))


hasPowerSeriesAtWith→continuousAt :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  PowerSeriesSumContinuousAt
    a
    ρ
    μ
    (fst expansion)
    (centeredDisplacement c x)
    (InPowerSeriesBall.displacementBound x-inBall) →
  HasPowerSeriesAtContinuousAt f c ρ x x-inBall
hasPowerSeriesAtWith→continuousAt expansion x x-inBall (ν , continuous) =
  ν ,
  hasPowerSeriesAtWith→continuousAtWith
    expansion
    x
    x-inBall
    continuous


hasPowerSeriesWithinAtWith→continuousAtWith :
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
    a
    ρ
    μ
    (fst expansion)
    (centeredDisplacement c x)
    (InPowerSeriesBall.displacementBound x-inBall)
    ν →
  HasPowerSeriesWithinAtContinuousAtWith
    {D = D}
    f
    c
    ρ
    x
    x-domain
    x-inBall
    ν
hasPowerSeriesWithinAtWith→continuousAtWith
  {c = c}
  expansion
  x
  x-domain
  x-inBall
  continuous
  ε
  {y = y}
  y-domain
  y-inBall
  x∼y =
  subst2
    (λ u v → MetricSpace.Close CauchyRealsMetricSpace u ε v)
    (sym (snd expansion x x-domain x-inBall))
    (sym (snd expansion y y-domain y-inBall))
    (continuous
      ε
      (InPowerSeriesBall.displacementBound y-inBall)
      (add-close-left x∼y (-ᶜ c)))


hasPowerSeriesWithinAtWith→continuousAt :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  (x : ℝᶜ) →
  (x-domain : D x) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  PowerSeriesSumContinuousAt
    a
    ρ
    μ
    (fst expansion)
    (centeredDisplacement c x)
    (InPowerSeriesBall.displacementBound x-inBall) →
  HasPowerSeriesWithinAtContinuousAt {D = D} f c ρ x x-domain x-inBall
hasPowerSeriesWithinAtWith→continuousAt
  expansion
  x
  x-domain
  x-inBall
  (ν , continuous) =
  ν ,
  hasPowerSeriesWithinAtWith→continuousAtWith
    expansion
    x
    x-domain
    x-inBall
    continuous
