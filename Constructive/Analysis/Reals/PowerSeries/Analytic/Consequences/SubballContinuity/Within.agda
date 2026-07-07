{-

Strict-subball continuity consequences for within-domain analytic expansions

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Analytic.Consequences.SubballContinuity.Within where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)

open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Metric.Instances.CauchyReals
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.Series using (SeriesMajorizedBy)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Continuity.Core
  using
    ( PowerSeriesCoefficientBounds
    ; PowerSeriesCoefficientBoundsWith
    ; powerSeriesBallTermBoundsFromMajorantBoundsWith
    ; powerSeriesCoefficientBoundPrecisionFromBallTermBounds
    ; powerSeriesCoefficientBoundsFromBallTermBoundsWith
    ; powerSeriesLimitApproximationIndex
    ; powerSeriesPartialSumsModulusFromCoefficientBounds
    )
open import Constructive.Analysis.Reals.PowerSeries.Continuity.Subball
  using (centeredPowerSeriesSumUniformlyContinuousOnSubballFromCoefficientBoundsWith)
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals

open import Constructive.Analysis.Reals.PowerSeries.Analytic.Core
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Continuity
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Consequences.SubballContinuity.Internal
  using (inPowerSeriesSubball→largerBall)


hasPowerSeriesWithinAtWith→uniformlyContinuousOnSubballFromCoefficientBoundsWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a σ μ) →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  PowerSeriesCoefficientBoundsWith a κ →
  HasPowerSeriesWithinAtUniformlyContinuousOnBallWith
    {D = D}
    f
    c
    ρ
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      κ
      ρ
      (powerSeriesLimitApproximationIndex μ))
hasPowerSeriesWithinAtWith→uniformlyContinuousOnSubballFromCoefficientBoundsWith
  {f = f}
  {c = c}
  {ρ = ρ}
  {σ = σ}
  expansion
  ρ<σ
  coeffBounds
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
    x-sum≡f
    y-sum≡f
    small-close
  where
  smallConvergence : HasPowerSeriesOnBallWith _ ρ _
  smallConvergence =
    hasPowerSeriesOnSmallerBallWith {ρ = ρ} {σ = σ} ρ<σ (fst expansion)

  x-inLarge : InPowerSeriesBall c σ x
  x-inLarge =
    inPowerSeriesSubball→largerBall ρ<σ x-inBall

  y-inLarge : InPowerSeriesBall c σ y
  y-inLarge =
    inPowerSeriesSubball→largerBall ρ<σ y-inBall

  x-sum≡large :
    centeredPowerSeriesSumOnBall _ c ρ _ smallConvergence x x-inBall ≡
    centeredPowerSeriesSumOnBall _ c σ _ (fst expansion) x x-inLarge
  x-sum≡large =
    centeredPowerSeriesSumOnBall-data-independent
      smallConvergence
      (fst expansion)
      x
      x-inBall
      x-inLarge

  y-sum≡large :
    centeredPowerSeriesSumOnBall _ c ρ _ smallConvergence y y-inBall ≡
    centeredPowerSeriesSumOnBall _ c σ _ (fst expansion) y y-inLarge
  y-sum≡large =
    centeredPowerSeriesSumOnBall-data-independent
      smallConvergence
      (fst expansion)
      y
      y-inBall
      y-inLarge

  x-sum≡f :
    centeredPowerSeriesSumOnBall _ c ρ _ smallConvergence x x-inBall ≡
    f x x-domain
  x-sum≡f =
    x-sum≡large ∙ sym (snd expansion x x-domain x-inLarge)

  y-sum≡f :
    centeredPowerSeriesSumOnBall _ c ρ _ smallConvergence y y-inBall ≡
    f y y-domain
  y-sum≡f =
    y-sum≡large ∙ sym (snd expansion y y-domain y-inLarge)

  small-close :
    MetricSpace.Close
      CauchyRealsMetricSpace
      (centeredPowerSeriesSumOnBall _ c ρ _ smallConvergence x x-inBall)
      ε
      (centeredPowerSeriesSumOnBall _ c ρ _ smallConvergence y y-inBall)
  small-close =
    centeredPowerSeriesSumUniformlyContinuousOnSubballFromCoefficientBoundsWith
      {c = c}
      {convergence = fst expansion}
      ρ<σ
      coeffBounds
      ε
      x-inBall
      y-inBall
      x∼y


hasPowerSeriesWithinAtWith→uniformlyContinuousOnSubballFromCoefficientBounds :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a σ μ) →
  radius ρ ℚOrder.< radius σ →
  PowerSeriesCoefficientBounds a →
  HasPowerSeriesWithinAtUniformlyContinuousOnBall {D = D} f c ρ
hasPowerSeriesWithinAtWith→uniformlyContinuousOnSubballFromCoefficientBounds
  {ρ = ρ}
  {μ = μ}
  expansion
  ρ<σ
  (κ , coeffBounds) =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    κ
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  hasPowerSeriesWithinAtWith→uniformlyContinuousOnSubballFromCoefficientBoundsWith
    expansion
    ρ<σ
    coeffBounds


hasPowerSeriesWithinAtWith→continuousAtOnSubballFromCoefficientBoundsWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a σ μ) →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  PowerSeriesCoefficientBoundsWith a κ →
  (x : ℝᶜ) →
  (x-domain : D x) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesWithinAtContinuousAtWith
    {D = D}
    f
    c
    ρ
    x
    x-domain
    x-inBall
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      κ
      ρ
      (powerSeriesLimitApproximationIndex μ))
hasPowerSeriesWithinAtWith→continuousAtOnSubballFromCoefficientBoundsWith
  expansion
  ρ<σ
  coeffBounds
  x
  x-domain
  x-inBall
  ε
  y-domain
  y-inBall
  x∼y =
  hasPowerSeriesWithinAtWith→uniformlyContinuousOnSubballFromCoefficientBoundsWith
    expansion
    ρ<σ
    coeffBounds
    ε
    x-domain
    y-domain
    x-inBall
    y-inBall
    x∼y


hasPowerSeriesWithinAtWith→continuousAtOnSubballFromCoefficientBounds :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a σ μ) →
  radius ρ ℚOrder.< radius σ →
  PowerSeriesCoefficientBounds a →
  (x : ℝᶜ) →
  (x-domain : D x) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesWithinAtContinuousAt {D = D} f c ρ x x-domain x-inBall
hasPowerSeriesWithinAtWith→continuousAtOnSubballFromCoefficientBounds
  {ρ = ρ}
  {μ = μ}
  expansion
  ρ<σ
  (κ , coeffBounds)
  x
  x-domain
  x-inBall =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    κ
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  hasPowerSeriesWithinAtWith→continuousAtOnSubballFromCoefficientBoundsWith
    expansion
    ρ<σ
    coeffBounds
    x
    x-domain
    x-inBall


hasPowerSeriesWithinAtWith→uniformlyContinuousOnSubballFromBallTermBoundsWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a σ μ) →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  HasPowerSeriesWithinAtUniformlyContinuousOnBallWith
    {D = D}
    f
    c
    ρ
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
      ρ
      (powerSeriesLimitApproximationIndex μ))
hasPowerSeriesWithinAtWith→uniformlyContinuousOnSubballFromBallTermBoundsWith
  {ρ = ρ}
  expansion
  ρ<σ
  termBounds =
  hasPowerSeriesWithinAtWith→uniformlyContinuousOnSubballFromCoefficientBoundsWith
    expansion
    ρ<σ
    (powerSeriesCoefficientBoundsFromBallTermBoundsWith ρ termBounds)


hasPowerSeriesWithinAtWith→uniformlyContinuousOnSubballFromBallTermBounds :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a σ μ) →
  radius ρ ℚOrder.< radius σ →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  HasPowerSeriesWithinAtUniformlyContinuousOnBall {D = D} f c ρ
hasPowerSeriesWithinAtWith→uniformlyContinuousOnSubballFromBallTermBounds
  {ρ = ρ}
  {μ = μ}
  expansion
  ρ<σ
  (κ , termBounds) =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  hasPowerSeriesWithinAtWith→uniformlyContinuousOnSubballFromBallTermBoundsWith
    expansion
    ρ<σ
    termBounds


hasPowerSeriesWithinAtWith→continuousAtOnSubballFromBallTermBoundsWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a σ μ) →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  (x : ℝᶜ) →
  (x-domain : D x) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesWithinAtContinuousAtWith
    {D = D}
    f
    c
    ρ
    x
    x-domain
    x-inBall
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
      ρ
      (powerSeriesLimitApproximationIndex μ))
hasPowerSeriesWithinAtWith→continuousAtOnSubballFromBallTermBoundsWith
  {ρ = ρ}
  expansion
  ρ<σ
  termBounds =
  hasPowerSeriesWithinAtWith→continuousAtOnSubballFromCoefficientBoundsWith
    expansion
    ρ<σ
    (powerSeriesCoefficientBoundsFromBallTermBoundsWith ρ termBounds)


hasPowerSeriesWithinAtWith→continuousAtOnSubballFromBallTermBounds :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a σ μ) →
  radius ρ ℚOrder.< radius σ →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  (x : ℝᶜ) →
  (x-domain : D x) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesWithinAtContinuousAt {D = D} f c ρ x x-domain x-inBall
hasPowerSeriesWithinAtWith→continuousAtOnSubballFromBallTermBounds
  {ρ = ρ}
  {μ = μ}
  expansion
  ρ<σ
  (κ , termBounds)
  x
  x-domain
  x-inBall =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  hasPowerSeriesWithinAtWith→continuousAtOnSubballFromBallTermBoundsWith
    expansion
    ρ<σ
    termBounds
    x
    x-domain
    x-inBall


hasPowerSeriesWithinAtWith→uniformlyContinuousOnSubballFromMajorantBoundsWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {v : ℕ → ℝᶜ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a σ μ) →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    SeriesMajorizedBy (powerSeriesTerm a h) v) →
  ((n : ℕ) → BoundedByᶜ (κ n) (v n)) →
  HasPowerSeriesWithinAtUniformlyContinuousOnBallWith
    {D = D}
    f
    c
    ρ
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
      ρ
      (powerSeriesLimitApproximationIndex μ))
hasPowerSeriesWithinAtWith→uniformlyContinuousOnSubballFromMajorantBoundsWith
  expansion
  ρ<σ
  termMajorized
  majorantBounds =
  hasPowerSeriesWithinAtWith→uniformlyContinuousOnSubballFromBallTermBoundsWith
    expansion
    ρ<σ
    (powerSeriesBallTermBoundsFromMajorantBoundsWith
      termMajorized
      majorantBounds)


hasPowerSeriesWithinAtWith→uniformlyContinuousOnSubballFromMajorantBounds :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {v : ℕ → ℝᶜ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a σ μ) →
  radius ρ ℚOrder.< radius σ →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    SeriesMajorizedBy (powerSeriesTerm a h) v) →
  Σ[ κ ∈ (ℕ → ℚ⁺) ] ((n : ℕ) → BoundedByᶜ (κ n) (v n)) →
  HasPowerSeriesWithinAtUniformlyContinuousOnBall {D = D} f c ρ
hasPowerSeriesWithinAtWith→uniformlyContinuousOnSubballFromMajorantBounds
  {ρ = ρ}
  {μ = μ}
  expansion
  ρ<σ
  termMajorized
  (κ , majorantBounds) =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  hasPowerSeriesWithinAtWith→uniformlyContinuousOnSubballFromMajorantBoundsWith
    expansion
    ρ<σ
    termMajorized
    majorantBounds


hasPowerSeriesWithinAtWith→continuousAtOnSubballFromMajorantBoundsWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {v : ℕ → ℝᶜ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a σ μ) →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    SeriesMajorizedBy (powerSeriesTerm a h) v) →
  ((n : ℕ) → BoundedByᶜ (κ n) (v n)) →
  (x : ℝᶜ) →
  (x-domain : D x) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesWithinAtContinuousAtWith
    {D = D}
    f
    c
    ρ
    x
    x-domain
    x-inBall
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
      ρ
      (powerSeriesLimitApproximationIndex μ))
hasPowerSeriesWithinAtWith→continuousAtOnSubballFromMajorantBoundsWith
  expansion
  ρ<σ
  termMajorized
  majorantBounds =
  hasPowerSeriesWithinAtWith→continuousAtOnSubballFromBallTermBoundsWith
    expansion
    ρ<σ
    (powerSeriesBallTermBoundsFromMajorantBoundsWith
      termMajorized
      majorantBounds)


hasPowerSeriesWithinAtWith→continuousAtOnSubballFromMajorantBounds :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {v : ℕ → ℝᶜ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a σ μ) →
  radius ρ ℚOrder.< radius σ →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    SeriesMajorizedBy (powerSeriesTerm a h) v) →
  Σ[ κ ∈ (ℕ → ℚ⁺) ] ((n : ℕ) → BoundedByᶜ (κ n) (v n)) →
  (x : ℝᶜ) →
  (x-domain : D x) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesWithinAtContinuousAt {D = D} f c ρ x x-domain x-inBall
hasPowerSeriesWithinAtWith→continuousAtOnSubballFromMajorantBounds
  {ρ = ρ}
  {μ = μ}
  expansion
  ρ<σ
  termMajorized
  (κ , majorantBounds)
  x
  x-domain
  x-inBall =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  hasPowerSeriesWithinAtWith→continuousAtOnSubballFromMajorantBoundsWith
    expansion
    ρ<σ
    termMajorized
    majorantBounds
    x
    x-domain
    x-inBall
