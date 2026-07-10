{-

Strict-subball continuity consequences for ordinary analytic expansions

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Analytic.Consequences.SubballContinuity.Ordinary where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)

open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Metric
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.Series using (SeriesMajorizedBy)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Bounds
  using
    ( PowerSeriesCoefficientBounds
    ; PowerSeriesCoefficientBoundsWith
    ; powerSeriesCoefficientBoundPrecisionFromBallTermBounds
    ; powerSeriesCoefficientBoundsFromBallTermBoundsWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Continuity.Core
  using
    ( powerSeriesBallTermBoundsFromMajorantBoundsWith
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


hasPowerSeriesAtWith→uniformlyContinuousOnSubballFromCoefficientBoundsWith :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesAtWith f c a σ μ) →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  PowerSeriesCoefficientBoundsWith a κ →
  HasPowerSeriesAtUniformlyContinuousOnBallWith
    f
    c
    ρ
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      κ
      ρ
      (powerSeriesLimitApproximationIndex μ))
hasPowerSeriesAtWith→uniformlyContinuousOnSubballFromCoefficientBoundsWith
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
    centeredPowerSeriesSumOnBall _ c ρ _ smallConvergence x x-inBall ≡ f x
  x-sum≡f =
    x-sum≡large ∙ sym (snd expansion x x-inLarge)

  y-sum≡f :
    centeredPowerSeriesSumOnBall _ c ρ _ smallConvergence y y-inBall ≡ f y
  y-sum≡f =
    y-sum≡large ∙ sym (snd expansion y y-inLarge)

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


hasPowerSeriesAtWith→uniformlyContinuousOnSubballFromCoefficientBounds :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a σ μ) →
  radius ρ ℚOrder.< radius σ →
  PowerSeriesCoefficientBounds a →
  HasPowerSeriesAtUniformlyContinuousOnBall f c ρ
hasPowerSeriesAtWith→uniformlyContinuousOnSubballFromCoefficientBounds
  {ρ = ρ}
  {μ = μ}
  expansion
  ρ<σ
  (κ , coeffBounds) =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    κ
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  hasPowerSeriesAtWith→uniformlyContinuousOnSubballFromCoefficientBoundsWith
    expansion
    ρ<σ
    coeffBounds


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
  (expansion , bounds)
  ρ<σ =
  hasPowerSeriesAtWith→uniformlyContinuousOnSubballFromCoefficientBounds
    expansion
    ρ<σ
    bounds


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


hasPowerSeriesAtWith→continuousAtOnSubballFromCoefficientBoundsWith :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesAtWith f c a σ μ) →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  PowerSeriesCoefficientBoundsWith a κ →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesAtContinuousAtWith
    f
    c
    ρ
    x
    x-inBall
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      κ
      ρ
      (powerSeriesLimitApproximationIndex μ))
hasPowerSeriesAtWith→continuousAtOnSubballFromCoefficientBoundsWith
  expansion
  ρ<σ
  coeffBounds
  x
  x-inBall
  ε
  y-inBall
  x∼y =
  hasPowerSeriesAtWith→uniformlyContinuousOnSubballFromCoefficientBoundsWith
    expansion
    ρ<σ
    coeffBounds
    ε
    x-inBall
    y-inBall
    x∼y


hasPowerSeriesAtWith→continuousAtOnSubballFromCoefficientBounds :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a σ μ) →
  radius ρ ℚOrder.< radius σ →
  PowerSeriesCoefficientBounds a →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesAtContinuousAt f c ρ x x-inBall
hasPowerSeriesAtWith→continuousAtOnSubballFromCoefficientBounds
  {ρ = ρ}
  {μ = μ}
  expansion
  ρ<σ
  (κ , coeffBounds)
  x
  x-inBall =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    κ
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  hasPowerSeriesAtWith→continuousAtOnSubballFromCoefficientBoundsWith
    expansion
    ρ<σ
    coeffBounds
    x
    x-inBall


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
hasPowerSeriesAtWithBounds→continuousAtOnSubball
  (expansion , bounds)
  ρ<σ
  x
  x-inBall =
  hasPowerSeriesAtWith→continuousAtOnSubballFromCoefficientBounds
    expansion
    ρ<σ
    bounds
    x
    x-inBall


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


hasPowerSeriesAtWith→uniformlyContinuousOnSubballFromBallTermBoundsWith :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesAtWith f c a σ μ) →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  HasPowerSeriesAtUniformlyContinuousOnBallWith
    f
    c
    ρ
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
      ρ
      (powerSeriesLimitApproximationIndex μ))
hasPowerSeriesAtWith→uniformlyContinuousOnSubballFromBallTermBoundsWith
  {ρ = ρ}
  expansion
  ρ<σ
  termBounds =
  hasPowerSeriesAtWith→uniformlyContinuousOnSubballFromCoefficientBoundsWith
    expansion
    ρ<σ
    (powerSeriesCoefficientBoundsFromBallTermBoundsWith ρ termBounds)


hasPowerSeriesAtWith→uniformlyContinuousOnSubballFromBallTermBounds :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a σ μ) →
  radius ρ ℚOrder.< radius σ →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  HasPowerSeriesAtUniformlyContinuousOnBall f c ρ
hasPowerSeriesAtWith→uniformlyContinuousOnSubballFromBallTermBounds
  {ρ = ρ}
  {μ = μ}
  expansion
  ρ<σ
  (κ , termBounds) =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  hasPowerSeriesAtWith→uniformlyContinuousOnSubballFromBallTermBoundsWith
    expansion
    ρ<σ
    termBounds


hasPowerSeriesAtWith→continuousAtOnSubballFromBallTermBoundsWith :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesAtWith f c a σ μ) →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesAtContinuousAtWith
    f
    c
    ρ
    x
    x-inBall
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
      ρ
      (powerSeriesLimitApproximationIndex μ))
hasPowerSeriesAtWith→continuousAtOnSubballFromBallTermBoundsWith
  {ρ = ρ}
  expansion
  ρ<σ
  termBounds =
  hasPowerSeriesAtWith→continuousAtOnSubballFromCoefficientBoundsWith
    expansion
    ρ<σ
    (powerSeriesCoefficientBoundsFromBallTermBoundsWith ρ termBounds)


hasPowerSeriesAtWith→continuousAtOnSubballFromBallTermBounds :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a σ μ) →
  radius ρ ℚOrder.< radius σ →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesAtContinuousAt f c ρ x x-inBall
hasPowerSeriesAtWith→continuousAtOnSubballFromBallTermBounds
  {ρ = ρ}
  {μ = μ}
  expansion
  ρ<σ
  (κ , termBounds)
  x
  x-inBall =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  hasPowerSeriesAtWith→continuousAtOnSubballFromBallTermBoundsWith
    expansion
    ρ<σ
    termBounds
    x
    x-inBall


hasPowerSeriesAtWith→uniformlyContinuousOnSubballFromMajorantBoundsWith :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {v : ℕ → ℝᶜ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesAtWith f c a σ μ) →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    SeriesMajorizedBy (powerSeriesTerm a h) v) →
  ((n : ℕ) → BoundedByᶜ (κ n) (v n)) →
  HasPowerSeriesAtUniformlyContinuousOnBallWith
    f
    c
    ρ
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
      ρ
      (powerSeriesLimitApproximationIndex μ))
hasPowerSeriesAtWith→uniformlyContinuousOnSubballFromMajorantBoundsWith
  expansion
  ρ<σ
  termMajorized
  majorantBounds =
  hasPowerSeriesAtWith→uniformlyContinuousOnSubballFromBallTermBoundsWith
    expansion
    ρ<σ
    (powerSeriesBallTermBoundsFromMajorantBoundsWith
      termMajorized
      majorantBounds)


hasPowerSeriesAtWith→uniformlyContinuousOnSubballFromMajorantBounds :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {v : ℕ → ℝᶜ} →
  (expansion : HasPowerSeriesAtWith f c a σ μ) →
  radius ρ ℚOrder.< radius σ →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    SeriesMajorizedBy (powerSeriesTerm a h) v) →
  Σ[ κ ∈ (ℕ → ℚ⁺) ] ((n : ℕ) → BoundedByᶜ (κ n) (v n)) →
  HasPowerSeriesAtUniformlyContinuousOnBall f c ρ
hasPowerSeriesAtWith→uniformlyContinuousOnSubballFromMajorantBounds
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
  hasPowerSeriesAtWith→uniformlyContinuousOnSubballFromMajorantBoundsWith
    expansion
    ρ<σ
    termMajorized
    majorantBounds


hasPowerSeriesAtWith→continuousAtOnSubballFromMajorantBoundsWith :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {v : ℕ → ℝᶜ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesAtWith f c a σ μ) →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    SeriesMajorizedBy (powerSeriesTerm a h) v) →
  ((n : ℕ) → BoundedByᶜ (κ n) (v n)) →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesAtContinuousAtWith
    f
    c
    ρ
    x
    x-inBall
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
      ρ
      (powerSeriesLimitApproximationIndex μ))
hasPowerSeriesAtWith→continuousAtOnSubballFromMajorantBoundsWith
  expansion
  ρ<σ
  termMajorized
  majorantBounds =
  hasPowerSeriesAtWith→continuousAtOnSubballFromBallTermBoundsWith
    expansion
    ρ<σ
    (powerSeriesBallTermBoundsFromMajorantBoundsWith
      termMajorized
      majorantBounds)


hasPowerSeriesAtWith→continuousAtOnSubballFromMajorantBounds :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {v : ℕ → ℝᶜ} →
  (expansion : HasPowerSeriesAtWith f c a σ μ) →
  radius ρ ℚOrder.< radius σ →
  ((h : ℝᶜ) →
    BoundedByᶜ ρ h →
    SeriesMajorizedBy (powerSeriesTerm a h) v) →
  Σ[ κ ∈ (ℕ → ℚ⁺) ] ((n : ℕ) → BoundedByᶜ (κ n) (v n)) →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesAtContinuousAt f c ρ x x-inBall
hasPowerSeriesAtWith→continuousAtOnSubballFromMajorantBounds
  {ρ = ρ}
  {μ = μ}
  expansion
  ρ<σ
  termMajorized
  (κ , majorantBounds)
  x
  x-inBall =
  powerSeriesPartialSumsModulusFromCoefficientBounds
    (powerSeriesCoefficientBoundPrecisionFromBallTermBounds ρ κ)
    ρ
    (powerSeriesLimitApproximationIndex μ) ,
  hasPowerSeriesAtWith→continuousAtOnSubballFromMajorantBoundsWith
    expansion
    ρ<σ
    termMajorized
    majorantBounds
    x
    x-inBall
