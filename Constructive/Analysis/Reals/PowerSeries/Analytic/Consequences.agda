{-

Part of Constructive.Analysis.Reals.PowerSeries.Analytic

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Analytic.Consequences where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
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
open import Constructive.Analysis.Reals.Calculus.Derivative
  using (HasDerivativeAtWith ; hasDerivativeAtWith-local-cong)
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
open import Constructive.Analysis.Reals.PowerSeries.Continuity
  using
    ( PowerSeriesCoefficientBounds
    ; PowerSeriesCoefficientBoundsWith
    ; PowerSeriesPartialSumsUniformlyContinuousOnBall
    ; PowerSeriesPartialSumsUniformlyContinuousOnBallWith
    ; centeredPowerSeriesSumUniformlyContinuousFromBallTermBounds
    ; centeredPowerSeriesSumUniformlyContinuousFromBallTermBoundsCanonical
    ; centeredPowerSeriesSumUniformlyContinuousFromBallTermBoundsCanonicalWith
    ; centeredPowerSeriesSumUniformlyContinuousFromBallTermBoundsWith
    ; centeredPowerSeriesSumUniformlyContinuousFromCoefficientBounds
    ; centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonical
    ; centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonicalWith
    ; centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsWith
    ; centeredPowerSeriesSumUniformlyContinuousFromPartialSums
    ; powerSeriesCoefficientBoundPrecisionFromBallTermBounds
    ; powerSeriesLimitApproximationIndex
    ; powerSeriesPartialSumsModulusFromCoefficientBounds
    ; powerSeriesSumContinuousAtFromBallTermBounds
    ; powerSeriesSumContinuousAtFromBallTermBoundsCanonical
    ; powerSeriesSumContinuousAtFromBallTermBoundsCanonicalWith
    ; powerSeriesSumContinuousAtFromBallTermBoundsWith
    ; powerSeriesSumContinuousAtFromCoefficientBounds
    ; powerSeriesSumContinuousAtFromCoefficientBoundsCanonical
    ; powerSeriesSumContinuousAtFromCoefficientBoundsCanonicalWith
    ; powerSeriesSumContinuousAtFromCoefficientBoundsWith
    ; powerSeriesSumContinuousAtFromPartialSums
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
      let
        x+h-inBall = forward-inBall ε η η≤νε h h-bound
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


hasPowerSeriesAtWith→uniformlyContinuousOnBallFromPartialSumsWith :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  {ν : PrecisionModulus} →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBallWith a ρ χ ν →
  HasPowerSeriesAtUniformlyContinuousOnBallWith f c ρ ν
hasPowerSeriesAtWith→uniformlyContinuousOnBallFromPartialSumsWith
  expansion
  index-large
  partial-cont =
  hasPowerSeriesAtWith→uniformlyContinuousOnBallWith
    expansion
    (centeredPowerSeriesSumUniformlyContinuousFromPartialSums
      index-large
      partial-cont)


hasPowerSeriesAtWith→uniformlyContinuousOnBallFromPartialSums :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBall a ρ χ →
  HasPowerSeriesAtUniformlyContinuousOnBall f c ρ
hasPowerSeriesAtWith→uniformlyContinuousOnBallFromPartialSums
  expansion
  index-large
  (ν , partial-cont) =
  ν ,
  hasPowerSeriesAtWith→uniformlyContinuousOnBallFromPartialSumsWith
    expansion
    index-large
    partial-cont


hasPowerSeriesAtWith→uniformlyContinuousOnBallFromCoefficientBoundsWith :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesCoefficientBoundsWith a κ →
  HasPowerSeriesAtUniformlyContinuousOnBallWith
    f
    c
    ρ
    (powerSeriesPartialSumsModulusFromCoefficientBounds κ ρ χ)
hasPowerSeriesAtWith→uniformlyContinuousOnBallFromCoefficientBoundsWith
  expansion
  index-large
  coeffBounds =
  hasPowerSeriesAtWith→uniformlyContinuousOnBallWith
    expansion
    (centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsWith
      index-large
      coeffBounds)


hasPowerSeriesAtWith→uniformlyContinuousOnBallFromCoefficientBounds :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesCoefficientBounds a →
  HasPowerSeriesAtUniformlyContinuousOnBall f c ρ
hasPowerSeriesAtWith→uniformlyContinuousOnBallFromCoefficientBounds
  expansion
  index-large
  bounds =
  hasPowerSeriesAtWith→uniformlyContinuousOnBall
    expansion
    (centeredPowerSeriesSumUniformlyContinuousFromCoefficientBounds
      index-large
      bounds)


hasPowerSeriesAtWith→uniformlyContinuousOnBallFromCoefficientBoundsCanonicalWith :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  PowerSeriesCoefficientBoundsWith a κ →
  HasPowerSeriesAtUniformlyContinuousOnBallWith
    f
    c
    ρ
    (powerSeriesPartialSumsModulusFromCoefficientBounds
      κ
      ρ
      (powerSeriesLimitApproximationIndex μ))
hasPowerSeriesAtWith→uniformlyContinuousOnBallFromCoefficientBoundsCanonicalWith
  expansion
  coeffBounds =
  hasPowerSeriesAtWith→uniformlyContinuousOnBallWith
    expansion
    (centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonicalWith
      coeffBounds)


hasPowerSeriesAtWith→uniformlyContinuousOnBallFromCoefficientBoundsCanonical :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  PowerSeriesCoefficientBounds a →
  HasPowerSeriesAtUniformlyContinuousOnBall f c ρ
hasPowerSeriesAtWith→uniformlyContinuousOnBallFromCoefficientBoundsCanonical
  expansion
  bounds =
  hasPowerSeriesAtWith→uniformlyContinuousOnBall
    expansion
    (centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonical
      bounds)


hasPowerSeriesAtWith→uniformlyContinuousOnBallFromBallTermBoundsWith :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
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
      χ)
hasPowerSeriesAtWith→uniformlyContinuousOnBallFromBallTermBoundsWith
  expansion
  index-large
  termBounds =
  hasPowerSeriesAtWith→uniformlyContinuousOnBallWith
    expansion
    (centeredPowerSeriesSumUniformlyContinuousFromBallTermBoundsWith
      index-large
      termBounds)


hasPowerSeriesAtWith→uniformlyContinuousOnBallFromBallTermBounds :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  HasPowerSeriesAtUniformlyContinuousOnBall f c ρ
hasPowerSeriesAtWith→uniformlyContinuousOnBallFromBallTermBounds
  expansion
  index-large
  bounds =
  hasPowerSeriesAtWith→uniformlyContinuousOnBall
    expansion
    (centeredPowerSeriesSumUniformlyContinuousFromBallTermBounds
      index-large
      bounds)


hasPowerSeriesAtWith→uniformlyContinuousOnBallFromBallTermBoundsCanonicalWith :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
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
hasPowerSeriesAtWith→uniformlyContinuousOnBallFromBallTermBoundsCanonicalWith
  expansion
  termBounds =
  hasPowerSeriesAtWith→uniformlyContinuousOnBallWith
    expansion
    (centeredPowerSeriesSumUniformlyContinuousFromBallTermBoundsCanonicalWith
      termBounds)


hasPowerSeriesAtWith→uniformlyContinuousOnBallFromBallTermBoundsCanonical :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  HasPowerSeriesAtUniformlyContinuousOnBall f c ρ
hasPowerSeriesAtWith→uniformlyContinuousOnBallFromBallTermBoundsCanonical
  expansion
  bounds =
  hasPowerSeriesAtWith→uniformlyContinuousOnBall
    expansion
    (centeredPowerSeriesSumUniformlyContinuousFromBallTermBoundsCanonical
      bounds)


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


hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromPartialSumsWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  {ν : PrecisionModulus} →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBallWith a ρ χ ν →
  HasPowerSeriesWithinAtUniformlyContinuousOnBallWith {D = D} f c ρ ν
hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromPartialSumsWith
  expansion
  index-large
  partial-cont =
  hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallWith
    expansion
    (centeredPowerSeriesSumUniformlyContinuousFromPartialSums
      index-large
      partial-cont)


hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromPartialSums :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBall a ρ χ →
  HasPowerSeriesWithinAtUniformlyContinuousOnBall {D = D} f c ρ
hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromPartialSums
  expansion
  index-large
  (ν , partial-cont) =
  ν ,
  hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromPartialSumsWith
    expansion
    index-large
    partial-cont


hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromCoefficientBoundsWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesCoefficientBoundsWith a κ →
  HasPowerSeriesWithinAtUniformlyContinuousOnBallWith
    {D = D}
    f
    c
    ρ
    (powerSeriesPartialSumsModulusFromCoefficientBounds κ ρ χ)
hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromCoefficientBoundsWith
  expansion
  index-large
  coeffBounds =
  hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallWith
    expansion
    (centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsWith
      index-large
      coeffBounds)


hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromCoefficientBounds :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesCoefficientBounds a →
  HasPowerSeriesWithinAtUniformlyContinuousOnBall {D = D} f c ρ
hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromCoefficientBounds
  expansion
  index-large
  bounds =
  hasPowerSeriesWithinAtWith→uniformlyContinuousOnBall
    expansion
    (centeredPowerSeriesSumUniformlyContinuousFromCoefficientBounds
      index-large
      bounds)


hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromCoefficientBoundsCanonicalWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
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
hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromCoefficientBoundsCanonicalWith
  expansion
  coeffBounds =
  hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallWith
    expansion
    (centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonicalWith
      coeffBounds)


hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromCoefficientBoundsCanonical :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  PowerSeriesCoefficientBounds a →
  HasPowerSeriesWithinAtUniformlyContinuousOnBall {D = D} f c ρ
hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromCoefficientBoundsCanonical
  expansion
  bounds =
  hasPowerSeriesWithinAtWith→uniformlyContinuousOnBall
    expansion
    (centeredPowerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonical
      bounds)


hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromBallTermBoundsWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
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
      χ)
hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromBallTermBoundsWith
  expansion
  index-large
  termBounds =
  hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallWith
    expansion
    (centeredPowerSeriesSumUniformlyContinuousFromBallTermBoundsWith
      index-large
      termBounds)


hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromBallTermBounds :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  HasPowerSeriesWithinAtUniformlyContinuousOnBall {D = D} f c ρ
hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromBallTermBounds
  expansion
  index-large
  bounds =
  hasPowerSeriesWithinAtWith→uniformlyContinuousOnBall
    expansion
    (centeredPowerSeriesSumUniformlyContinuousFromBallTermBounds
      index-large
      bounds)


hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromBallTermBoundsCanonicalWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
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
hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromBallTermBoundsCanonicalWith
  expansion
  termBounds =
  hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallWith
    expansion
    (centeredPowerSeriesSumUniformlyContinuousFromBallTermBoundsCanonicalWith
      termBounds)


hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromBallTermBoundsCanonical :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  HasPowerSeriesWithinAtUniformlyContinuousOnBall {D = D} f c ρ
hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallFromBallTermBoundsCanonical
  expansion
  bounds =
  hasPowerSeriesWithinAtWith→uniformlyContinuousOnBall
    expansion
    (centeredPowerSeriesSumUniformlyContinuousFromBallTermBoundsCanonical
      bounds)


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


hasPowerSeriesAtWith→continuousAtFromPartialSumsWith :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  {ν : PrecisionModulus} →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBallWith a ρ χ ν →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesAtContinuousAtWith f c ρ x x-inBall ν
hasPowerSeriesAtWith→continuousAtFromPartialSumsWith
  {c = c}
  expansion
  index-large
  partial-cont
  x
  x-inBall =
  hasPowerSeriesAtWith→continuousAtWith
    expansion
    x
    x-inBall
    (powerSeriesSumContinuousAtFromPartialSums
      index-large
      partial-cont
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound x-inBall))


hasPowerSeriesAtWith→continuousAtFromPartialSums :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBall a ρ χ →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesAtContinuousAt f c ρ x x-inBall
hasPowerSeriesAtWith→continuousAtFromPartialSums
  expansion
  index-large
  (ν , partial-cont)
  x
  x-inBall =
  ν ,
  hasPowerSeriesAtWith→continuousAtFromPartialSumsWith
    expansion
    index-large
    partial-cont
    x
    x-inBall


hasPowerSeriesAtWith→continuousAtFromCoefficientBoundsWith :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesCoefficientBoundsWith a κ →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesAtContinuousAtWith
    f
    c
    ρ
    x
    x-inBall
    (powerSeriesPartialSumsModulusFromCoefficientBounds κ ρ χ)
hasPowerSeriesAtWith→continuousAtFromCoefficientBoundsWith
  {c = c}
  expansion
  index-large
  coeffBounds
  x
  x-inBall =
  hasPowerSeriesAtWith→continuousAtWith
    expansion
    x
    x-inBall
    (powerSeriesSumContinuousAtFromCoefficientBoundsWith
      index-large
      coeffBounds
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound x-inBall))


hasPowerSeriesAtWith→continuousAtFromCoefficientBounds :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesCoefficientBounds a →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesAtContinuousAt f c ρ x x-inBall
hasPowerSeriesAtWith→continuousAtFromCoefficientBounds
  {c = c}
  expansion
  index-large
  bounds
  x
  x-inBall =
  hasPowerSeriesAtWith→continuousAt
    expansion
    x
    x-inBall
    (powerSeriesSumContinuousAtFromCoefficientBounds
      index-large
      bounds
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound x-inBall))


hasPowerSeriesAtWith→continuousAtFromCoefficientBoundsCanonicalWith :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
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
hasPowerSeriesAtWith→continuousAtFromCoefficientBoundsCanonicalWith
  {c = c}
  expansion
  coeffBounds
  x
  x-inBall =
  hasPowerSeriesAtWith→continuousAtWith
    expansion
    x
    x-inBall
    (powerSeriesSumContinuousAtFromCoefficientBoundsCanonicalWith
      coeffBounds
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound x-inBall))


hasPowerSeriesAtWith→continuousAtFromCoefficientBoundsCanonical :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  PowerSeriesCoefficientBounds a →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesAtContinuousAt f c ρ x x-inBall
hasPowerSeriesAtWith→continuousAtFromCoefficientBoundsCanonical
  {c = c}
  expansion
  bounds
  x
  x-inBall =
  hasPowerSeriesAtWith→continuousAt
    expansion
    x
    x-inBall
    (powerSeriesSumContinuousAtFromCoefficientBoundsCanonical
      bounds
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound x-inBall))


hasPowerSeriesAtWith→continuousAtFromBallTermBoundsWith :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
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
      χ)
hasPowerSeriesAtWith→continuousAtFromBallTermBoundsWith
  {c = c}
  expansion
  index-large
  termBounds
  x
  x-inBall =
  hasPowerSeriesAtWith→continuousAtWith
    expansion
    x
    x-inBall
    (powerSeriesSumContinuousAtFromBallTermBoundsWith
      index-large
      termBounds
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound x-inBall))


hasPowerSeriesAtWith→continuousAtFromBallTermBounds :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesAtContinuousAt f c ρ x x-inBall
hasPowerSeriesAtWith→continuousAtFromBallTermBounds
  {c = c}
  expansion
  index-large
  bounds
  x
  x-inBall =
  hasPowerSeriesAtWith→continuousAt
    expansion
    x
    x-inBall
    (powerSeriesSumContinuousAtFromBallTermBounds
      index-large
      bounds
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound x-inBall))


hasPowerSeriesAtWith→continuousAtFromBallTermBoundsCanonicalWith :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
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
hasPowerSeriesAtWith→continuousAtFromBallTermBoundsCanonicalWith
  {c = c}
  expansion
  termBounds
  x
  x-inBall =
  hasPowerSeriesAtWith→continuousAtWith
    expansion
    x
    x-inBall
    (powerSeriesSumContinuousAtFromBallTermBoundsCanonicalWith
      termBounds
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound x-inBall))


hasPowerSeriesAtWith→continuousAtFromBallTermBoundsCanonical :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesAtContinuousAt f c ρ x x-inBall
hasPowerSeriesAtWith→continuousAtFromBallTermBoundsCanonical
  {c = c}
  expansion
  bounds
  x
  x-inBall =
  hasPowerSeriesAtWith→continuousAt
    expansion
    x
    x-inBall
    (powerSeriesSumContinuousAtFromBallTermBoundsCanonical
      bounds
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound x-inBall))


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


hasPowerSeriesWithinAtWith→continuousAtFromPartialSumsWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  {ν : PrecisionModulus} →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBallWith a ρ χ ν →
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
    ν
hasPowerSeriesWithinAtWith→continuousAtFromPartialSumsWith
  {c = c}
  expansion
  index-large
  partial-cont
  x
  x-domain
  x-inBall =
  hasPowerSeriesWithinAtWith→continuousAtWith
    expansion
    x
    x-domain
    x-inBall
    (powerSeriesSumContinuousAtFromPartialSums
      index-large
      partial-cont
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound x-inBall))


hasPowerSeriesWithinAtWith→continuousAtFromPartialSums :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesPartialSumsUniformlyContinuousOnBall a ρ χ →
  (x : ℝᶜ) →
  (x-domain : D x) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesWithinAtContinuousAt {D = D} f c ρ x x-domain x-inBall
hasPowerSeriesWithinAtWith→continuousAtFromPartialSums
  expansion
  index-large
  (ν , partial-cont)
  x
  x-domain
  x-inBall =
  ν ,
  hasPowerSeriesWithinAtWith→continuousAtFromPartialSumsWith
    expansion
    index-large
    partial-cont
    x
    x-domain
    x-inBall


hasPowerSeriesWithinAtWith→continuousAtFromCoefficientBoundsWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
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
    (powerSeriesPartialSumsModulusFromCoefficientBounds κ ρ χ)
hasPowerSeriesWithinAtWith→continuousAtFromCoefficientBoundsWith
  {c = c}
  expansion
  index-large
  coeffBounds
  x
  x-domain
  x-inBall =
  hasPowerSeriesWithinAtWith→continuousAtWith
    expansion
    x
    x-domain
    x-inBall
    (powerSeriesSumContinuousAtFromCoefficientBoundsWith
      index-large
      coeffBounds
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound x-inBall))


hasPowerSeriesWithinAtWith→continuousAtFromCoefficientBounds :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  PowerSeriesCoefficientBounds a →
  (x : ℝᶜ) →
  (x-domain : D x) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesWithinAtContinuousAt {D = D} f c ρ x x-domain x-inBall
hasPowerSeriesWithinAtWith→continuousAtFromCoefficientBounds
  {c = c}
  expansion
  index-large
  bounds
  x
  x-domain
  x-inBall =
  hasPowerSeriesWithinAtWith→continuousAt
    expansion
    x
    x-domain
    x-inBall
    (powerSeriesSumContinuousAtFromCoefficientBounds
      index-large
      bounds
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound x-inBall))


hasPowerSeriesWithinAtWith→continuousAtFromCoefficientBoundsCanonicalWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
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
hasPowerSeriesWithinAtWith→continuousAtFromCoefficientBoundsCanonicalWith
  {c = c}
  expansion
  coeffBounds
  x
  x-domain
  x-inBall =
  hasPowerSeriesWithinAtWith→continuousAtWith
    expansion
    x
    x-domain
    x-inBall
    (powerSeriesSumContinuousAtFromCoefficientBoundsCanonicalWith
      coeffBounds
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound x-inBall))


hasPowerSeriesWithinAtWith→continuousAtFromCoefficientBoundsCanonical :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  PowerSeriesCoefficientBounds a →
  (x : ℝᶜ) →
  (x-domain : D x) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesWithinAtContinuousAt {D = D} f c ρ x x-domain x-inBall
hasPowerSeriesWithinAtWith→continuousAtFromCoefficientBoundsCanonical
  {c = c}
  expansion
  bounds
  x
  x-domain
  x-inBall =
  hasPowerSeriesWithinAtWith→continuousAt
    expansion
    x
    x-domain
    x-inBall
    (powerSeriesSumContinuousAtFromCoefficientBoundsCanonical
      bounds
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound x-inBall))


hasPowerSeriesWithinAtWith→continuousAtFromBallTermBoundsWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
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
      χ)
hasPowerSeriesWithinAtWith→continuousAtFromBallTermBoundsWith
  {c = c}
  expansion
  index-large
  termBounds
  x
  x-domain
  x-inBall =
  hasPowerSeriesWithinAtWith→continuousAtWith
    expansion
    x
    x-domain
    x-inBall
    (powerSeriesSumContinuousAtFromBallTermBoundsWith
      index-large
      termBounds
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound x-inBall))


hasPowerSeriesWithinAtWith→continuousAtFromBallTermBounds :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ χ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  ((ε : ℚ⁺) →
    (NatOrder._≤_) (powerSeriesLimitApproximationIndex μ ε) (χ ε)) →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  (x : ℝᶜ) →
  (x-domain : D x) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesWithinAtContinuousAt {D = D} f c ρ x x-domain x-inBall
hasPowerSeriesWithinAtWith→continuousAtFromBallTermBounds
  {c = c}
  expansion
  index-large
  bounds
  x
  x-domain
  x-inBall =
  hasPowerSeriesWithinAtWith→continuousAt
    expansion
    x
    x-domain
    x-inBall
    (powerSeriesSumContinuousAtFromBallTermBounds
      index-large
      bounds
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound x-inBall))


hasPowerSeriesWithinAtWith→continuousAtFromBallTermBoundsCanonicalWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  {κ : ℕ → ℚ⁺} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
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
hasPowerSeriesWithinAtWith→continuousAtFromBallTermBoundsCanonicalWith
  {c = c}
  expansion
  termBounds
  x
  x-domain
  x-inBall =
  hasPowerSeriesWithinAtWith→continuousAtWith
    expansion
    x
    x-domain
    x-inBall
    (powerSeriesSumContinuousAtFromBallTermBoundsCanonicalWith
      termBounds
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound x-inBall))


hasPowerSeriesWithinAtWith→continuousAtFromBallTermBoundsCanonical :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  Σ[ κ ∈ (ℕ → ℚ⁺) ]
    ((h : ℝᶜ) →
      BoundedByᶜ ρ h →
      (n : ℕ) →
      BoundedByᶜ (κ n) (powerSeriesTerm a h n)) →
  (x : ℝᶜ) →
  (x-domain : D x) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  HasPowerSeriesWithinAtContinuousAt {D = D} f c ρ x x-domain x-inBall
hasPowerSeriesWithinAtWith→continuousAtFromBallTermBoundsCanonical
  {c = c}
  expansion
  bounds
  x
  x-domain
  x-inBall =
  hasPowerSeriesWithinAtWith→continuousAt
    expansion
    x
    x-domain
    x-inBall
    (powerSeriesSumContinuousAtFromBallTermBoundsCanonical
      bounds
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound x-inBall))
