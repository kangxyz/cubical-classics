{-

Part of Constructive.Analysis.Reals.PowerSeries.Analytic

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Analytic.Continuity where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Rationals using (ℚ)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁ ; ∣_∣₁)

open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Metric
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
  using (TailBound)
open import Constructive.Analysis.Modulus
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


HasPowerSeriesAtUniformlyContinuousOnBallAtPrecision :
  (ℝᶜ → ℝᶜ) →
  ℝᶜ →
  ℚ⁺ →
  ℚ⁺ →
  ℚ⁺ →
  Type₀
HasPowerSeriesAtUniformlyContinuousOnBallAtPrecision f c ρ ε δ =
  {x y : ℝᶜ} →
  (x-inBall : InPowerSeriesBall c ρ x) →
  (y-inBall : InPowerSeriesBall c ρ y) →
  MetricSpace.Close CauchyRealsMetricSpace x δ y →
  MetricSpace.Close CauchyRealsMetricSpace (f x) ε (f y)


HasPowerSeriesAtMerelyUniformlyContinuousOnBall :
  (ℝᶜ → ℝᶜ) →
  ℝᶜ →
  ℚ⁺ →
  Type₀
HasPowerSeriesAtMerelyUniformlyContinuousOnBall f c ρ =
  (ε : ℚ⁺) →
  ∥ Σ[ δ ∈ ℚ⁺ ]
      HasPowerSeriesAtUniformlyContinuousOnBallAtPrecision f c ρ ε δ
  ∥₁


hasPowerSeriesAtUniformlyContinuousOnBall→merelyUniformlyContinuousOnBall :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  HasPowerSeriesAtUniformlyContinuousOnBall f c ρ →
  HasPowerSeriesAtMerelyUniformlyContinuousOnBall f c ρ
hasPowerSeriesAtUniformlyContinuousOnBall→merelyUniformlyContinuousOnBall
  (ν , uniform)
  ε =
  ∣ ν ε , uniform ε ∣₁


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


HasPowerSeriesAtContinuousAtPrecision :
  (f : ℝᶜ → ℝᶜ) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (x : ℝᶜ) →
  InPowerSeriesBall c ρ x →
  ℚ⁺ →
  ℚ⁺ →
  Type₀
HasPowerSeriesAtContinuousAtPrecision f c ρ x x-inBall ε δ =
  {y : ℝᶜ} →
  (y-inBall : InPowerSeriesBall c ρ y) →
  MetricSpace.Close CauchyRealsMetricSpace x δ y →
  MetricSpace.Close CauchyRealsMetricSpace (f x) ε (f y)


HasPowerSeriesAtMerelyContinuousAt :
  (f : ℝᶜ → ℝᶜ) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (x : ℝᶜ) →
  InPowerSeriesBall c ρ x →
  Type₀
HasPowerSeriesAtMerelyContinuousAt f c ρ x x-inBall =
  (ε : ℚ⁺) →
  ∥ Σ[ δ ∈ ℚ⁺ ]
      HasPowerSeriesAtContinuousAtPrecision f c ρ x x-inBall ε δ
  ∥₁


hasPowerSeriesAtContinuousAt→merelyContinuousAt :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  {x : ℝᶜ} →
  {x-inBall : InPowerSeriesBall c ρ x} →
  HasPowerSeriesAtContinuousAt f c ρ x x-inBall →
  HasPowerSeriesAtMerelyContinuousAt f c ρ x x-inBall
hasPowerSeriesAtContinuousAt→merelyContinuousAt (ν , continuous) ε =
  ∣ ν ε , continuous ε ∣₁


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


HasPowerSeriesWithinAtUniformlyContinuousOnBallAtPrecision :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  ℝᶜ →
  ℚ⁺ →
  ℚ⁺ →
  ℚ⁺ →
  Type ℓ
HasPowerSeriesWithinAtUniformlyContinuousOnBallAtPrecision
  {D = D}
  f
  c
  ρ
  ε
  δ =
  {x y : ℝᶜ} →
  (x-domain : D x) →
  (y-domain : D y) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  (y-inBall : InPowerSeriesBall c ρ y) →
  MetricSpace.Close CauchyRealsMetricSpace x δ y →
  MetricSpace.Close CauchyRealsMetricSpace
    (f x x-domain)
    ε
    (f y y-domain)


HasPowerSeriesWithinAtMerelyUniformlyContinuousOnBall :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  ℝᶜ →
  ℚ⁺ →
  Type ℓ
HasPowerSeriesWithinAtMerelyUniformlyContinuousOnBall {D = D} f c ρ =
  (ε : ℚ⁺) →
  ∥ Σ[ δ ∈ ℚ⁺ ]
      HasPowerSeriesWithinAtUniformlyContinuousOnBallAtPrecision
        {D = D}
        f
        c
        ρ
        ε
        δ
  ∥₁


hasPowerSeriesWithinAtUniformlyContinuousOnBall→merelyUniformlyContinuousOnBall :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  HasPowerSeriesWithinAtUniformlyContinuousOnBall {D = D} f c ρ →
  HasPowerSeriesWithinAtMerelyUniformlyContinuousOnBall {D = D} f c ρ
hasPowerSeriesWithinAtUniformlyContinuousOnBall→merelyUniformlyContinuousOnBall
  (ν , uniform)
  ε =
  ∣ ν ε , uniform ε ∣₁


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


HasPowerSeriesWithinAtContinuousAtPrecision :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  (f : (x : ℝᶜ) → D x → ℝᶜ) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (x : ℝᶜ) →
  D x →
  InPowerSeriesBall c ρ x →
  ℚ⁺ →
  ℚ⁺ →
  Type ℓ
HasPowerSeriesWithinAtContinuousAtPrecision
  {D = D}
  f
  c
  ρ
  x
  x-domain
  x-inBall
  ε
  δ =
  {y : ℝᶜ} →
  (y-domain : D y) →
  (y-inBall : InPowerSeriesBall c ρ y) →
  MetricSpace.Close CauchyRealsMetricSpace x δ y →
  MetricSpace.Close CauchyRealsMetricSpace
    (f x x-domain)
    ε
    (f y y-domain)


HasPowerSeriesWithinAtMerelyContinuousAt :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  (f : (x : ℝᶜ) → D x → ℝᶜ) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (x : ℝᶜ) →
  D x →
  InPowerSeriesBall c ρ x →
  Type ℓ
HasPowerSeriesWithinAtMerelyContinuousAt
  {D = D}
  f
  c
  ρ
  x
  x-domain
  x-inBall =
  (ε : ℚ⁺) →
  ∥ Σ[ δ ∈ ℚ⁺ ]
      HasPowerSeriesWithinAtContinuousAtPrecision
        {D = D}
        f
        c
        ρ
        x
        x-domain
        x-inBall
        ε
        δ
  ∥₁


hasPowerSeriesWithinAtContinuousAt→merelyContinuousAt :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {ρ : ℚ⁺} →
  {x : ℝᶜ} →
  {x-domain : D x} →
  {x-inBall : InPowerSeriesBall c ρ x} →
  HasPowerSeriesWithinAtContinuousAt {D = D} f c ρ x x-domain x-inBall →
  HasPowerSeriesWithinAtMerelyContinuousAt {D = D} f c ρ x x-domain x-inBall
hasPowerSeriesWithinAtContinuousAt→merelyContinuousAt (ν , continuous) ε =
  ∣ ν ε , continuous ε ∣₁
