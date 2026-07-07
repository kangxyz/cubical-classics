{-

Part of Constructive.Analysis.Reals.PowerSeries.Analytic

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Analytic.Core where

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
open import Constructive.Analysis.Reals.PowerSeries.Continuity.Core
  using (PowerSeriesCoefficientBounds)
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals

open import Constructive.Analysis.Reals.PowerSeries.Analytic.Internal

PowerSeriesExpansionPath :
  (ℝᶜ → ℝᶜ) →
  ℝᶜ →
  (a : PowerSeries) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  HasPowerSeriesOnBallWith a ρ μ →
  Type₀
PowerSeriesExpansionPath f c a ρ μ convergence =
  (x : ℝᶜ) →
  (inBall : InPowerSeriesBall c ρ x) →
  f x ≡ centeredPowerSeriesSumOnBall a c ρ μ convergence x inBall


HasPowerSeriesAtWith :
  (ℝᶜ → ℝᶜ) →
  ℝᶜ →
  PowerSeries →
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type₀
HasPowerSeriesAtWith f c a ρ μ =
  Σ[ convergence ∈ HasPowerSeriesOnBallWith a ρ μ ]
    PowerSeriesExpansionPath f c a ρ μ convergence


HasPowerSeriesAtWithBounds :
  (ℝᶜ → ℝᶜ) →
  ℝᶜ →
  PowerSeries →
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type₀
HasPowerSeriesAtWithBounds f c a ρ μ =
  Σ[ expansion ∈ HasPowerSeriesAtWith f c a ρ μ ]
    PowerSeriesCoefficientBounds a


HasPowerSeriesAtOnBall :
  (ℝᶜ → ℝᶜ) →
  ℝᶜ →
  PowerSeries →
  ℚ⁺ →
  Type₀
HasPowerSeriesAtOnBall f c a ρ =
  Σ[ μ ∈ (ℚ⁺ → ℕ) ] HasPowerSeriesAtWith f c a ρ μ


HasPowerSeriesAt :
  (ℝᶜ → ℝᶜ) →
  ℝᶜ →
  PowerSeries →
  Type₀
HasPowerSeriesAt f c a =
  Σ[ ρ ∈ ℚ⁺ ] HasPowerSeriesAtOnBall f c a ρ


AnalyticAt :
  (ℝᶜ → ℝᶜ) →
  ℝᶜ →
  Type₀
AnalyticAt f c =
  Σ[ a ∈ PowerSeries ] HasPowerSeriesAt f c a


centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (ρ : ℚ⁺) →
  HasPowerSeriesAtWith
    (centeredPowerSeriesSumEverywhere a c radiusData)
    c
    a
    ρ
    (fst (radiusData ρ))
centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
  {a = a}
  {c = c}
  radiusData
  ρ =
  snd (radiusData ρ) ,
  λ x inBall →
    centeredPowerSeriesSumEverywhere-bound-path
      a
      c
      radiusData
      ρ
      x
      inBall


centeredPowerSeriesSumEverywhereHasPowerSeriesAtOnBall :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (ρ : ℚ⁺) →
  HasPowerSeriesAtOnBall
    (centeredPowerSeriesSumEverywhere a c radiusData)
    c
    a
    ρ
centeredPowerSeriesSumEverywhereHasPowerSeriesAtOnBall radiusData ρ =
  fst (radiusData ρ) ,
  centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith radiusData ρ


centeredPowerSeriesSumEverywhereHasPowerSeriesAt :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  HasPowerSeriesAt
    (centeredPowerSeriesSumEverywhere a c radiusData)
    c
    a
centeredPowerSeriesSumEverywhereHasPowerSeriesAt radiusData =
  1⁺ ,
  centeredPowerSeriesSumEverywhereHasPowerSeriesAtOnBall radiusData 1⁺


centeredPowerSeriesSumEverywhereAnalyticAt :
  (a : PowerSeries) →
  (c : ℝᶜ) →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  AnalyticAt (centeredPowerSeriesSumEverywhere a c radiusData) c
centeredPowerSeriesSumEverywhereAnalyticAt a c radiusData =
  a ,
  centeredPowerSeriesSumEverywhereHasPowerSeriesAt radiusData


PowerSeriesWithinExpansionPath :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  ℝᶜ →
  (a : PowerSeries) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  HasPowerSeriesOnBallWith a ρ μ →
  Type ℓ
PowerSeriesWithinExpansionPath {D = D} f c a ρ μ convergence =
  (x : ℝᶜ) →
  (domain : D x) →
  (inBall : InPowerSeriesBall c ρ x) →
  f x domain ≡ centeredPowerSeriesSumOnBall a c ρ μ convergence x inBall


HasPowerSeriesWithinAtWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  ℝᶜ →
  PowerSeries →
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type ℓ
HasPowerSeriesWithinAtWith {D = D} f c a ρ μ =
  Σ[ convergence ∈ HasPowerSeriesOnBallWith a ρ μ ]
    PowerSeriesWithinExpansionPath {D = D} f c a ρ μ convergence


HasPowerSeriesWithinAtWithBounds :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  ℝᶜ →
  PowerSeries →
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type ℓ
HasPowerSeriesWithinAtWithBounds {D = D} f c a ρ μ =
  Σ[ expansion ∈ HasPowerSeriesWithinAtWith {D = D} f c a ρ μ ]
    PowerSeriesCoefficientBounds a


HasPowerSeriesWithinAtOnBall :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  ℝᶜ →
  PowerSeries →
  ℚ⁺ →
  Type ℓ
HasPowerSeriesWithinAtOnBall {D = D} f c a ρ =
  Σ[ μ ∈ (ℚ⁺ → ℕ) ] HasPowerSeriesWithinAtWith {D = D} f c a ρ μ


HasPowerSeriesWithinAt :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  ℝᶜ →
  PowerSeries →
  Type ℓ
HasPowerSeriesWithinAt {D = D} f c a =
  Σ[ ρ ∈ ℚ⁺ ] HasPowerSeriesWithinAtOnBall {D = D} f c a ρ


AnalyticWithinAt :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  ℝᶜ →
  Type ℓ
AnalyticWithinAt {D = D} f c =
  Σ[ a ∈ PowerSeries ] HasPowerSeriesWithinAt {D = D} f c a


centeredPowerSeriesWithinBallFunction :
  (a : PowerSeries) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  HasPowerSeriesOnBallWith a ρ μ →
  (x : ℝᶜ) →
  InPowerSeriesBall c ρ x →
  ℝᶜ
centeredPowerSeriesWithinBallFunction a c ρ μ convergence x x-inBall =
  centeredPowerSeriesSumOnBall a c ρ μ convergence x x-inBall


centeredPowerSeriesWithinBallHasPowerSeriesWithinAtWith :
  (a : PowerSeries) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  HasPowerSeriesWithinAtWith
    {D = InPowerSeriesBall c ρ}
    (centeredPowerSeriesWithinBallFunction a c ρ μ convergence)
    c
    a
    ρ
    μ
centeredPowerSeriesWithinBallHasPowerSeriesWithinAtWith a c ρ μ convergence =
  convergence ,
  λ x domain inBall →
    centeredPowerSeriesSumOnBall-inBall-independent
      convergence
      x
      domain
      inBall


centeredPowerSeriesWithinBallHasPowerSeriesWithinAtOnBall :
  (a : PowerSeries) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  HasPowerSeriesWithinAtOnBall
    {D = InPowerSeriesBall c ρ}
    (centeredPowerSeriesWithinBallFunction a c ρ μ convergence)
    c
    a
    ρ
centeredPowerSeriesWithinBallHasPowerSeriesWithinAtOnBall a c ρ μ convergence =
  μ ,
  centeredPowerSeriesWithinBallHasPowerSeriesWithinAtWith
    a
    c
    ρ
    μ
    convergence


centeredPowerSeriesWithinBallHasPowerSeriesWithinAt :
  (a : PowerSeries) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  HasPowerSeriesWithinAt
    {D = InPowerSeriesBall c ρ}
    (centeredPowerSeriesWithinBallFunction a c ρ μ convergence)
    c
    a
centeredPowerSeriesWithinBallHasPowerSeriesWithinAt a c ρ μ convergence =
  ρ ,
  centeredPowerSeriesWithinBallHasPowerSeriesWithinAtOnBall
    a
    c
    ρ
    μ
    convergence


centeredPowerSeriesWithinBallAnalyticWithinAt :
  (a : PowerSeries) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  AnalyticWithinAt
    {D = InPowerSeriesBall c ρ}
    (centeredPowerSeriesWithinBallFunction a c ρ μ convergence)
    c
centeredPowerSeriesWithinBallAnalyticWithinAt a c ρ μ convergence =
  a ,
  centeredPowerSeriesWithinBallHasPowerSeriesWithinAt
    a
    c
    ρ
    μ
    convergence
