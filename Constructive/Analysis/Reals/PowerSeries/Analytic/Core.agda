{-

Part of Constructive.Analysis.Reals.PowerSeries.Analytic

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Analytic.Core where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)

open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Bounds
  using (PowerSeriesCoefficientBounds)
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals


HasPowerSeriesAtWith :
  (ℝᶜ → ℝᶜ) →
  ℝᶜ →
  PowerSeries →
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type₀
HasPowerSeriesAtWith f c a ρ μ =
  Σ[ convergence ∈ HasPowerSeriesOnBallWith a ρ μ ]
    ((x : ℝᶜ) →
     (inBall : InPowerSeriesBall c ρ x) →
     f x ≡ centeredPowerSeriesSumOnBall a c ρ μ convergence x inBall)


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


centeredPowerSeriesSumEverywhereAnalyticAt :
  (a : PowerSeries) →
  (c : ℝᶜ) →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  AnalyticAt (centeredPowerSeriesSumEverywhere a c radiusData) c
centeredPowerSeriesSumEverywhereAnalyticAt a c radiusData =
  a ,
  1⁺ ,
  fst (radiusData 1⁺) ,
  centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith radiusData 1⁺


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
    ((x : ℝᶜ) →
     (domain : D x) →
     (inBall : InPowerSeriesBall c ρ x) →
     f x domain ≡
       centeredPowerSeriesSumOnBall a c ρ μ convergence x inBall)


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
  ρ ,
  μ ,
  centeredPowerSeriesWithinBallHasPowerSeriesWithinAtWith
    a
    c
    ρ
    μ
    convergence
