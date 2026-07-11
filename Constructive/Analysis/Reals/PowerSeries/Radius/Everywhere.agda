{-

Part of Constructive.Analysis.Reals.PowerSeries.Radius

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Radius.Everywhere where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; max)
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁)

import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Metric
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using (neg-zeroᶜ)
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Data.PositiveRationals

open import Constructive.Analysis.Reals.PowerSeries.Convergence

HasInfinitePowerSeriesRadius :
  PowerSeries →
  Type₀
HasInfinitePowerSeriesRadius a =
  (ρ : ℚ⁺) → HasPowerSeriesOnBall a ρ


hasInfinitePowerSeriesRadius→radius :
  {a : PowerSeries} →
  (R : ℚ⁺) →
  HasInfinitePowerSeriesRadius a →
  HasPowerSeriesRadius a R
hasInfinitePowerSeriesRadius→radius R radiusData ρ _ =
  radiusData ρ


hasPowerSeriesRadius-cong :
  {a b : PowerSeries} →
  {R : ℚ⁺} →
  ((n : ℕ) → a n ≡ b n) →
  HasPowerSeriesRadius a R →
  HasPowerSeriesRadius b R
hasPowerSeriesRadius-cong coeff≡ radiusData ρ ρ<R =
  hasPowerSeriesOnBall-cong coeff≡ (radiusData ρ ρ<R)


hasInfinitePowerSeriesRadius-cong :
  {a b : PowerSeries} →
  ((n : ℕ) → a n ≡ b n) →
  HasInfinitePowerSeriesRadius a →
  HasInfinitePowerSeriesRadius b
hasInfinitePowerSeriesRadius-cong coeff≡ radiusData ρ =
  hasPowerSeriesOnBall-cong coeff≡ (radiusData ρ)


private
  PowerSeriesPointBoundData :
    ℝᶜ →
    Type₀
  PowerSeriesPointBoundData x =
    Σ[ ρ ∈ ℚ⁺ ] BoundedByᶜ ρ x


  powerSeriesSumEverywhereFromBounds :
    (a : PowerSeries) →
    HasInfinitePowerSeriesRadius a →
    (x : ℝᶜ) →
    ∥ PowerSeriesPointBoundData x ∥₁ →
    ℝᶜ
  powerSeriesSumEverywhereFromBounds a radiusData x =
    Prop.rec→Set
      (MetricSpace.isSetCarrier CauchyRealsMetricSpace)
      sumWithBound
      sumWithBound-constant
    where
    sumWithBound :
      PowerSeriesPointBoundData x →
      ℝᶜ
    sumWithBound (ρ , x-bound) =
      powerSeriesSumOnBallFrom a ρ (radiusData ρ) x x-bound

    sumWithBound-constant :
      (left right : PowerSeriesPointBoundData x) →
      sumWithBound left ≡ sumWithBound right
    sumWithBound-constant (ρ , ρ-bound) (σ , σ-bound) =
      powerSeriesSumOnBallFrom-data-independent
        (radiusData ρ)
        (radiusData σ)
        x
        ρ-bound
        σ-bound


powerSeriesSumEverywhere :
  (a : PowerSeries) →
  HasInfinitePowerSeriesRadius a →
  ℝᶜ →
  ℝᶜ
powerSeriesSumEverywhere a radiusData x =
  powerSeriesSumEverywhereFromBounds
    a
    radiusData
    x
    (merely-boundedᶜ x)


powerSeriesSumEverywhere-bound-path :
  (a : PowerSeries) →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (ρ : ℚ⁺) →
  (x : ℝᶜ) →
  (x-bound : BoundedByᶜ ρ x) →
  powerSeriesSumEverywhere a radiusData x ≡
  powerSeriesSumOnBallFrom a ρ (radiusData ρ) x x-bound
powerSeriesSumEverywhere-bound-path a radiusData ρ x x-bound =
  Prop.elim
    {P = λ bounds →
      powerSeriesSumEverywhereFromBounds a radiusData x bounds ≡
      powerSeriesSumOnBallFrom a ρ (radiusData ρ) x x-bound}
    (λ _ → MetricSpace.isSetCarrier CauchyRealsMetricSpace _ _)
    step
    (merely-boundedᶜ x)
  where
  step :
    (bounds : PowerSeriesPointBoundData x) →
    powerSeriesSumEverywhereFromBounds a radiusData x ∣ bounds ∣₁ ≡
    powerSeriesSumOnBallFrom a ρ (radiusData ρ) x x-bound
  step (σ , σ-bound) =
    powerSeriesSumOnBallFrom-data-independent
      (radiusData σ)
      (radiusData ρ)
      x
      σ-bound
      x-bound


powerSeriesSumEverywhere-coefficients-path :
  {a b : PowerSeries} →
  ((n : ℕ) → a n ≡ b n) →
  (leftRadius : HasInfinitePowerSeriesRadius a) →
  (rightRadius : HasInfinitePowerSeriesRadius b) →
  (x : ℝᶜ) →
  powerSeriesSumEverywhere a leftRadius x ≡
  powerSeriesSumEverywhere b rightRadius x
powerSeriesSumEverywhere-coefficients-path
  {a = a}
  {b = b}
  coeff≡
  leftRadius
  rightRadius
  x =
  Prop.elim
    {P = λ bounds →
      powerSeriesSumEverywhereFromBounds a leftRadius x bounds ≡
      powerSeriesSumEverywhere b rightRadius x}
    (λ _ → MetricSpace.isSetCarrier CauchyRealsMetricSpace _ _)
    step
    (merely-boundedᶜ x)
  where
  step :
    (bounds : PowerSeriesPointBoundData x) →
    powerSeriesSumEverywhereFromBounds a leftRadius x ∣ bounds ∣₁ ≡
    powerSeriesSumEverywhere b rightRadius x
  step (ρ , x-bound) =
    powerSeriesSumOnBallFrom-coefficients-path
      coeff≡
      (leftRadius ρ)
      (rightRadius ρ)
      x
      x-bound
      x-bound ∙
    sym
      (powerSeriesSumEverywhere-bound-path
        b
        rightRadius
        ρ
        x
        x-bound)
