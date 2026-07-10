{-

Convergence transport for formal derivative and primitive coefficients

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.Closure where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using (derivativePowerSeries ; primitivePowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.StrictSubball.OnBall.Tail
  using (derivativePowerSeriesOnStrictSubball)


derivativePowerSeriesRadius :
  {a : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius a R →
  HasPowerSeriesRadius (derivativePowerSeries a) R
derivativePowerSeriesRadius {a = a} {R = R} radiusData ρ ρ<R =
  derivativePowerSeriesOnStrictSubball
    {a = a}
    {ρ = ρ}
    {σ = middleRadius ρ ρ<R}
    (ρ<middle ρ ρ<R)
    (radiusData (middleRadius ρ ρ<R) (middle<R ρ ρ<R))
  where
  middle-positive :
    (ρ : ℚ⁺) →
    (ρ<R : radius ρ ℚOrder.< radius R) →
    Rational.0ℚ ℚOrder.< Rational.middle (radius ρ) (radius R)
  middle-positive ρ ρ<R =
    Rational.≤<-trans
      {p = Rational.0ℚ}
      {q = radius ρ}
      {r = Rational.middle (radius ρ) (radius R)}
      (Rational.<→≤ {p = Rational.0ℚ} {q = radius ρ} (ρ .snd))
      (Rational.middle>l {p = radius ρ} {q = radius R} ρ<R)

  middleRadius :
    (ρ : ℚ⁺) →
    radius ρ ℚOrder.< radius R →
    ℚ⁺
  middleRadius ρ ρ<R =
    Rational.middle (radius ρ) (radius R) ,
    middle-positive ρ ρ<R

  ρ<middle :
    (ρ : ℚ⁺) →
    (ρ<R : radius ρ ℚOrder.< radius R) →
    radius ρ ℚOrder.< radius (middleRadius ρ ρ<R)
  ρ<middle ρ ρ<R =
    Rational.middle>l {p = radius ρ} {q = radius R} ρ<R

  middle<R :
    (ρ : ℚ⁺) →
    (ρ<R : radius ρ ℚOrder.< radius R) →
    radius (middleRadius ρ ρ<R) ℚOrder.< radius R
  middle<R ρ ρ<R =
    Rational.middle<r {p = radius ρ} {q = radius R} ρ<R


derivativePowerSeriesInfiniteRadius :
  {a : PowerSeries} →
  HasInfinitePowerSeriesRadius a →
  HasInfinitePowerSeriesRadius (derivativePowerSeries a)
derivativePowerSeriesInfiniteRadius {a = a} radiusData ρ =
  derivativePowerSeriesOnStrictSubball
    {a = a}
    {ρ = ρ}
    {σ = ρ +⁺ 1⁺}
    (summand-left<sum ρ 1⁺)
    (radiusData (ρ +⁺ 1⁺))




derivativePowerSeriesInfiniteRadiusFromCoefficientPath :
  {a b : PowerSeries} →
  ((n : ℕ) → derivativePowerSeries a n ≡ b n) →
  HasInfinitePowerSeriesRadius b →
  HasInfinitePowerSeriesRadius (derivativePowerSeries a)
derivativePowerSeriesInfiniteRadiusFromCoefficientPath {a = a} {b = b} coeff≡ =
  hasInfinitePowerSeriesRadius-cong
    {a = b}
    {b = derivativePowerSeries a}
    (λ n → sym (coeff≡ n))




primitivePowerSeriesInfiniteRadiusFromCoefficientPath :
  {a b : PowerSeries} →
  ((n : ℕ) → primitivePowerSeries a n ≡ b n) →
  HasInfinitePowerSeriesRadius b →
  HasInfinitePowerSeriesRadius (primitivePowerSeries a)
primitivePowerSeriesInfiniteRadiusFromCoefficientPath {a = a} {b = b} coeff≡ =
  hasInfinitePowerSeriesRadius-cong
    {a = b}
    {b = primitivePowerSeries a}
    (λ n → sym (coeff≡ n))
