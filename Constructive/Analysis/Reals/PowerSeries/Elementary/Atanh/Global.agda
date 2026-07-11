{-

Hyperbolic arctangent on the strict subunit domain

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Global where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (Σ-syntax ; fst ; snd)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Coefficients
  using (atanhPowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Convergence
  using (atanhPowerSeriesOnSubunitBallWith)
open import Constructive.Analysis.Reals.PowerSeries.Convergence
  using
    ( powerSeriesSumOnBall
    ; powerSeriesSumOnBall-data-independent
    )
open import Constructive.Analysis.GeometricDecay
  using (positiveGeometricPowerModulus)
open import Constructive.Data.PositiveRationals
  using (ℚ⁺ ; radius)
import Constructive.Data.Rationals as Rational


StrictSubunitDataᶜ :
  ℝᶜ →
  Type₀
StrictSubunitDataᶜ z =
  Σ[ ρ ∈ ℚ⁺ ]
    Σ[ ρ<1 ∈ radius ρ ℚOrder.< Rational.1ℚ ]
      BoundedByᶜ ρ z


module StrictSubunitDataᶜ where
  subunitRadius :
    {z : ℝᶜ} →
    StrictSubunitDataᶜ z →
    ℚ⁺
  subunitRadius =
    fst

  subunitRadius<1 :
    {z : ℝᶜ} →
    (domain : StrictSubunitDataᶜ z) →
    radius (subunitRadius domain) ℚOrder.< Rational.1ℚ
  subunitRadius<1 =
    λ domain → fst (snd domain)

  subunitBound :
    {z : ℝᶜ} →
    (domain : StrictSubunitDataᶜ z) →
    BoundedByᶜ (subunitRadius domain) z
  subunitBound =
    λ domain → snd (snd domain)


open StrictSubunitDataᶜ public


atanhᶜFromSubunitBound :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  (z : ℝᶜ) →
  BoundedByᶜ ρ z →
  ℝᶜ
atanhᶜFromSubunitBound ρ ρ<1 z z-bound =
  powerSeriesSumOnBall
    atanhPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (atanhPowerSeriesOnSubunitBallWith ρ ρ<1)
    z
    z-bound


atanhᶜFromSubunitBound-data-independent :
  (ρ σ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (σ<1 : radius σ ℚOrder.< Rational.1ℚ) →
  (z : ℝᶜ) →
  (zρ : BoundedByᶜ ρ z) →
  (zσ : BoundedByᶜ σ z) →
  atanhᶜFromSubunitBound ρ ρ<1 z zρ ≡
  atanhᶜFromSubunitBound σ σ<1 z zσ
atanhᶜFromSubunitBound-data-independent ρ σ ρ<1 σ<1 z zρ zσ =
  powerSeriesSumOnBall-data-independent
    (atanhPowerSeriesOnSubunitBallWith ρ ρ<1)
    (atanhPowerSeriesOnSubunitBallWith σ σ<1)
    z
    zρ
    zσ


atanhᶜ :
  (z : ℝᶜ) →
  StrictSubunitDataᶜ z →
  ℝᶜ
atanhᶜ z domain =
  atanhᶜFromSubunitBound
    (subunitRadius domain)
    (subunitRadius<1 domain)
    z
    (subunitBound domain)


atanhᶜ-data-independent :
  (z : ℝᶜ) →
  (left right : StrictSubunitDataᶜ z) →
  atanhᶜ z left ≡ atanhᶜ z right
atanhᶜ-data-independent z left right =
  atanhᶜFromSubunitBound-data-independent
    (subunitRadius left)
    (subunitRadius right)
    (subunitRadius<1 left)
    (subunitRadius<1 right)
    z
    (subunitBound left)
    (subunitBound right)
