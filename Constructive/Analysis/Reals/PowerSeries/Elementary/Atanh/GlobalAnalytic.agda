{-

Analyticity of atanh throughout its strict subunit domain.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.GlobalAnalytic where

open import Cubical.Foundations.Prelude

import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
  using (_+ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
  using (0ᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Base
  using (AnalyticWithinAt ; HasPowerSeriesWithinAtWith)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Coefficients
  using (atanhPowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Majorants
  using (atanhPowerSeriesMajorizedOnBall)
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Atanh.Global
  using
    ( StrictSubunitDataᶜ
    ; atanhᶜ
    ; atanhᶜFromSubunitBound
    ; atanhᶜFromSubunitBound-data-independent
    ; subunitBound
    ; subunitRadius
    ; subunitRadius<1
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using (majorizedOnBall→hasPowerSeriesOnBallWith)
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Recenter
open import Constructive.Analysis.GeometricDecay
  using (positiveGeometricPowerModulus)
open import Constructive.Data.PositiveRationals
  using
    ( ℚ⁺
    ; 1⁺
    ; radius
    ; _⊖_[_]
    ; _+⁺_
    ; half⁺
    ; half<
    ; quarter⁺
    ; sum<from-difference
    )
import Constructive.Data.Rationals as Rational


atanhᶜAnalyticWithinAt :
  (x : ℝᶜ) →
  (domain : StrictSubunitDataᶜ x) →
  AnalyticWithinAt
    {D = StrictSubunitDataᶜ}
    atanhᶜ
    x
atanhᶜAnalyticWithinAt x domain =
  recenterSeries ,
  τ ,
  positiveGeometricPowerModulus σ σ<1 ,
  expansion
  where
  ρ : ℚ⁺
  ρ =
    subunitRadius domain

  ρ<1 : radius ρ ℚOrder.< Rational.1ℚ
  ρ<1 =
    subunitRadius<1 domain

  gap : ℚ⁺
  gap =
    1⁺ ⊖ ρ [ ρ<1 ]

  σ : ℚ⁺
  σ =
    ρ +⁺ half⁺ gap

  τ : ℚ⁺
  τ =
    quarter⁺ gap

  σ<1 : radius σ ℚOrder.< Rational.1ℚ
  σ<1 =
    sum<from-difference
      1⁺
      ρ
      (half⁺ gap)
      ρ<1
      (half< gap)

  margin : radius (ρ +⁺ τ) ℚOrder.< radius σ
  margin =
    ℚOrder.<-o+
      (radius τ)
      (radius (half⁺ gap))
      (radius ρ)
      (half< (half⁺ gap))

  majorized =
    atanhPowerSeriesMajorizedOnBall σ σ<1

  oldConvergence =
    majorizedOnBall→hasPowerSeriesOnBallWith majorized

  x-displacement-bound :
    BoundedByᶜ ρ (centeredDisplacement 0ᶜ x)
  x-displacement-bound =
    subst
      (BoundedByᶜ ρ)
      (sym (centeredDisplacement-zero x))
      (subunitBound domain)

  recenterData :
    RecenterPowerSeriesData
      atanhPowerSeries
      (centeredDisplacement 0ᶜ x)
  recenterData =
    recenterPowerSeriesDataFromMajorizedOnStrictSubball
      x-displacement-bound
      margin
      majorized

  recenterSeries : PowerSeries
  recenterSeries =
    recenterPowerSeriesWith
      atanhPowerSeries
      (centeredDisplacement 0ᶜ x)
      recenterData

  fixedExpansion =
    centeredPowerSeriesWithinBallHasPowerSeriesWithinAtWithFromMajorized
      x-displacement-bound
      margin
      majorized

  newConvergence =
    fst fixedExpansion

  expansion :
    HasPowerSeriesWithinAtWith
      {D = StrictSubunitDataᶜ}
      atanhᶜ
      x
      recenterSeries
      τ
      (positiveGeometricPowerModulus σ σ<1)
  expansion =
    newConvergence , expansionPath
    where
    expansionPath :
      (y : ℝᶜ) →
      (y-domain : StrictSubunitDataᶜ y) →
      (y-inBall : InPowerSeriesBall x τ y) →
      atanhᶜ y y-domain ≡
      centeredPowerSeriesSumOnBall
        recenterSeries
        x
        τ
        (positiveGeometricPowerModulus σ σ<1)
        newConvergence
        y
        y-inBall
    expansionPath y y-domain y-inBall =
      atanhᶜFromSubunitBound-data-independent
        (subunitRadius y-domain)
        σ
        (subunitRadius<1 y-domain)
        σ<1
        y
        (subunitBound y-domain)
        y-bound
      ∙ sym
          (centeredPowerSeriesSumOnBallAtZero-path
          oldConvergence
          y
          y-bound
          )
      ∙ snd fixedExpansion y y-inOldBall y-inBall
      where
      h : ℝᶜ
      h =
        centeredDisplacement x y

      h-bound : BoundedByᶜ τ h
      h-bound =
        InPowerSeriesBall.displacementBound y-inBall

      shifted-path : centeredDisplacement 0ᶜ x +ᶜ h ≡ y
      shifted-path =
        cong (_+ᶜ h) (centeredDisplacement-zero x) ∙
        add-center-centeredDisplacement x y

      y-bound : BoundedByᶜ σ y
      y-bound =
        subst
          (BoundedByᶜ σ)
          shifted-path
          (recenterShiftedDisplacementBound
            x-displacement-bound
            h-bound
            margin)

      y-inOldBall : InPowerSeriesBall 0ᶜ σ y
      y-inOldBall =
        inPowerSeriesBallAtZeroFromBound y-bound
