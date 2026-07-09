{-

Analyticity of a majorized power-series sum at strict interior points.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Recenter.Analytic where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
  using (_+ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
  using (add-cancel-left)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Core
  using
    ( AnalyticWithinAt
    ; HasPowerSeriesWithinAtWith
    ; centeredPowerSeriesWithinBallFunction
    )
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using
    ( PowerSeriesMajorizedOnBall
    ; majorizedOnBall→hasPowerSeriesOnBallWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Base
open import Constructive.Analysis.Reals.PowerSeries.Recenter.StrictSubball
  using (recenterStrictSubballModulus ; recenterShiftedDisplacementBound)
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Theorem
  using
    ( centeredPowerSeriesSumRecenteredOnStrictSubball
    ; recenterPowerSeriesDataFromMajorizedOnStrictSubball
    ; recenterPowerSeriesOnStrictSubballFromMajorizedOnBall
    )
open import Constructive.Data.PositiveRationals
  using (ℚ⁺ ; radius ; _+⁺_)


private
  centeredDisplacement-split :
    (c x y : ℝᶜ) →
    centeredDisplacement c x +ᶜ centeredDisplacement x y ≡
    centeredDisplacement c y
  centeredDisplacement-split c x y =
    add-cancel-left
      (centeredDisplacement c x +ᶜ centeredDisplacement x y)
      (centeredDisplacement c y)
      c
      ( add-center-centeredDisplacement-forward
          c
          x
          (centeredDisplacement x y)
      ∙ add-center-centeredDisplacement x y
      ∙ sym (add-center-centeredDisplacement c y)
      )


centeredPowerSeriesWithinBallHasPowerSeriesWithinAtWithFromMajorized :
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {δ τ σ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {ν : ℚ⁺ → ℕ} →
  (d-bound : BoundedByᶜ δ (centeredDisplacement c x)) →
  (margin : radius (δ +⁺ τ) ℚOrder.< radius σ) →
  (majorized : PowerSeriesMajorizedOnBall a σ v ν) →
  HasPowerSeriesWithinAtWith
    {D = InPowerSeriesBall c σ}
    (centeredPowerSeriesWithinBallFunction
      a
      c
      σ
      ν
      (majorizedOnBall→hasPowerSeriesOnBallWith majorized))
    x
    (recenterPowerSeriesWith
      a
      (centeredDisplacement c x)
      (recenterPowerSeriesDataFromMajorizedOnStrictSubball
        d-bound
        margin
        majorized))
    τ
    (recenterStrictSubballModulus δ τ σ ν)
centeredPowerSeriesWithinBallHasPowerSeriesWithinAtWithFromMajorized
    {a = a}
    {c = c}
    {x = x}
    {δ = δ}
    {τ = τ}
    {σ = σ}
    {ν = ν}
    d-bound
    margin
    majorized =
  newConvergence , expansion
  where
  oldConvergence : HasPowerSeriesOnBallWith a σ ν
  oldConvergence =
    majorizedOnBall→hasPowerSeriesOnBallWith majorized

  recenterData : RecenterPowerSeriesData a (centeredDisplacement c x)
  recenterData =
    recenterPowerSeriesDataFromMajorizedOnStrictSubball
      d-bound
      margin
      majorized

  newConvergence :
    HasPowerSeriesOnBallWith
      (recenterPowerSeriesWith a (centeredDisplacement c x) recenterData)
      τ
      (recenterStrictSubballModulus δ τ σ ν)
  newConvergence =
    recenterPowerSeriesOnStrictSubballFromMajorizedOnBall
      d-bound
      margin
      majorized

  expansion :
    (y : ℝᶜ) →
    (y-inOldBall : InPowerSeriesBall c σ y) →
    (y-inBall : InPowerSeriesBall x τ y) →
    centeredPowerSeriesWithinBallFunction
      a
      c
      σ
      ν
      oldConvergence
      y
      y-inOldBall
    ≡
    centeredPowerSeriesSumOnBall
      (recenterPowerSeriesWith a (centeredDisplacement c x) recenterData)
      x
      τ
      (recenterStrictSubballModulus δ τ σ ν)
      newConvergence
      y
      y-inBall
  expansion y y-inOldBall y-inBall =
    powerSeriesSumOnBall-center-path
      oldConvergence
      (sym displacement-path)
      old-bound
      shifted-bound
    ∙ centeredPowerSeriesSumRecenteredOnStrictSubball
        d-bound
        h-bound
        margin
        majorized
    where
    h : ℝᶜ
    h =
      centeredDisplacement x y

    h-bound : BoundedByᶜ τ h
    h-bound =
      InPowerSeriesBall.displacementBound y-inBall

    displacement-path :
      centeredDisplacement c x +ᶜ h ≡ centeredDisplacement c y
    displacement-path =
      centeredDisplacement-split c x y

    shifted-bound :
      BoundedByᶜ σ (centeredDisplacement c x +ᶜ h)
    shifted-bound =
      recenterShiftedDisplacementBound d-bound h-bound margin

    old-bound : BoundedByᶜ σ (centeredDisplacement c y)
    old-bound =
      InPowerSeriesBall.displacementBound y-inOldBall


centeredPowerSeriesWithinBallAnalyticWithinAtFromMajorized :
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {δ τ σ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {ν : ℚ⁺ → ℕ} →
  (d-bound : BoundedByᶜ δ (centeredDisplacement c x)) →
  (margin : radius (δ +⁺ τ) ℚOrder.< radius σ) →
  (majorized : PowerSeriesMajorizedOnBall a σ v ν) →
  AnalyticWithinAt
    {D = InPowerSeriesBall c σ}
    (centeredPowerSeriesWithinBallFunction
      a
      c
      σ
      ν
      (majorizedOnBall→hasPowerSeriesOnBallWith majorized))
    x
centeredPowerSeriesWithinBallAnalyticWithinAtFromMajorized
    {a = a}
    {c = c}
    {x = x}
    {δ = δ}
    {τ = τ}
    {σ = σ}
    {ν = ν}
    d-bound
    margin
    majorized =
  recenterPowerSeriesWith
    a
    (centeredDisplacement c x)
    (recenterPowerSeriesDataFromMajorizedOnStrictSubball
      d-bound
      margin
      majorized) ,
  τ ,
  recenterStrictSubballModulus δ τ σ ν ,
  centeredPowerSeriesWithinBallHasPowerSeriesWithinAtWithFromMajorized
    d-bound
    margin
    majorized
