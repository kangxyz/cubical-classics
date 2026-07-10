{-

Analyticity of the derivative model by re-centering.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.DerivativeAnalytic where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (_,_ ; fst ; snd)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
  using (_+ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
  using (add-cancel-left)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Core
  using
    ( AnalyticAt
    ; HasPowerSeriesAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using (derivativePowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using
    ( PowerSeriesMajorizedOnBall
    ; majorizedOnBall→hasPowerSeriesOnBallWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Recenter
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


private
  derivativePowerSeriesModelHasPowerSeriesAtWithFromMajorized :
    {a : PowerSeries} →
    {c x : ℝᶜ} →
    {δ τ σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    (derivativeRadius : HasInfinitePowerSeriesRadius (derivativePowerSeries a)) →
    (d-bound : BoundedByᶜ δ (centeredDisplacement c x)) →
    (margin : radius (δ +⁺ τ) ℚOrder.< radius σ) →
    (majorized : PowerSeriesMajorizedOnBall (derivativePowerSeries a) σ v ν) →
    HasPowerSeriesAtWith
      (centeredPowerSeriesSumEverywhere
        (derivativePowerSeries a)
        c
        derivativeRadius)
      x
      (recenterPowerSeriesWith
        (derivativePowerSeries a)
        (centeredDisplacement c x)
        (recenterPowerSeriesDataFromMajorizedOnStrictSubball
          d-bound
          margin
          majorized))
      τ
      (ν)
  derivativePowerSeriesModelHasPowerSeriesAtWithFromMajorized
      {a = a}
      {c = c}
      {x = x}
      {δ = δ}
      {τ = τ}
      {σ = σ}
      {v = v}
      {ν = ν}
      derivativeRadius
      d-bound
      margin
      majorized =
    newConvergence , expansionAt
    where
    da : PowerSeries
    da =
      derivativePowerSeries a

    oldConvergence : HasPowerSeriesOnBallWith da σ ν
    oldConvergence =
      majorizedOnBall→hasPowerSeriesOnBallWith majorized

    newConvergence :
      HasPowerSeriesOnBallWith
        (recenterPowerSeriesWith da
          (centeredDisplacement c x)
          (recenterPowerSeriesDataFromMajorizedOnStrictSubball
            d-bound
            margin
            majorized))
        τ
        (ν)
    newConvergence =
      recenterPowerSeriesOnStrictSubballFromMajorizedOnBall
        d-bound
        margin
        majorized

    expansionAt :
      (y : ℝᶜ) →
      (y-inBall : InPowerSeriesBall x τ y) →
      centeredPowerSeriesSumEverywhere da c derivativeRadius y ≡
      centeredPowerSeriesSumOnBall
        (recenterPowerSeriesWith da
          (centeredDisplacement c x)
          (recenterPowerSeriesDataFromMajorizedOnStrictSubball
            d-bound
            margin
            majorized))
        x
        τ
        (ν)
        newConvergence
        y
        y-inBall
    expansionAt y y-inBall =
      centeredPowerSeriesSumEverywhere-bound-path
        da
        c
        derivativeRadius
        σ
        y
        y-inOldBall
      ∙ centeredPowerSeriesSumOnBall-data-independent
          (snd (derivativeRadius σ))
          oldConvergence
          y
          y-inOldBall
          y-inOldBall
      ∙ powerSeriesSumOnBall-center-path
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
        subst
          (BoundedByᶜ σ)
          displacement-path
          shifted-bound

      y-inOldBall : InPowerSeriesBall c σ y
      y-inOldBall =
        record { displacementBound = old-bound }


  derivativeFunctionHasPowerSeriesAtWithFromModelPathAndMajorized :
    {a : PowerSeries} →
    {f' : ℝᶜ → ℝᶜ} →
    {c x : ℝᶜ} →
    {δ τ σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    (derivativeRadius : HasInfinitePowerSeriesRadius (derivativePowerSeries a)) →
    ((y : ℝᶜ) →
      InPowerSeriesBall x τ y →
      f' y ≡
      centeredPowerSeriesSumEverywhere
        (derivativePowerSeries a)
        c
        derivativeRadius
        y) →
    (d-bound : BoundedByᶜ δ (centeredDisplacement c x)) →
    (margin : radius (δ +⁺ τ) ℚOrder.< radius σ) →
    (majorized : PowerSeriesMajorizedOnBall (derivativePowerSeries a) σ v ν) →
    HasPowerSeriesAtWith
      f'
      x
      (recenterPowerSeriesWith
        (derivativePowerSeries a)
        (centeredDisplacement c x)
        (recenterPowerSeriesDataFromMajorizedOnStrictSubball
          d-bound
          margin
          majorized))
      τ
      (ν)
  derivativeFunctionHasPowerSeriesAtWithFromModelPathAndMajorized
      {a = a}
      {c = c}
      {x = x}
      {δ = δ}
      {τ = τ}
      {σ = σ}
      {ν = ν}
      derivativeRadius
      modelPath
      d-bound
      margin
      majorized =
    convergence ,
    λ y y-inBall →
      modelPath y y-inBall ∙ expansionPath y y-inBall
    where
    modelExpansion :
      HasPowerSeriesAtWith
        (centeredPowerSeriesSumEverywhere
          (derivativePowerSeries a)
          c
          derivativeRadius)
        x
        (recenterPowerSeriesWith
          (derivativePowerSeries a)
          (centeredDisplacement c x)
          (recenterPowerSeriesDataFromMajorizedOnStrictSubball
            d-bound
            margin
            majorized))
        τ
        (ν)
    modelExpansion =
      derivativePowerSeriesModelHasPowerSeriesAtWithFromMajorized
        derivativeRadius
        d-bound
        margin
        majorized

    convergence =
      fst modelExpansion

    expansionPath =
      snd modelExpansion


derivativePowerSeriesModelAnalyticAtFromMajorized :
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {δ τ σ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {ν : ℚ⁺ → ℕ} →
  (derivativeRadius : HasInfinitePowerSeriesRadius (derivativePowerSeries a)) →
  (d-bound : BoundedByᶜ δ (centeredDisplacement c x)) →
  (margin : radius (δ +⁺ τ) ℚOrder.< radius σ) →
  (majorized : PowerSeriesMajorizedOnBall (derivativePowerSeries a) σ v ν) →
  AnalyticAt
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      derivativeRadius)
    x
derivativePowerSeriesModelAnalyticAtFromMajorized
    {a = a}
    {c = c}
    {x = x}
    {δ = δ}
    {τ = τ}
    {σ = σ}
    {ν = ν}
    derivativeRadius
    d-bound
    margin
    majorized =
  recenterPowerSeriesWith
    (derivativePowerSeries a)
    (centeredDisplacement c x)
    (recenterPowerSeriesDataFromMajorizedOnStrictSubball
      d-bound
      margin
      majorized) ,
  τ ,
  ν ,
  derivativePowerSeriesModelHasPowerSeriesAtWithFromMajorized
    derivativeRadius
    d-bound
    margin
    majorized


derivativeFunctionAnalyticAtFromModelPathAndMajorized :
  {a : PowerSeries} →
  {f' : ℝᶜ → ℝᶜ} →
  {c x : ℝᶜ} →
  {δ τ σ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {ν : ℚ⁺ → ℕ} →
  (derivativeRadius : HasInfinitePowerSeriesRadius (derivativePowerSeries a)) →
  ((y : ℝᶜ) →
    InPowerSeriesBall x τ y →
    f' y ≡
    centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      derivativeRadius
      y) →
  (d-bound : BoundedByᶜ δ (centeredDisplacement c x)) →
  (margin : radius (δ +⁺ τ) ℚOrder.< radius σ) →
  (majorized : PowerSeriesMajorizedOnBall (derivativePowerSeries a) σ v ν) →
  AnalyticAt f' x
derivativeFunctionAnalyticAtFromModelPathAndMajorized
    {a = a}
    {c = c}
    {x = x}
    {δ = δ}
    {τ = τ}
    {σ = σ}
    {ν = ν}
    derivativeRadius
    modelPath
    d-bound
    margin
    majorized =
  recenterPowerSeriesWith
    (derivativePowerSeries a)
    (centeredDisplacement c x)
    (recenterPowerSeriesDataFromMajorizedOnStrictSubball
      d-bound
      margin
      majorized) ,
  τ ,
  ν ,
  derivativeFunctionHasPowerSeriesAtWithFromModelPathAndMajorized
    derivativeRadius
    modelPath
    d-bound
    margin
    majorized
