{-

Automatic termwise derivative consequences

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Automatic where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁)

open import Constructive.Analysis.Reals.Calculus.Derivative.Base
  using (HasDerivativeAt)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Core
  using (HasPowerSeriesAtWith)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using (derivativePowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence
  using (derivativePowerSeriesInfiniteRadius)
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.SecondDerivativePartialSumBounds.Finite
  using
    ( PowerSeriesSecondDerivativePartialSumsBoundOnBall
    ; powerSeriesSecondDerivativePartialSumsBoundOnBallFromConvergence
    )
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Theorem
  using
    ( centeredPowerSeriesHasDerivativeFromSecondDerivativeBounds
    ; hasPowerSeriesDerivativeFromSecondDerivativeBounds
    )
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.UniformPartialSums
  using
    ( partialSumsDerivativeTargetModulus
    ; powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound
    )
open import Constructive.Data.PositiveRationals


private
  positiveAddRightMonotone :
    {α β σ : ℚ⁺} →
    radius α ℚOrder.≤ radius β →
    radius (σ +⁺ α) ℚOrder.≤ radius (σ +⁺ β)
  positiveAddRightMonotone {α = α} {β = β} {σ = σ} α≤β =
    subst2
      ℚOrder._≤_
      (ℚ.+Comm (radius α) (radius σ))
      (ℚ.+Comm (radius β) (radius σ))
      (ℚOrder.≤-+o
        (radius α)
        (radius β)
        (radius σ)
        α≤β)

  secondDerivativeTargetModulus≤1 :
    (Γ : ℚ⁺) →
    (ε : ℚ⁺) →
    radius
      (partialSumsDerivativeTargetModulus
        (powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound Γ)
        ε)
      ℚOrder.≤ radius 1⁺
  secondDerivativeTargetModulus≤1 Γ ε =
    min⁺≤left 1⁺ (posInv⁺ (Γ +⁺ 1⁺) *⁺ quarter⁺ (quarter⁺ ε))

  secondDerivativeCanonicalUnitMargin :
    (σ Γ : ℚ⁺) →
    (ε : ℚ⁺) →
    radius
      (σ +⁺
        partialSumsDerivativeTargetModulus
          (powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound Γ)
          ε)
      ℚOrder.≤ radius (σ +⁺ 1⁺)
  secondDerivativeCanonicalUnitMargin σ Γ ε =
    positiveAddRightMonotone
      {α =
        partialSumsDerivativeTargetModulus
          (powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound Γ)
          ε}
      {β = 1⁺}
      {σ = σ}
      (secondDerivativeTargetModulus≤1 Γ ε)


centeredPowerSeriesSumEverywhereFormalDerivativeAt :
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {σ : ℚ⁺} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  BoundedByᶜ σ (centeredDisplacement c x) →
  ∥ HasDerivativeAt
      (centeredPowerSeriesSumEverywhere a c radiusData)
      x
      (centeredPowerSeriesSumEverywhere
        (derivativePowerSeries a)
        c
        (derivativePowerSeriesInfiniteRadius radiusData)
        x) ∥₁
centeredPowerSeriesSumEverywhereFormalDerivativeAt
  {a = a}
  {c = c}
  {x = x}
  {σ = σ}
  radiusData
  x-displacement-bound =
  Prop.map prove secondDerivativeBound
  where
  secondDerivativeBound :
    ∥ PowerSeriesSecondDerivativePartialSumsBoundOnBall
        a
        (σ +⁺ 1⁺) ∥₁
  secondDerivativeBound =
    powerSeriesSecondDerivativePartialSumsBoundOnBallFromConvergence
      (derivativePowerSeriesInfiniteRadius
        (derivativePowerSeriesInfiniteRadius radiusData)
        (σ +⁺ 1⁺)
        .snd)

  prove :
    PowerSeriesSecondDerivativePartialSumsBoundOnBall a (σ +⁺ 1⁺) →
    HasDerivativeAt
      (centeredPowerSeriesSumEverywhere a c radiusData)
      x
      (centeredPowerSeriesSumEverywhere
        (derivativePowerSeries a)
        c
        (derivativePowerSeriesInfiniteRadius radiusData)
        x)
  prove (Γ , bound) =
    partialSumsDerivativeTargetModulus
      (powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound Γ) ,
    centeredPowerSeriesHasDerivativeFromSecondDerivativeBounds
      {a = a}
      {c = c}
      {x = x}
      {ρ = σ +⁺ 1⁺}
      {σ = σ}
      {Γ = Γ}
      radiusData
      x-displacement-bound
      (secondDerivativeCanonicalUnitMargin σ Γ)
      bound


hasPowerSeriesAtWith→formalDerivativeAt :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {σ : ℚ⁺} →
  {seriesModulus : ℚ⁺ → ℕ} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  HasPowerSeriesAtWith f c a (σ +⁺ 1⁺) seriesModulus →
  BoundedByᶜ σ (centeredDisplacement c x) →
  ∥ HasDerivativeAt
      f
      x
      (centeredPowerSeriesSumEverywhere
        (derivativePowerSeries a)
        c
        (derivativePowerSeriesInfiniteRadius radiusData)
        x) ∥₁
hasPowerSeriesAtWith→formalDerivativeAt
  {f = f}
  {a = a}
  {c = c}
  {x = x}
  {σ = σ}
  radiusData
  expansion
  x-displacement-bound =
  Prop.map prove secondDerivativeBound
  where
  secondDerivativeBound :
    ∥ PowerSeriesSecondDerivativePartialSumsBoundOnBall
        a
        (σ +⁺ 1⁺) ∥₁
  secondDerivativeBound =
    powerSeriesSecondDerivativePartialSumsBoundOnBallFromConvergence
      (derivativePowerSeriesInfiniteRadius
        (derivativePowerSeriesInfiniteRadius radiusData)
        (σ +⁺ 1⁺)
        .snd)

  prove :
    PowerSeriesSecondDerivativePartialSumsBoundOnBall a (σ +⁺ 1⁺) →
    HasDerivativeAt
      f
      x
      (centeredPowerSeriesSumEverywhere
        (derivativePowerSeries a)
        c
        (derivativePowerSeriesInfiniteRadius radiusData)
        x)
  prove (Γ , bound) =
    partialSumsDerivativeTargetModulus
      (powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound Γ) ,
    hasPowerSeriesDerivativeFromSecondDerivativeBounds
      {a = a}
      {c = c}
      {x = x}
      {ρ = σ +⁺ 1⁺}
      {σ = σ}
      {Γ = Γ}
      radiusData
      expansion
      x-displacement-bound
      (secondDerivativeCanonicalUnitMargin σ Γ)
      bound
