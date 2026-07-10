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
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.Derivative.Base
  using (HasDerivativeAt ; HasDerivativeAtWith)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Core
  using (HasPowerSeriesAtWith)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using (derivativePowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence
  using (derivativePowerSeriesInfiniteRadius)
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using (PowerSeriesMajorizedOnBall)
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.SecondDerivativePartialSumBounds
  using
    ( PowerSeriesSecondDerivativePartialSumsBoundOnBall
    ; powerSeriesSecondDerivativePartialSumsBoundMajorizedRationalΓ
    ; powerSeriesSecondDerivativePartialSumsBoundOnBallFromConvergence
    ; powerSeriesSecondDerivativePartialSumsBoundOnBallFromMajorizedRationalBounds
    )
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Theorem
  using
    ( centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromSecondDerivativePartialSumsBoundOnSubballCanonicalIndex→hasDerivativeAtWith
    ; hasPowerSeriesAtWith→hasDerivativeAtWithFromSecondDerivativePartialSumsBoundOnSubballCanonicalIndex
    )
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.UniformPartialSums
  using
    ( partialSumsDerivativeTargetModulus
    ; powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound
    )
open import Constructive.Data.PositiveRationals
open import Constructive.Data.Rationals as Rational


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


centeredPowerSeriesSumEverywhereFormalDerivativeAtFromSecondDerivativePartialSumsBound :
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {σ : ℚ⁺} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  BoundedByᶜ σ (centeredDisplacement c x) →
  PowerSeriesSecondDerivativePartialSumsBoundOnBall a (σ +⁺ 1⁺) →
  HasDerivativeAt
    (centeredPowerSeriesSumEverywhere a c radiusData)
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      (derivativePowerSeriesInfiniteRadius radiusData)
      x)
centeredPowerSeriesSumEverywhereFormalDerivativeAtFromSecondDerivativePartialSumsBound
  {a = a}
  {c = c}
  {x = x}
  {σ = σ}
  radiusData
  x-displacement-bound
  (Γ , secondDerivativeBound) =
  partialSumsDerivativeTargetModulus
    (powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound Γ) ,
  centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromSecondDerivativePartialSumsBoundOnSubballCanonicalIndex→hasDerivativeAtWith
    {a = a}
    {c = c}
    {x = x}
    {ρ = σ +⁺ 1⁺}
    {σ = σ}
    {Γ = Γ}
    radiusData
    x-displacement-bound
    (secondDerivativeCanonicalUnitMargin σ Γ)
    secondDerivativeBound


centeredPowerSeriesSumEverywhereFormalDerivativeAtFromSecondDerivativeConvergence :
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {σ : ℚ⁺} →
  {ν : ℚ⁺ → ℕ} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  BoundedByᶜ σ (centeredDisplacement c x) →
  HasPowerSeriesOnBallWith
    (derivativePowerSeries (derivativePowerSeries a))
    (σ +⁺ 1⁺)
    ν →
  ∥ HasDerivativeAt
      (centeredPowerSeriesSumEverywhere a c radiusData)
      x
      (centeredPowerSeriesSumEverywhere
        (derivativePowerSeries a)
        c
        (derivativePowerSeriesInfiniteRadius radiusData)
        x) ∥₁
centeredPowerSeriesSumEverywhereFormalDerivativeAtFromSecondDerivativeConvergence
  {a = a}
  {c = c}
  {x = x}
  {σ = σ}
  radiusData
  x-displacement-bound
  secondDerivativeConvergence =
  Prop.rec
    squash₁
    (λ secondDerivativeBound →
      ∣ centeredPowerSeriesSumEverywhereFormalDerivativeAtFromSecondDerivativePartialSumsBound
          {a = a}
          {c = c}
          {x = x}
          {σ = σ}
          radiusData
          x-displacement-bound
          secondDerivativeBound ∣₁)
    (powerSeriesSecondDerivativePartialSumsBoundOnBallFromConvergence
      secondDerivativeConvergence)


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
  centeredPowerSeriesSumEverywhereFormalDerivativeAtFromSecondDerivativeConvergence
    {a = a}
    {c = c}
    {x = x}
    {σ = σ}
    radiusData
    x-displacement-bound
    (derivativePowerSeriesInfiniteRadius
      (derivativePowerSeriesInfiniteRadius radiusData)
      (σ +⁺ 1⁺)
      .snd)


centeredPowerSeriesSumEverywhereFormalDerivativeAtWithFromSecondDerivativeMajorizedRationalBoundsOnSubball :
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {ν : ℚ⁺ → ℕ} →
  {β : ℕ → ℚ⁺} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  BoundedByᶜ σ (centeredDisplacement c x) →
  (margin :
    (ε : ℚ⁺) →
    radius
      (σ +⁺
        partialSumsDerivativeTargetModulus
          (powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound
            (powerSeriesSecondDerivativePartialSumsBoundMajorizedRationalΓ
              β
              ν))
          ε)
      ℚOrder.≤ radius ρ) →
  PowerSeriesMajorizedOnBall
    (derivativePowerSeries (derivativePowerSeries a))
    (σ +⁺ 1⁺)
    v
    ν →
  ((n : ℕ) → BoundedByᶜ (β n) (v n)) →
  HasDerivativeAtWith
    (centeredPowerSeriesSumEverywhere a c radiusData)
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      (derivativePowerSeriesInfiniteRadius radiusData)
      x)
    (partialSumsDerivativeTargetModulus
      (powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound
        (powerSeriesSecondDerivativePartialSumsBoundMajorizedRationalΓ
          β
          ν)))
centeredPowerSeriesSumEverywhereFormalDerivativeAtWithFromSecondDerivativeMajorizedRationalBoundsOnSubball
  {a = a}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {v = v}
  {ν = ν}
  {β = β}
  radiusData
  x-displacement-bound
  margin
  majorized
  β-bound =
  centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromSecondDerivativePartialSumsBoundOnSubballCanonicalIndex→hasDerivativeAtWith
    {a = a}
    {c = c}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {Γ = powerSeriesSecondDerivativePartialSumsBoundMajorizedRationalΓ β ν}
    radiusData
    x-displacement-bound
    margin
    (powerSeriesSecondDerivativePartialSumsBoundOnBallFromMajorizedRationalBounds
      {a = a}
      {ρ = σ +⁺ 1⁺}
      {v = v}
      {ν = ν}
      {β = β}
      majorized
      β-bound
      .snd)


hasPowerSeriesAtWith→formalDerivativeAtFromSecondDerivativePartialSumsBound :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {σ : ℚ⁺} →
  {seriesModulus : ℚ⁺ → ℕ} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  HasPowerSeriesAtWith f c a (σ +⁺ 1⁺) seriesModulus →
  BoundedByᶜ σ (centeredDisplacement c x) →
  PowerSeriesSecondDerivativePartialSumsBoundOnBall a (σ +⁺ 1⁺) →
  HasDerivativeAt
    f
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      (derivativePowerSeriesInfiniteRadius radiusData)
      x)
hasPowerSeriesAtWith→formalDerivativeAtFromSecondDerivativePartialSumsBound
  {a = a}
  {c = c}
  {x = x}
  {σ = σ}
  radiusData
  expansion
  x-displacement-bound
  (Γ , secondDerivativeBound) =
  partialSumsDerivativeTargetModulus
    (powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound Γ) ,
  hasPowerSeriesAtWith→hasDerivativeAtWithFromSecondDerivativePartialSumsBoundOnSubballCanonicalIndex
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
    secondDerivativeBound


hasPowerSeriesAtWith→formalDerivativeAtFromSecondDerivativeConvergence :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {σ : ℚ⁺} →
  {seriesModulus : ℚ⁺ → ℕ} →
  {ν : ℚ⁺ → ℕ} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  HasPowerSeriesAtWith f c a (σ +⁺ 1⁺) seriesModulus →
  BoundedByᶜ σ (centeredDisplacement c x) →
  HasPowerSeriesOnBallWith
    (derivativePowerSeries (derivativePowerSeries a))
    (σ +⁺ 1⁺)
    ν →
  ∥ HasDerivativeAt
      f
      x
      (centeredPowerSeriesSumEverywhere
        (derivativePowerSeries a)
        c
        (derivativePowerSeriesInfiniteRadius radiusData)
        x) ∥₁
hasPowerSeriesAtWith→formalDerivativeAtFromSecondDerivativeConvergence
  {a = a}
  {c = c}
  {x = x}
  {σ = σ}
  radiusData
  expansion
  x-displacement-bound
  secondDerivativeConvergence =
  Prop.rec
    squash₁
    (λ secondDerivativeBound →
      ∣ hasPowerSeriesAtWith→formalDerivativeAtFromSecondDerivativePartialSumsBound
          {a = a}
          {c = c}
          {x = x}
          {σ = σ}
          radiusData
          expansion
          x-displacement-bound
          secondDerivativeBound ∣₁)
    (powerSeriesSecondDerivativePartialSumsBoundOnBallFromConvergence
      secondDerivativeConvergence)


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
  {a = a}
  {c = c}
  {x = x}
  {σ = σ}
  radiusData
  expansion
  x-displacement-bound =
  hasPowerSeriesAtWith→formalDerivativeAtFromSecondDerivativeConvergence
    {a = a}
    {c = c}
    {x = x}
    {σ = σ}
    radiusData
    expansion
    x-displacement-bound
    (derivativePowerSeriesInfiniteRadius
      (derivativePowerSeriesInfiniteRadius radiusData)
      (σ +⁺ 1⁺)
      .snd)


hasPowerSeriesAtWith→formalDerivativeAtWithFromSecondDerivativeMajorizedRationalBoundsOnSubball :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {seriesModulus : ℚ⁺ → ℕ} →
  {v : ℕ → ℝᶜ} →
  {ν : ℚ⁺ → ℕ} →
  {β : ℕ → ℚ⁺} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  HasPowerSeriesAtWith f c a ρ seriesModulus →
  BoundedByᶜ σ (centeredDisplacement c x) →
  (margin :
    (ε : ℚ⁺) →
    radius
      (σ +⁺
        partialSumsDerivativeTargetModulus
          (powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound
            (powerSeriesSecondDerivativePartialSumsBoundMajorizedRationalΓ
              β
              ν))
          ε)
      ℚOrder.≤ radius ρ) →
  PowerSeriesMajorizedOnBall
    (derivativePowerSeries (derivativePowerSeries a))
    (σ +⁺ 1⁺)
    v
    ν →
  ((n : ℕ) → BoundedByᶜ (β n) (v n)) →
  HasDerivativeAtWith
    f
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      (derivativePowerSeriesInfiniteRadius radiusData)
      x)
    (partialSumsDerivativeTargetModulus
      (powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound
        (powerSeriesSecondDerivativePartialSumsBoundMajorizedRationalΓ
          β
          ν)))
hasPowerSeriesAtWith→formalDerivativeAtWithFromSecondDerivativeMajorizedRationalBoundsOnSubball
  {a = a}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {v = v}
  {ν = ν}
  {β = β}
  radiusData
  expansion
  x-displacement-bound
  margin
  majorized
  β-bound =
  hasPowerSeriesAtWith→hasDerivativeAtWithFromSecondDerivativePartialSumsBoundOnSubballCanonicalIndex
    {a = a}
    {c = c}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {Γ = powerSeriesSecondDerivativePartialSumsBoundMajorizedRationalΓ β ν}
    radiusData
    expansion
    x-displacement-bound
    margin
    (powerSeriesSecondDerivativePartialSumsBoundOnBallFromMajorizedRationalBounds
      {a = a}
      {ρ = σ +⁺ 1⁺}
      {v = v}
      {ν = ν}
      {β = β}
      majorized
      β-bound
      .snd)
