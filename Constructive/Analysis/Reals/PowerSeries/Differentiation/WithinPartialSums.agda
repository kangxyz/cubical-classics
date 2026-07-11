{-

Uniform finite partial-sum derivatives with an explicit ball margin

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Differentiation.WithinPartialSums where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (suc ; zero)
open import Cubical.Data.Sigma using (Σ-syntax)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (squash₁)

open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.DerivativeData
  using (HasDerivativeAtWith)
open import Constructive.Analysis.Reals.Calculus.SegmentEstimates
  using (HasDerivativeOnBallWith ; isPropHasDerivativeAtWith)
open import Constructive.Analysis.Reals.Calculus.SecondOrderLocal
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.FormalDerivative
  using (derivativePowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.Finite
  using (powerSeriesConstantPartialSumHasDerivativeAtWith)
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.PartialSums
  using (PowerSeriesFormalPartialSumsHaveDerivativeWith)
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.UniformPartialSums
  using
    ( PowerSeriesSecondDerivativePartialSumsBoundOnBallWith
    ; merelyPowerSeriesPartialSumHasDerivativeOnBall
    )
open import Constructive.Data.PositiveRationals


powerSeriesFormalPartialSumsHaveDerivativeWithFromSecondDerivativeBoundOnMargin :
  {a : PowerSeries} →
  {x : ℝᶜ} →
  (σ ζ Γ : ℚ⁺) →
  BoundedByᶜ σ x →
  PowerSeriesSecondDerivativePartialSumsBoundOnBallWith a (σ +⁺ ζ) Γ →
  PowerSeriesFormalPartialSumsHaveDerivativeWith
    a
    x
    (λ _ → boundedSecondDerivativeMarginModulus ζ Γ)
powerSeriesFormalPartialSumsHaveDerivativeWithFromSecondDerivativeBoundOnMargin
  {a = a}
  {x = x}
  σ
  ζ
  Γ
  x-bound
  secondBound
  zero =
  powerSeriesConstantPartialSumHasDerivativeAtWith
powerSeriesFormalPartialSumsHaveDerivativeWithFromSecondDerivativeBoundOnMargin
  {a = a}
  {x = x}
  σ
  ζ
  Γ
  x-bound
  secondBound
  (suc n) =
  Prop.rec
    targetProp
    firstDerivativeCase
    (merelyPowerSeriesPartialSumHasDerivativeOnBall a (σ +⁺ ζ) (suc n))
  where
  targetModulus : PrecisionModulus
  targetModulus =
    boundedSecondDerivativeMarginModulus ζ Γ

  targetProp :
    isProp
      (HasDerivativeAtWith
        (λ y → powerSeriesPartialSum a y (suc (suc n)))
        x
        (powerSeriesPartialSum (derivativePowerSeries a) x (suc n))
        targetModulus)
  targetProp =
    isPropHasDerivativeAtWith
      (λ y → powerSeriesPartialSum a y (suc (suc n)))
      x
      (powerSeriesPartialSum (derivativePowerSeries a) x (suc n))
      targetModulus

  firstDerivativeCase :
    Σ[ μ ∈ PrecisionModulus ]
      HasDerivativeOnBallWith
        (λ y → powerSeriesPartialSum a y (suc (suc n)))
        (λ y → powerSeriesPartialSum (derivativePowerSeries a) y (suc n))
        (σ +⁺ ζ)
        μ →
    HasDerivativeAtWith
      (λ y → powerSeriesPartialSum a y (suc (suc n)))
      x
      (powerSeriesPartialSum (derivativePowerSeries a) x (suc n))
      targetModulus
  firstDerivativeCase (μ , firstDerivative) =
    Prop.rec
      targetProp
      secondDerivativeCase
      (merelyPowerSeriesPartialSumHasDerivativeOnBall
        (derivativePowerSeries a)
        (σ +⁺ ζ)
        n)
    where
    secondDerivativeCase :
      Σ[ ν ∈ PrecisionModulus ]
        HasDerivativeOnBallWith
          (λ y → powerSeriesPartialSum (derivativePowerSeries a) y (suc n))
          (λ y →
            powerSeriesPartialSum
              (derivativePowerSeries (derivativePowerSeries a))
              y
              n)
          (σ +⁺ ζ)
          ν →
      HasDerivativeAtWith
        (λ y → powerSeriesPartialSum a y (suc (suc n)))
        x
        (powerSeriesPartialSum (derivativePowerSeries a) x (suc n))
        targetModulus
    secondDerivativeCase (ν , secondDerivative) =
      boundedSecondDerivativeHasDerivativeAtWithFromSecondBoundOnMargin
        σ
        ζ
        Γ
        firstDerivative
        secondDerivative
        (λ y y-bound → secondBound y y-bound n)
        x
        x-bound
