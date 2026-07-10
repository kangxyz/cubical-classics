{-

Uniform partial-sum derivative moduli for termwise derivatives

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.UniformPartialSums where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (ℕ ; suc ; zero)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.Derivative.Base
  using (HasDerivativeAtWith)
open import Constructive.Analysis.Reals.Calculus.Derivative.BoundedSegment.Base
  using
    ( BoundedOnBallWith
    ; HasDerivativeOnBallWith
    ; boundedSecondDerivativeHasDerivativeAtWithFromSecondBound
    ; hasDerivativeAtWith-submodulus
    ; isPropHasDerivativeAtWith
    )
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using (bounded-byᶜ-zero ; shiftPowerSeries ; powerSeriesPartialSum-shift)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using (derivativePowerSeries)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Index
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.PartialSums
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Finite
  using
    ( powerSeriesConstantPartialSumHasDerivativeAtWith
    ; powerSeriesFormalDerivativePartialSum-step-value
    )
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.IteratedBounds
  using (powerSeriesPartialDerivativeRemainderBoundFromPartialSumsDerivative)


powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound :
  ℚ⁺ →
  PrecisionModulus
powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound Γ ε =
  min⁺ 1⁺ (posInv⁺ (Γ +⁺ 1⁺) *⁺ quarter⁺ ε)


PowerSeriesSecondDerivativePartialSumsBoundOnBallWith :
  PowerSeries →
  ℚ⁺ →
  ℚ⁺ →
  Type₀
PowerSeriesSecondDerivativePartialSumsBoundOnBallWith a ρ Γ =
  (y : ℝᶜ) →
  BoundedByᶜ ρ y →
  (n : ℕ) →
  BoundedByᶜ Γ
    (powerSeriesPartialSum
      (derivativePowerSeries (derivativePowerSeries a))
      y
      n)


private
  PowerSeriesPartialSumBoundedOnBallWith :
    PowerSeries →
    ℚ⁺ →
    ℕ →
    ℚ⁺ →
    Type₀
  PowerSeriesPartialSumBoundedOnBallWith a ρ n Γ =
    BoundedOnBallWith
      (λ y → powerSeriesPartialSum a y n)
      ρ
      Γ

  PowerSeriesPartialSumBoundedOnBall :
    PowerSeries →
    ℚ⁺ →
    ℕ →
    Type₀
  PowerSeriesPartialSumBoundedOnBall a ρ n =
    Σ[ Γ ∈ ℚ⁺ ] PowerSeriesPartialSumBoundedOnBallWith a ρ n Γ

  finitePartialSumBoundedOnBall :
    (a : PowerSeries) →
    (ρ : ℚ⁺) →
    (n : ℕ) →
    ∥ PowerSeriesPartialSumBoundedOnBall a ρ n ∥₁
  finitePartialSumBoundedOnBall a ρ zero =
    ∣ 1⁺ , (λ _ _ → bounded-byᶜ-zero 1⁺) ∣₁
  finitePartialSumBoundedOnBall a ρ (suc n) =
    Prop.rec
      squash₁
      coefficientCase
      (merely-boundedᶜ (a zero))
    where
    coefficientCase :
      Σ[ κ ∈ ℚ⁺ ] BoundedByᶜ κ (a zero) →
      ∥ PowerSeriesPartialSumBoundedOnBall a ρ (suc n) ∥₁
    coefficientCase (κ , a0-bound) =
      Prop.rec
        squash₁
        tailCase
        (finitePartialSumBoundedOnBall (shiftPowerSeries a) ρ n)
      where
      tailCase :
        PowerSeriesPartialSumBoundedOnBall (shiftPowerSeries a) ρ n →
        ∥ PowerSeriesPartialSumBoundedOnBall a ρ (suc n) ∥₁
      tailCase (Γ , tailBound) =
        ∣ κ +⁺ (ρ *⁺ Γ) , bound ∣₁
        where
        bound :
          PowerSeriesPartialSumBoundedOnBallWith
            a
            ρ
            (suc n)
            (κ +⁺ (ρ *⁺ Γ))
        bound y y-bound =
          subst
            (BoundedByᶜ (κ +⁺ (ρ *⁺ Γ)))
            (sym (powerSeriesPartialSum-shift a y n))
            shiftedBound
          where
          shiftedTail : ℝᶜ
          shiftedTail =
            powerSeriesPartialSum (shiftPowerSeries a) y n

          productBound :
            BoundedByᶜ (ρ *⁺ Γ) (y ·ᶜ shiftedTail)
          productBound =
            bounded-byᶜ-mul
              ρ
              Γ
              y
              shiftedTail
              y-bound
              (tailBound y y-bound)

          shiftedBound :
            BoundedByᶜ
              (κ +⁺ (ρ *⁺ Γ))
              (a zero +ᶜ y ·ᶜ shiftedTail)
          shiftedBound =
            bounded-byᶜ-add
              κ
              (ρ *⁺ Γ)
              (a zero)
              (y ·ᶜ shiftedTail)
              a0-bound
              productBound

  PowerSeriesPartialSumDerivativeOnBallWith :
    PowerSeries →
    ℚ⁺ →
    ℕ →
    PrecisionModulus →
    Type₀
  PowerSeriesPartialSumDerivativeOnBallWith a ρ n μ =
    HasDerivativeOnBallWith
      (λ y → powerSeriesPartialSum a y (suc n))
      (λ y → powerSeriesPartialSum (derivativePowerSeries a) y n)
      ρ
      μ

  PowerSeriesPartialSumDerivativeOnBall :
    PowerSeries →
    ℚ⁺ →
    ℕ →
    Type₀
  PowerSeriesPartialSumDerivativeOnBall a ρ n =
    Σ[ μ ∈ PrecisionModulus ]
      PowerSeriesPartialSumDerivativeOnBallWith a ρ n μ

  finitePartialSumDerivativeOnBall :
    (a : PowerSeries) →
    (ρ : ℚ⁺) →
    (n : ℕ) →
    ∥ PowerSeriesPartialSumDerivativeOnBall a ρ n ∥₁
  finitePartialSumDerivativeOnBall a ρ zero =
    ∣ (λ _ → 1⁺) ,
      (λ _ _ → powerSeriesConstantPartialSumHasDerivativeAtWith) ∣₁
  finitePartialSumDerivativeOnBall a ρ (suc n) =
    Prop.rec
      squash₁
      shiftedDerivativeCase
      (finitePartialSumDerivativeOnBall (shiftPowerSeries a) ρ n)
    where
    shiftedDerivativeCase :
      PowerSeriesPartialSumDerivativeOnBall (shiftPowerSeries a) ρ n →
      ∥ PowerSeriesPartialSumDerivativeOnBall a ρ (suc n) ∥₁
    shiftedDerivativeCase (μ , shiftedDerivative) =
      Prop.rec
        squash₁
        derivativeBoundCase
        (finitePartialSumBoundedOnBall
          (derivativePowerSeries (shiftPowerSeries a))
          ρ
          n)
      where
      derivativeBoundCase :
        PowerSeriesPartialSumBoundedOnBall
          (derivativePowerSeries (shiftPowerSeries a))
          ρ
          n →
        ∥ PowerSeriesPartialSumDerivativeOnBall a ρ (suc n) ∥₁
      derivativeBoundCase (Γ , derivativeBound) =
        ∣ powerSeriesPartialSumShiftDerivativeStepModulus ρ Γ μ ,
          derivativeOnBall ∣₁
        where
        derivativeOnBall :
          PowerSeriesPartialSumDerivativeOnBallWith
            a
            ρ
            (suc n)
            (powerSeriesPartialSumShiftDerivativeStepModulus ρ Γ μ)
        derivativeOnBall y y-bound =
          powerSeriesPartialSumShiftDerivativeStepAtWith
            ρ
            Γ
            y-bound
            (derivativeBound y y-bound)
            (shiftedDerivative y y-bound)
            (powerSeriesFormalDerivativePartialSum-step-value a y n)


merelyPowerSeriesPartialSumHasDerivativeOnBall :
  (a : PowerSeries) →
  (ρ : ℚ⁺) →
  (n : ℕ) →
  ∥ Σ[ μ ∈ PrecisionModulus ]
      HasDerivativeOnBallWith
        (λ y → powerSeriesPartialSum a y (suc n))
        (λ y → powerSeriesPartialSum (derivativePowerSeries a) y n)
        ρ
        μ ∥₁
merelyPowerSeriesPartialSumHasDerivativeOnBall =
  finitePartialSumDerivativeOnBall






powerSeriesFormalPartialSumsHaveDerivativeWithFromSecondDerivativeBound :
  {a : PowerSeries} →
  {x : ℝᶜ} →
  (σ Γ : ℚ⁺) →
  BoundedByᶜ σ x →
  PowerSeriesSecondDerivativePartialSumsBoundOnBallWith a (σ +⁺ 1⁺) Γ →
  PowerSeriesFormalPartialSumsHaveDerivativeWith
    a
    x
    (λ _ → powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound Γ)
powerSeriesFormalPartialSumsHaveDerivativeWithFromSecondDerivativeBound
  {a = a}
  {x = x}
  σ
  Γ
  x-bound
  secondBound
  zero =
  powerSeriesConstantPartialSumHasDerivativeAtWith
powerSeriesFormalPartialSumsHaveDerivativeWithFromSecondDerivativeBound
  {a = a}
  {x = x}
  σ
  Γ
  x-bound
  secondBound
  (suc n) =
  Prop.rec
    targetProp
    firstDerivativeCase
    (finitePartialSumDerivativeOnBall a (σ +⁺ 1⁺) (suc n))
  where
  targetModulus : PrecisionModulus
  targetModulus =
    powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound Γ

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
    PowerSeriesPartialSumDerivativeOnBall a (σ +⁺ 1⁺) (suc n) →
    HasDerivativeAtWith
      (λ y → powerSeriesPartialSum a y (suc (suc n)))
      x
      (powerSeriesPartialSum (derivativePowerSeries a) x (suc n))
      targetModulus
  firstDerivativeCase (μ , firstDerivative) =
    Prop.rec
      targetProp
      secondDerivativeCase
      (finitePartialSumDerivativeOnBall
        (derivativePowerSeries a)
        (σ +⁺ 1⁺)
        n)
    where
    secondDerivativeCase :
      PowerSeriesPartialSumDerivativeOnBall
        (derivativePowerSeries a)
        (σ +⁺ 1⁺)
        n →
      HasDerivativeAtWith
        (λ y → powerSeriesPartialSum a y (suc (suc n)))
        x
        (powerSeriesPartialSum (derivativePowerSeries a) x (suc n))
        targetModulus
    secondDerivativeCase (ν , secondDerivative) =
      boundedSecondDerivativeHasDerivativeAtWithFromSecondBound
        σ
        Γ
        firstDerivative
        secondDerivative
        (λ y y-bound → secondBound y y-bound n)
        x
        x-bound




partialSumsDerivativeTargetModulus :
  PrecisionModulus →
  PrecisionModulus
partialSumsDerivativeTargetModulus μ ε =
  μ (quarter⁺ ε)


powerSeriesPartialSumsDerivativeUniformModulus-constant :
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  PowerSeriesPartialSumsDerivativeUniformModulus
    χ
    (partialSumsDerivativeTargetModulus μ)
    (λ _ → μ)
powerSeriesPartialSumsDerivativeUniformModulus-constant
  {μ = μ}
  ε
  η =
  Rational.≤-refl (radius (μ (quarter⁺ ε)))




powerSeriesFormalPartialDerivativeRemainderBoundFromUniformPartialSumsDerivative :
  {a : PowerSeries} →
  {x : ℝᶜ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  PowerSeriesFormalPartialSumsHaveDerivativeWith a x (λ _ → μ) →
  PowerSeriesPartialDerivativeRemainderBoundWith
    a
    (derivativePowerSeries a)
    x
    χ
    (partialSumsDerivativeTargetModulus μ)
powerSeriesFormalPartialDerivativeRemainderBoundFromUniformPartialSumsDerivative
  {χ = χ}
  {μ = μ}
  partialDerivative =
  powerSeriesPartialDerivativeRemainderBoundFromPartialSumsDerivative
    partialDerivative
    (powerSeriesPartialSumsDerivativeModulusLargeFromUniformModulus
      {χ = χ}
      {μ = partialSumsDerivativeTargetModulus μ}
      {ω = λ _ → μ}
      (powerSeriesPartialSumsDerivativeUniformModulus-constant
        {χ = χ}
        {μ = μ}))
