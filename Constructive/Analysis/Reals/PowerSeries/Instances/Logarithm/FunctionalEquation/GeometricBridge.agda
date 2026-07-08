{-

Geometric-series bridge for logarithm functional equations

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.GeometricBridge where

open import Cubical.Foundations.Prelude

import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; suc ; zero)
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Instances.CauchyReals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedDivision
  using
    ( BoundedAwayPositiveᶜ
    ; reciprocalPositiveᶜ
    ; reciprocalPositiveᶜ-right
    )
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Inverse
  using (right-inverse-uniqueᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using (neg-zeroᶜ)
open import Constructive.Analysis.Reals.PowerSeries.Base
  using (powerSeriesTerm)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Geometric
  using
    ( alternatingGeometricPowerSeries
    ; alternatingGeometricPowerSeriesOnBallWith
    ; alternatingGeometricPowerSeriesTerm
    ; alternatingGeometricPowerSeriesTermPath
    )
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm
  using
    ( derivativePowerSeries-logOnePlus
    ; logOnePlusPowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using (derivativePowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Radius
  using
    ( HasPowerSeriesOnBallWith
    ; hasPowerSeriesOnBallWith-cong
    ; powerSeriesSumOnBall
    ; powerSeriesSumOnBall-coefficients-path
    )
open import Constructive.Analysis.Reals.Series
  using
    ( AntitoneTailModulus
    ; TailBound
    ; partialSum
    ; seriesSumFromFiniteTailBound-mul-left-convergesAt
    ; tailSum
    ; tailSum-one
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
  using
    ( positiveGeometricPowerModulus
    ; positiveGeometricPowerModulus-antitone
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using
    ( realGeometricFiniteIdentity
    ; realPower
    )
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


logOnePlusDerivativePowerSeriesOnSubunitBallWith :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  HasPowerSeriesOnBallWith
    (derivativePowerSeries logOnePlusPowerSeries)
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
logOnePlusDerivativePowerSeriesOnSubunitBallWith ρ ρ<1 =
  hasPowerSeriesOnBallWith-cong
    (λ n → sym (derivativePowerSeries-logOnePlus n))
    (alternatingGeometricPowerSeriesOnBallWith ρ ρ<1)


alternatingGeometricPowerSeriesFiniteIdentity :
  (h : ℝᶜ) →
  (n : ℕ) →
  (1ᶜ +ᶜ h) ·ᶜ
    partialSum (powerSeriesTerm alternatingGeometricPowerSeries h) n
  ≡
  1ᶜ +ᶜ (-ᶜ realPower (-ᶜ h) n)
alternatingGeometricPowerSeriesFiniteIdentity h n =
  cong₂
    _·ᶜ_
    (sym (cong (1ᶜ +ᶜ_) (neg-involutive h)))
    (cong (λ u → partialSum u n)
      (alternatingGeometricPowerSeriesTermPath h)) ∙
  realGeometricFiniteIdentity (-ᶜ h) n


alternatingGeometricPowerSeriesNeumannRightInverseOnBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (1ᶜ +ᶜ h) →
  (1ᶜ +ᶜ h) ·ᶜ
    powerSeriesSumOnBall
      alternatingGeometricPowerSeries
      ρ
      (positiveGeometricPowerModulus ρ ρ<1)
      (alternatingGeometricPowerSeriesOnBallWith ρ ρ<1)
      h
      h-bound
  ≡
  1ᶜ
alternatingGeometricPowerSeriesNeumannRightInverseOnBall
  ρ
  ρ<1
  h
  h-bound
  κ
  factorBound =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    product
    1ᶜ
    closeAt
  where
  μ : ℚ⁺ → ℕ
  μ =
    positiveGeometricPowerModulus ρ ρ<1

  μ-antitone : AntitoneTailModulus μ
  μ-antitone =
    positiveGeometricPowerModulus-antitone ρ ρ<1

  convergence :
    HasPowerSeriesOnBallWith
      alternatingGeometricPowerSeries
      ρ
      μ
  convergence =
    alternatingGeometricPowerSeriesOnBallWith ρ ρ<1

  tailBound :
    TailBound (powerSeriesTerm alternatingGeometricPowerSeries h) μ
  tailBound =
    HasPowerSeriesOnBallWith.tailBound convergence h h-bound

  factor : ℝᶜ
  factor =
    1ᶜ +ᶜ h

  sum : ℝᶜ
  sum =
    powerSeriesSumOnBall
      alternatingGeometricPowerSeries
      ρ
      μ
      convergence
      h
      h-bound

  product : ℝᶜ
  product =
    factor ·ᶜ sum

  closeAt :
    (ε : ℚ⁺) →
    product ∼[ ε ] 1ᶜ
  closeAt ε =
    subst
      (λ precision → product ∼[ precision ] 1ᶜ)
      (half⁺+half⁺≡ ε)
      (MetricSpace.close-triangle
        CauchyRealsMetricSpace
        product∼partial
        partial∼one)
    where
    η : ℚ⁺
    η =
      half⁺ ε

    productPrecision : ℚ⁺
    productPrecision =
      quarter⁺
        (half⁺
          (fst (mulᶜ-continuous-right-with-bound κ factor factorBound) η))

    tailPrecision : ℚ⁺
    tailPrecision =
      half⁺ η

    productIndex : ℕ
    productIndex =
      μ productPrecision

    tailIndex : ℕ
    tailIndex =
      μ tailPrecision

    n : ℕ
    n =
      productIndex Nat.+ tailIndex

    productIndex≤n : NatOrder._≤_ productIndex n
    productIndex≤n =
      tailIndex , Nat.+-comm tailIndex productIndex

    tailIndex≤n : NatOrder._≤_ tailIndex n
    tailIndex≤n =
      productIndex , refl

    product∼partial :
      product ∼[ η ]
      factor ·ᶜ
        partialSum (powerSeriesTerm alternatingGeometricPowerSeries h) n
    product∼partial =
      seriesSumFromFiniteTailBound-mul-left-convergesAt
        factor
        κ
        factorBound
        (powerSeriesTerm alternatingGeometricPowerSeries h)
        μ
        tailBound
        μ-antitone
        η
        n
        productIndex≤n

    termTailBound :
      BoundedByᶜ
        tailPrecision
        (tailSum
          (powerSeriesTerm alternatingGeometricPowerSeries h)
          n
          (suc zero))
    termTailBound =
      tailBound tailPrecision n (suc zero) tailIndex≤n

    termBound :
      BoundedByᶜ
        tailPrecision
        (powerSeriesTerm alternatingGeometricPowerSeries h n)
    termBound =
      subst
        (BoundedByᶜ tailPrecision)
        (tailSum-one (powerSeriesTerm alternatingGeometricPowerSeries h) n)
        termTailBound

    powerBound :
      BoundedByᶜ tailPrecision (realPower (-ᶜ h) n)
    powerBound =
      subst
        (BoundedByᶜ tailPrecision)
        (alternatingGeometricPowerSeriesTerm h n)
        termBound

    power∼zero :
      realPower (-ᶜ h) n ∼[ η ] 0ᶜ
    power∼zero =
      bounded-byᶜ-close-zero
        tailPrecision
        η
        (realPower (-ᶜ h) n)
        powerBound
        (half< η)

    negPower∼zero :
      (-ᶜ realPower (-ᶜ h) n) ∼[ η ] 0ᶜ
    negPower∼zero =
      subst
        (λ z → (-ᶜ realPower (-ᶜ h) n) ∼[ η ] z)
        neg-zeroᶜ
        (neg-close power∼zero)

    oneMinusPower∼one :
      (1ᶜ +ᶜ (-ᶜ realPower (-ᶜ h) n)) ∼[ η ] 1ᶜ
    oneMinusPower∼one =
      subst
        (λ z → (1ᶜ +ᶜ (-ᶜ realPower (-ᶜ h) n)) ∼[ η ] z)
        (add-zero-right 1ᶜ)
        (add-close-right 1ᶜ negPower∼zero)

    partial∼one :
      factor ·ᶜ
        partialSum (powerSeriesTerm alternatingGeometricPowerSeries h) n
      ∼[ η ]
      1ᶜ
    partial∼one =
      subst
        (λ z → z ∼[ η ] 1ᶜ)
        (sym (alternatingGeometricPowerSeriesFiniteIdentity h n))
        oneMinusPower∼one


logOnePlusDerivativePowerSeriesNeumannRightInverseOnBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (1ᶜ +ᶜ h) →
  (1ᶜ +ᶜ h) ·ᶜ
    powerSeriesSumOnBall
      (derivativePowerSeries logOnePlusPowerSeries)
      ρ
      (positiveGeometricPowerModulus ρ ρ<1)
      (logOnePlusDerivativePowerSeriesOnSubunitBallWith ρ ρ<1)
      h
      h-bound
  ≡
  1ᶜ
logOnePlusDerivativePowerSeriesNeumannRightInverseOnBall
  ρ
  ρ<1
  h
  h-bound
  κ
  factorBound =
  cong
    ((1ᶜ +ᶜ h) ·ᶜ_)
    (sym derivativeSumPath) ∙
  alternatingGeometricPowerSeriesNeumannRightInverseOnBall
    ρ
    ρ<1
    h
    h-bound
    κ
    factorBound
  where
  derivativeSumPath :
    powerSeriesSumOnBall
      alternatingGeometricPowerSeries
      ρ
      (positiveGeometricPowerModulus ρ ρ<1)
      (alternatingGeometricPowerSeriesOnBallWith ρ ρ<1)
      h
      h-bound
    ≡
    powerSeriesSumOnBall
      (derivativePowerSeries logOnePlusPowerSeries)
      ρ
      (positiveGeometricPowerModulus ρ ρ<1)
      (logOnePlusDerivativePowerSeriesOnSubunitBallWith ρ ρ<1)
      h
      h-bound
  derivativeSumPath =
    powerSeriesSumOnBall-coefficients-path
      (λ n → sym (derivativePowerSeries-logOnePlus n))
      (alternatingGeometricPowerSeriesOnBallWith ρ ρ<1)
      (logOnePlusDerivativePowerSeriesOnSubunitBallWith ρ ρ<1)
      h
      h-bound
      h-bound


logOnePlusDerivativePowerSeriesReciprocalOnBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  (factorLower κ : ℚ⁺) →
  (factorAway : BoundedAwayPositiveᶜ factorLower (1ᶜ +ᶜ h)) →
  BoundedByᶜ κ (1ᶜ +ᶜ h) →
  powerSeriesSumOnBall
    (derivativePowerSeries logOnePlusPowerSeries)
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (logOnePlusDerivativePowerSeriesOnSubunitBallWith ρ ρ<1)
    h
    h-bound
  ≡
  reciprocalPositiveᶜ factorLower (1ᶜ +ᶜ h) factorAway
logOnePlusDerivativePowerSeriesReciprocalOnBall
  ρ
  ρ<1
  h
  h-bound
  factorLower
  κ
  factorAway
  factorBound =
  sym
    (right-inverse-uniqueᶜ
      (reciprocalPositiveᶜ-right
        factorLower
        (1ᶜ +ᶜ h)
        factorAway)
      (logOnePlusDerivativePowerSeriesNeumannRightInverseOnBall
        ρ
        ρ<1
        h
        h-bound
        κ
        factorBound))
