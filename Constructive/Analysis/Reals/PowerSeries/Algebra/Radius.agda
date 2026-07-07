{-

Part of Constructive.Analysis.Reals.PowerSeries.Algebra

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Algebra.Radius where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; max ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.HITs.PropositionalTruncation as Prop

open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Metric.Instances.CauchyReals
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower)
open import Constructive.Analysis.Reals.Sequences.Base
  using
    ( maxModulus
    ; maxModulus-antitone
    ; maxModulus-left≤
    ; maxModulus-right≤
    ; splitModulus
    ; half-mono-≤
    )
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open import Constructive.Analysis.Reals.PowerSeries.Algebra.Internal
open import Constructive.Analysis.Reals.PowerSeries.Algebra.Core
open import Constructive.Analysis.Reals.PowerSeries.Algebra.ZeroConstant
open import Constructive.Analysis.Reals.PowerSeries.Algebra.Pointwise
open import Constructive.Analysis.Reals.PowerSeries.Algebra.Sums
open import Constructive.Analysis.Reals.PowerSeries.Algebra.Additive
open import Constructive.Analysis.Reals.PowerSeries.Algebra.Scaling

negPowerSeriesRadius :
  {a : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius a R →
  HasPowerSeriesRadius (negPowerSeries a) R
negPowerSeriesRadius radiusData =
  record
    { onSubball =
        λ ρ ρ<R →
          negPowerSeriesOnBall
            (HasPowerSeriesRadius.onSubball radiusData ρ ρ<R)
    }


addPowerSeriesRadius :
  {a b : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius a R →
  HasPowerSeriesRadius b R →
  HasPowerSeriesRadius (addPowerSeries a b) R
addPowerSeriesRadius left right =
  record
    { onSubball =
        λ ρ ρ<R →
          addPowerSeriesOnBall
            (HasPowerSeriesRadius.onSubball left ρ ρ<R)
            (HasPowerSeriesRadius.onSubball right ρ ρ<R)
    }


subPowerSeriesRadius :
  {a b : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius a R →
  HasPowerSeriesRadius b R →
  HasPowerSeriesRadius (subPowerSeries a b) R
subPowerSeriesRadius left right =
  record
    { onSubball =
        λ ρ ρ<R →
          subPowerSeriesOnBall
            (HasPowerSeriesRadius.onSubball left ρ ρ<R)
            (HasPowerSeriesRadius.onSubball right ρ ρ<R)
    }


rationalScalePowerSeriesRadius :
  (q : ℚ) →
  {a : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius a R →
  HasPowerSeriesRadius (rationalScalePowerSeries q a) R
rationalScalePowerSeriesRadius q radiusData =
  record
    { onSubball =
        λ ρ ρ<R →
          rationalScalePowerSeriesOnBall
            q
            (HasPowerSeriesRadius.onSubball radiusData ρ ρ<R)
    }


realScalePowerSeriesRadius :
  (x : ℝᶜ) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ x →
  {a : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius a R →
  HasPowerSeriesRadius (realScalePowerSeries x a) R
realScalePowerSeriesRadius x κ x-bound radiusData =
  record
    { onSubball =
        λ ρ ρ<R →
          realScalePowerSeriesOnBall
            x
            κ
            x-bound
            (HasPowerSeriesRadius.onSubball radiusData ρ ρ<R)
    }


negPowerSeriesInfiniteRadius :
  {a : PowerSeries} →
  HasInfinitePowerSeriesRadius a →
  HasInfinitePowerSeriesRadius (negPowerSeries a)
negPowerSeriesInfiniteRadius radiusData ρ =
  negPowerSeriesOnBall (radiusData ρ)


centeredPowerSeriesSumEverywhere-neg :
  {a : PowerSeries} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (c x : ℝᶜ) →
  centeredPowerSeriesSumEverywhere
    (negPowerSeries a)
    c
    (negPowerSeriesInfiniteRadius radiusData)
    x
  ≡
  -ᶜ centeredPowerSeriesSumEverywhere a c radiusData x
centeredPowerSeriesSumEverywhere-neg
  {a = a}
  radiusData
  c
  x =
  Prop.elim
    {P = λ bounds →
      left ≡ -ᶜ centeredPowerSeriesSumEverywhere a c radiusData x}
    (λ _ → MetricSpace.isSetCarrier CauchyRealsMetricSpace _ _)
    step
    (merely-boundedᶜ (centeredDisplacement c x))
  where
  left : ℝᶜ
  left =
    centeredPowerSeriesSumEverywhere
      (negPowerSeries a)
      c
      (negPowerSeriesInfiniteRadius radiusData)
      x

  step :
    Σ[ ρ ∈ ℚ⁺ ] BoundedByᶜ ρ (centeredDisplacement c x) →
    left ≡ -ᶜ centeredPowerSeriesSumEverywhere a c radiusData x
  step (ρ , displacementBound) =
    centeredPowerSeriesSumEverywhere-bound-path
      (negPowerSeries a)
      c
      (negPowerSeriesInfiniteRadius radiusData)
      ρ
      x
      inBall ∙
    powerSeriesSumOnBallFrom-neg
      (radiusData ρ)
      (centeredDisplacement c x)
      displacementBound ∙
    sym
      (cong
        -ᶜ_
        (centeredPowerSeriesSumEverywhere-bound-path
          a
          c
          radiusData
          ρ
          x
          inBall))
    where
    inBall : InPowerSeriesBall c ρ x
    inBall =
      record { displacementBound = displacementBound }


addPowerSeriesInfiniteRadius :
  {a b : PowerSeries} →
  HasInfinitePowerSeriesRadius a →
  HasInfinitePowerSeriesRadius b →
  HasInfinitePowerSeriesRadius (addPowerSeries a b)
addPowerSeriesInfiniteRadius left right ρ =
  addPowerSeriesOnBall (left ρ) (right ρ)


centeredPowerSeriesSumEverywhere-add :
  {a b : PowerSeries} →
  (leftRadius : HasInfinitePowerSeriesRadius a) →
  (rightRadius : HasInfinitePowerSeriesRadius b) →
  (c x : ℝᶜ) →
  centeredPowerSeriesSumEverywhere
    (addPowerSeries a b)
    c
    (addPowerSeriesInfiniteRadius leftRadius rightRadius)
    x
  ≡
  centeredPowerSeriesSumEverywhere a c leftRadius x +ᶜ
  centeredPowerSeriesSumEverywhere b c rightRadius x
centeredPowerSeriesSumEverywhere-add
  {a = a}
  {b = b}
  leftRadius
  rightRadius
  c
  x =
  Prop.elim
    {P = λ bounds →
      addSum ≡
      centeredPowerSeriesSumEverywhere a c leftRadius x +ᶜ
      centeredPowerSeriesSumEverywhere b c rightRadius x}
    (λ _ → MetricSpace.isSetCarrier CauchyRealsMetricSpace _ _)
    step
    (merely-boundedᶜ (centeredDisplacement c x))
  where
  addSum : ℝᶜ
  addSum =
    centeredPowerSeriesSumEverywhere
      (addPowerSeries a b)
      c
      (addPowerSeriesInfiniteRadius leftRadius rightRadius)
      x

  step :
    Σ[ ρ ∈ ℚ⁺ ] BoundedByᶜ ρ (centeredDisplacement c x) →
    addSum ≡
    centeredPowerSeriesSumEverywhere a c leftRadius x +ᶜ
    centeredPowerSeriesSumEverywhere b c rightRadius x
  step (ρ , displacementBound) =
    centeredPowerSeriesSumEverywhere-bound-path
      (addPowerSeries a b)
      c
      (addPowerSeriesInfiniteRadius leftRadius rightRadius)
      ρ
      x
      inBall ∙
    powerSeriesSumOnBallFrom-add
      (leftRadius ρ)
      (rightRadius ρ)
      (centeredDisplacement c x)
      displacementBound ∙
    cong₂
      _+ᶜ_
      (sym
        (centeredPowerSeriesSumEverywhere-bound-path
          a
          c
          leftRadius
          ρ
          x
          inBall))
      (sym
        (centeredPowerSeriesSumEverywhere-bound-path
          b
          c
          rightRadius
          ρ
          x
          inBall))
    where
    inBall : InPowerSeriesBall c ρ x
    inBall =
      record { displacementBound = displacementBound }


subPowerSeriesInfiniteRadius :
  {a b : PowerSeries} →
  HasInfinitePowerSeriesRadius a →
  HasInfinitePowerSeriesRadius b →
  HasInfinitePowerSeriesRadius (subPowerSeries a b)
subPowerSeriesInfiniteRadius left right ρ =
  subPowerSeriesOnBall (left ρ) (right ρ)


rationalScalePowerSeriesInfiniteRadius :
  (q : ℚ) →
  {a : PowerSeries} →
  HasInfinitePowerSeriesRadius a →
  HasInfinitePowerSeriesRadius (rationalScalePowerSeries q a)
rationalScalePowerSeriesInfiniteRadius q radiusData ρ =
  rationalScalePowerSeriesOnBall q (radiusData ρ)


realScalePowerSeriesInfiniteRadius :
  (x : ℝᶜ) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ x →
  {a : PowerSeries} →
  HasInfinitePowerSeriesRadius a →
  HasInfinitePowerSeriesRadius (realScalePowerSeries x a)
realScalePowerSeriesInfiniteRadius x κ x-bound radiusData ρ =
  realScalePowerSeriesOnBall x κ x-bound (radiusData ρ)


centeredPowerSeriesSumEverywhere-sub :
  {a b : PowerSeries} →
  (leftRadius : HasInfinitePowerSeriesRadius a) →
  (rightRadius : HasInfinitePowerSeriesRadius b) →
  (c x : ℝᶜ) →
  centeredPowerSeriesSumEverywhere
    (subPowerSeries a b)
    c
    (subPowerSeriesInfiniteRadius leftRadius rightRadius)
    x
  ≡
  centeredPowerSeriesSumEverywhere a c leftRadius x +ᶜ
  (-ᶜ centeredPowerSeriesSumEverywhere b c rightRadius x)
centeredPowerSeriesSumEverywhere-sub
  {a = a}
  {b = b}
  leftRadius
  rightRadius
  c
  x =
  Prop.elim
    {P = λ bounds →
      subSum ≡
      centeredPowerSeriesSumEverywhere a c leftRadius x +ᶜ
      (-ᶜ centeredPowerSeriesSumEverywhere b c rightRadius x)}
    (λ _ → MetricSpace.isSetCarrier CauchyRealsMetricSpace _ _)
    step
    (merely-boundedᶜ (centeredDisplacement c x))
  where
  subSum : ℝᶜ
  subSum =
    centeredPowerSeriesSumEverywhere
      (subPowerSeries a b)
      c
      (subPowerSeriesInfiniteRadius leftRadius rightRadius)
      x

  step :
    Σ[ ρ ∈ ℚ⁺ ] BoundedByᶜ ρ (centeredDisplacement c x) →
    subSum ≡
    centeredPowerSeriesSumEverywhere a c leftRadius x +ᶜ
    (-ᶜ centeredPowerSeriesSumEverywhere b c rightRadius x)
  step (ρ , displacementBound) =
    centeredPowerSeriesSumEverywhere-bound-path
      (subPowerSeries a b)
      c
      (subPowerSeriesInfiniteRadius leftRadius rightRadius)
      ρ
      x
      inBall ∙
    powerSeriesSumOnBallFrom-sub
      (leftRadius ρ)
      (rightRadius ρ)
      (centeredDisplacement c x)
      displacementBound ∙
    cong₂
      _+ᶜ_
      (sym
        (centeredPowerSeriesSumEverywhere-bound-path
          a
          c
          leftRadius
          ρ
          x
          inBall))
      (cong
        -ᶜ_
        (sym
          (centeredPowerSeriesSumEverywhere-bound-path
            b
            c
            rightRadius
            ρ
            x
            inBall)))
    where
    inBall : InPowerSeriesBall c ρ x
    inBall =
      record { displacementBound = displacementBound }


centeredPowerSeriesSumEverywhere-rationalScale :
  (q : ℚ) →
  {a : PowerSeries} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (c x : ℝᶜ) →
  centeredPowerSeriesSumEverywhere
    (rationalScalePowerSeries q a)
    c
    (rationalScalePowerSeriesInfiniteRadius q radiusData)
    x
  ≡
  rational q ·ᶜ centeredPowerSeriesSumEverywhere a c radiusData x
centeredPowerSeriesSumEverywhere-rationalScale
  q
  {a = a}
  radiusData
  c
  x =
  Prop.elim
    {P = λ bounds →
      scaledSum ≡
      rational q ·ᶜ centeredPowerSeriesSumEverywhere a c radiusData x}
    (λ _ → MetricSpace.isSetCarrier CauchyRealsMetricSpace _ _)
    step
    (merely-boundedᶜ (centeredDisplacement c x))
  where
  scaledSum : ℝᶜ
  scaledSum =
    centeredPowerSeriesSumEverywhere
      (rationalScalePowerSeries q a)
      c
      (rationalScalePowerSeriesInfiniteRadius q radiusData)
      x

  step :
    Σ[ ρ ∈ ℚ⁺ ] BoundedByᶜ ρ (centeredDisplacement c x) →
    scaledSum ≡
    rational q ·ᶜ centeredPowerSeriesSumEverywhere a c radiusData x
  step (ρ , displacementBound) =
    centeredPowerSeriesSumEverywhere-bound-path
      (rationalScalePowerSeries q a)
      c
      (rationalScalePowerSeriesInfiniteRadius q radiusData)
      ρ
      x
      inBall ∙
    powerSeriesSumOnBallFrom-rationalScale
      q
      (radiusData ρ)
      (centeredDisplacement c x)
      displacementBound ∙
    cong
      (rational q ·ᶜ_)
      (sym
        (centeredPowerSeriesSumEverywhere-bound-path
          a
          c
          radiusData
          ρ
          x
          inBall))
    where
    inBall : InPowerSeriesBall c ρ x
    inBall =
      record { displacementBound = displacementBound }


centeredPowerSeriesSumEverywhere-realScale :
  (s : ℝᶜ) →
  (κ : ℚ⁺) →
  (s-bound : BoundedByᶜ κ s) →
  {a : PowerSeries} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (c x : ℝᶜ) →
  centeredPowerSeriesSumEverywhere
    (realScalePowerSeries s a)
    c
    (realScalePowerSeriesInfiniteRadius s κ s-bound radiusData)
    x
  ≡
  s ·ᶜ centeredPowerSeriesSumEverywhere a c radiusData x
centeredPowerSeriesSumEverywhere-realScale
  s
  κ
  s-bound
  {a = a}
  radiusData
  c
  x =
  Prop.elim
    {P = λ bounds →
      scaledSum ≡
      s ·ᶜ centeredPowerSeriesSumEverywhere a c radiusData x}
    (λ _ → MetricSpace.isSetCarrier CauchyRealsMetricSpace _ _)
    step
    (merely-boundedᶜ (centeredDisplacement c x))
  where
  scaledSum : ℝᶜ
  scaledSum =
    centeredPowerSeriesSumEverywhere
      (realScalePowerSeries s a)
      c
      (realScalePowerSeriesInfiniteRadius s κ s-bound radiusData)
      x

  step :
    Σ[ ρ ∈ ℚ⁺ ] BoundedByᶜ ρ (centeredDisplacement c x) →
    scaledSum ≡
    s ·ᶜ centeredPowerSeriesSumEverywhere a c radiusData x
  step (ρ , displacementBound) =
    centeredPowerSeriesSumEverywhere-bound-path
      (realScalePowerSeries s a)
      c
      (realScalePowerSeriesInfiniteRadius s κ s-bound radiusData)
      ρ
      x
      inBall ∙
    powerSeriesSumOnBallFrom-realScale
      s
      κ
      s-bound
      (radiusData ρ)
      (centeredDisplacement c x)
      displacementBound ∙
    cong
      (s ·ᶜ_)
      (sym
        (centeredPowerSeriesSumEverywhere-bound-path
          a
          c
          radiusData
          ρ
          x
          inBall))
    where
    inBall : InPowerSeriesBall c ρ x
    inBall =
      record { displacementBound = displacementBound }
