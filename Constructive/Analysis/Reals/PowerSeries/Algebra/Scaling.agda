{-

Part of Constructive.Analysis.Reals.PowerSeries.Algebra

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Algebra.Scaling where

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
open import Constructive.Analysis.Reals.CauchyReals.Metric
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
open import Constructive.Analysis.Modulus
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

rationalScalePowerSeriesOnBallWith :
  (q : ℚ) →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesOnBallWith a ρ μ →
  HasPowerSeriesOnBallWith
    (rationalScalePowerSeries q a)
    ρ
    (rationalScaleModulus q μ)
rationalScalePowerSeriesOnBallWith q {a = a} {μ = μ} convergence =
  hasPowerSeriesOnBallWith
    (rationalScaleModulus-antitone
      q
      (HasPowerSeriesOnBallWith.antitoneModulus convergence))
    (λ h h-bound →
      subst
        (λ u → TailBound u (rationalScaleModulus q μ))
        (sym (funExt (rationalScalePowerSeriesTerm q a h)))
        (rationalScaleTailBound
          q
          (HasPowerSeriesOnBallWith.tailBound convergence h h-bound)))


rationalScalePowerSeriesOnBall :
  (q : ℚ) →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBall a ρ →
  HasPowerSeriesOnBall (rationalScalePowerSeries q a) ρ
rationalScalePowerSeriesOnBall q (μ , convergence) =
  rationalScaleModulus q μ ,
  rationalScalePowerSeriesOnBallWith q convergence


realScalePowerSeriesOnBallWith :
  (x : ℝᶜ) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ x →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesOnBallWith a ρ μ →
  HasPowerSeriesOnBallWith
    (realScalePowerSeries x a)
    ρ
    (realScaleModulus κ μ)
realScalePowerSeriesOnBallWith x κ x-bound {a = a} {μ = μ} convergence =
  hasPowerSeriesOnBallWith
    (realScaleModulus-antitone
      κ
      (HasPowerSeriesOnBallWith.antitoneModulus convergence))
    (λ h h-bound →
      subst
        (λ u → TailBound u (realScaleModulus κ μ))
        (sym (funExt (realScalePowerSeriesTerm x a h)))
        (realScaleTailBound
          x
          κ
          x-bound
          (HasPowerSeriesOnBallWith.tailBound convergence h h-bound)))


realScalePowerSeriesOnBall :
  (x : ℝᶜ) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ x →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBall a ρ →
  HasPowerSeriesOnBall (realScalePowerSeries x a) ρ
realScalePowerSeriesOnBall x κ x-bound (μ , convergence) =
  realScaleModulus κ μ ,
  realScalePowerSeriesOnBallWith x κ x-bound convergence


powerSeriesSumOnBall-rationalScale :
  (q : ℚ) →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    (rationalScalePowerSeries q a)
    ρ
    (rationalScaleModulus q μ)
    (rationalScalePowerSeriesOnBallWith q convergence)
    h
    h-bound
  ≡
  rational q ·ᶜ powerSeriesSumOnBall a ρ μ convergence h h-bound
powerSeriesSumOnBall-rationalScale
  q
  {a = a}
  {ρ = ρ}
  {μ = μ}
  convergence
  h
  h-bound =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    scaledSum
    scaledOriginalSum
    closeAt
  where
  scaledConvergence :
    HasPowerSeriesOnBallWith
      (rationalScalePowerSeries q a)
      ρ
      (rationalScaleModulus q μ)
  scaledConvergence =
    rationalScalePowerSeriesOnBallWith q convergence

  q-bound : BoundedByᶜ (scalar-bound q) (rational q)
  q-bound =
    rational-bound→boundedᶜ
      (scalar-bound q)
      q
      (scalar-bound-rational-boundᶜ q)

  scaledSum : ℝᶜ
  scaledSum =
    powerSeriesSumOnBall
      (rationalScalePowerSeries q a)
      ρ
      (rationalScaleModulus q μ)
      scaledConvergence
      h
      h-bound

  originalSum : ℝᶜ
  originalSum =
    powerSeriesSumOnBall a ρ μ convergence h h-bound

  scaledOriginalSum : ℝᶜ
  scaledOriginalSum =
    rational q ·ᶜ originalSum

  scaleModulus : ℚ⁺ → ℚ⁺
  scaleModulus =
    fst (mulᶜ-continuous-right-with-bound (scalar-bound q) (rational q) q-bound)

  leftIndex :
    ℚ⁺ →
    ℕ
  leftIndex ε =
    rationalScaleModulus
      q
      μ
      (quarter⁺ (half⁺ (half⁺ ε)))

  rightIndex :
    ℚ⁺ →
    ℕ
  rightIndex ε =
    μ (quarter⁺ (half⁺ (scaleModulus (half⁺ ε))))

  approximationIndex :
    ℚ⁺ →
    ℕ
  approximationIndex ε =
    max (leftIndex ε) (rightIndex ε)

  leftIndex≤approximation :
    (ε : ℚ⁺) →
    NatOrder._≤_ (leftIndex ε) (approximationIndex ε)
  leftIndex≤approximation ε =
    NatOrder.left-≤-max
      {m = leftIndex ε}
      {n = rightIndex ε}

  rightIndex≤approximation :
    (ε : ℚ⁺) →
    NatOrder._≤_ (rightIndex ε) (approximationIndex ε)
  rightIndex≤approximation ε =
    NatOrder.right-≤-max
      {n = rightIndex ε}
      {m = leftIndex ε}

  scaledPartialSum :
    ℚ⁺ →
    ℝᶜ
  scaledPartialSum ε =
    rational q ·ᶜ powerSeriesPartialSum a h (approximationIndex ε)

  leftTail :
    (ε : ℚ⁺) →
    scaledSum ∼[ half⁺ ε ] scaledPartialSum ε
  leftTail ε =
    subst
      (λ partial → scaledSum ∼[ half⁺ ε ] partial)
      (powerSeriesPartialSum-rationalScale q a h (approximationIndex ε))
      (seriesSumFromFiniteTailBoundConvergesAt
        (powerSeriesTerm (rationalScalePowerSeries q a) h)
        (rationalScaleModulus q μ)
        (HasPowerSeriesOnBallWith.tailBound
          scaledConvergence
          h
          h-bound)
        (HasPowerSeriesOnBallWith.antitoneModulus scaledConvergence)
        (half⁺ ε)
        (approximationIndex ε)
        (leftIndex≤approximation ε))

  rightTail :
    (ε : ℚ⁺) →
    scaledOriginalSum ∼[ half⁺ ε ] scaledPartialSum ε
  rightTail ε =
    seriesSumFromFiniteTailBound-mul-left-convergesAt
      (rational q)
      (scalar-bound q)
      q-bound
      (powerSeriesTerm a h)
      μ
      (HasPowerSeriesOnBallWith.tailBound convergence h h-bound)
      (HasPowerSeriesOnBallWith.antitoneModulus convergence)
      (half⁺ ε)
      (approximationIndex ε)
      (rightIndex≤approximation ε)

  closeAt :
    (ε : ℚ⁺) →
    scaledSum ∼[ ε ] scaledOriginalSum
  closeAt ε =
    subst
      (λ κ → scaledSum ∼[ κ ] scaledOriginalSum)
      (half⁺+half⁺≡ ε)
      (MetricSpace.close-triangle
        CauchyRealsMetricSpace
        (leftTail ε)
        (MetricSpace.close-sym CauchyRealsMetricSpace (rightTail ε)))


powerSeriesSumOnBall-realScale :
  (x : ℝᶜ) →
  (κ : ℚ⁺) →
  (x-bound : BoundedByᶜ κ x) →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    (realScalePowerSeries x a)
    ρ
    (realScaleModulus κ μ)
    (realScalePowerSeriesOnBallWith x κ x-bound convergence)
    h
    h-bound
  ≡
  x ·ᶜ powerSeriesSumOnBall a ρ μ convergence h h-bound
powerSeriesSumOnBall-realScale
  x
  κ
  x-bound
  {a = a}
  {ρ = ρ}
  {μ = μ}
  convergence
  h
  h-bound =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    scaledSum
    scaledOriginalSum
    closeAt
  where
  scaledConvergence :
    HasPowerSeriesOnBallWith
      (realScalePowerSeries x a)
      ρ
      (realScaleModulus κ μ)
  scaledConvergence =
    realScalePowerSeriesOnBallWith x κ x-bound convergence

  scaledSum : ℝᶜ
  scaledSum =
    powerSeriesSumOnBall
      (realScalePowerSeries x a)
      ρ
      (realScaleModulus κ μ)
      scaledConvergence
      h
      h-bound

  originalSum : ℝᶜ
  originalSum =
    powerSeriesSumOnBall a ρ μ convergence h h-bound

  scaledOriginalSum : ℝᶜ
  scaledOriginalSum =
    x ·ᶜ originalSum

  scaleModulus : ℚ⁺ → ℚ⁺
  scaleModulus =
    fst (mulᶜ-continuous-right-with-bound κ x x-bound)

  leftIndex :
    ℚ⁺ →
    ℕ
  leftIndex ε =
    realScaleModulus
      κ
      μ
      (quarter⁺ (half⁺ (half⁺ ε)))

  rightIndex :
    ℚ⁺ →
    ℕ
  rightIndex ε =
    μ (quarter⁺ (half⁺ (scaleModulus (half⁺ ε))))

  approximationIndex :
    ℚ⁺ →
    ℕ
  approximationIndex ε =
    max (leftIndex ε) (rightIndex ε)

  leftIndex≤approximation :
    (ε : ℚ⁺) →
    NatOrder._≤_ (leftIndex ε) (approximationIndex ε)
  leftIndex≤approximation ε =
    NatOrder.left-≤-max
      {m = leftIndex ε}
      {n = rightIndex ε}

  rightIndex≤approximation :
    (ε : ℚ⁺) →
    NatOrder._≤_ (rightIndex ε) (approximationIndex ε)
  rightIndex≤approximation ε =
    NatOrder.right-≤-max
      {n = rightIndex ε}
      {m = leftIndex ε}

  scaledPartialSum :
    ℚ⁺ →
    ℝᶜ
  scaledPartialSum ε =
    x ·ᶜ powerSeriesPartialSum a h (approximationIndex ε)

  leftTail :
    (ε : ℚ⁺) →
    scaledSum ∼[ half⁺ ε ] scaledPartialSum ε
  leftTail ε =
    subst
      (λ partial → scaledSum ∼[ half⁺ ε ] partial)
      (powerSeriesPartialSum-realScale x a h (approximationIndex ε))
      (seriesSumFromFiniteTailBoundConvergesAt
        (powerSeriesTerm (realScalePowerSeries x a) h)
        (realScaleModulus κ μ)
        (HasPowerSeriesOnBallWith.tailBound
          scaledConvergence
          h
          h-bound)
        (HasPowerSeriesOnBallWith.antitoneModulus scaledConvergence)
        (half⁺ ε)
        (approximationIndex ε)
        (leftIndex≤approximation ε))

  rightTail :
    (ε : ℚ⁺) →
    scaledOriginalSum ∼[ half⁺ ε ] scaledPartialSum ε
  rightTail ε =
    seriesSumFromFiniteTailBound-mul-left-convergesAt
      x
      κ
      x-bound
      (powerSeriesTerm a h)
      μ
      (HasPowerSeriesOnBallWith.tailBound convergence h h-bound)
      (HasPowerSeriesOnBallWith.antitoneModulus convergence)
      (half⁺ ε)
      (approximationIndex ε)
      (rightIndex≤approximation ε)

  closeAt :
    (ε : ℚ⁺) →
    scaledSum ∼[ ε ] scaledOriginalSum
  closeAt ε =
    subst
      (λ θ → scaledSum ∼[ θ ] scaledOriginalSum)
      (half⁺+half⁺≡ ε)
      (MetricSpace.close-triangle
        CauchyRealsMetricSpace
        (leftTail ε)
        (MetricSpace.close-sym CauchyRealsMetricSpace (rightTail ε)))


powerSeriesSumOnBallFrom-rationalScale :
  (q : ℚ) →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  (convergence : HasPowerSeriesOnBall a ρ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBallFrom
    (rationalScalePowerSeries q a)
    ρ
    (rationalScalePowerSeriesOnBall q convergence)
    h
    h-bound
  ≡
  rational q ·ᶜ powerSeriesSumOnBallFrom a ρ convergence h h-bound
powerSeriesSumOnBallFrom-rationalScale q (μ , convergence) h h-bound =
  powerSeriesSumOnBall-rationalScale q convergence h h-bound


powerSeriesSumOnBallFrom-realScale :
  (x : ℝᶜ) →
  (κ : ℚ⁺) →
  (x-bound : BoundedByᶜ κ x) →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  (convergence : HasPowerSeriesOnBall a ρ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBallFrom
    (realScalePowerSeries x a)
    ρ
    (realScalePowerSeriesOnBall x κ x-bound convergence)
    h
    h-bound
  ≡
  x ·ᶜ powerSeriesSumOnBallFrom a ρ convergence h h-bound
powerSeriesSumOnBallFrom-realScale x κ x-bound (μ , convergence) h h-bound =
  powerSeriesSumOnBall-realScale x κ x-bound convergence h h-bound


powerSeriesSumOnBall-subWithMax :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν : ℚ⁺ → ℕ} →
  (left : HasPowerSeriesOnBallWith a ρ μ) →
  (right : HasPowerSeriesOnBallWith b ρ ν) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    (subPowerSeries a b)
    ρ
    (splitModulus (maxModulus μ ν))
    (subPowerSeriesOnBallWithMax left right)
    h
    h-bound
  ≡
  powerSeriesSumOnBall a ρ μ left h h-bound +ᶜ
  (-ᶜ powerSeriesSumOnBall b ρ ν right h h-bound)
powerSeriesSumOnBall-subWithMax left right h h-bound =
  powerSeriesSumOnBall-addWithMax
    left
    (negPowerSeriesOnBallWith right)
    h
    h-bound ∙
  cong
    (powerSeriesSumOnBall _ _ _ left h h-bound +ᶜ_)
    (powerSeriesSumOnBall-neg right h h-bound)


powerSeriesSumOnBallFrom-sub :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  (left : HasPowerSeriesOnBall a ρ) →
  (right : HasPowerSeriesOnBall b ρ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBallFrom
    (subPowerSeries a b)
    ρ
    (subPowerSeriesOnBall left right)
    h
    h-bound
  ≡
  powerSeriesSumOnBallFrom a ρ left h h-bound +ᶜ
  (-ᶜ powerSeriesSumOnBallFrom b ρ right h h-bound)
powerSeriesSumOnBallFrom-sub (μ , left) (ν , right) h h-bound =
  powerSeriesSumOnBall-subWithMax left right h h-bound
