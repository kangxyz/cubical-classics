{-

Part of Constructive.Analysis.Reals.PowerSeries.Algebra

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Algebra.Sums where

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

powerSeriesSumOnBall-zero :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  (zero-bound : BoundedByᶜ ρ 0ᶜ) →
  powerSeriesSumOnBall a ρ μ convergence 0ᶜ zero-bound ≡
  a zero
powerSeriesSumOnBall-zero
  {a = a}
  {ρ = ρ}
  {μ = μ}
  convergence
  zero-bound =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    sum
    (a zero)
    closeAt
  where
  sum : ℝᶜ
  sum =
    powerSeriesSumOnBall a ρ μ convergence 0ᶜ zero-bound

  tailIndex :
    ℚ⁺ →
    ℕ
  tailIndex ε =
    μ (quarter⁺ (half⁺ ε))

  approximationIndex :
    ℚ⁺ →
    ℕ
  approximationIndex ε =
    max (tailIndex ε) (suc zero)

  tailIndex≤approximation :
    (ε : ℚ⁺) →
    NatOrder._≤_ (tailIndex ε) (approximationIndex ε)
  tailIndex≤approximation ε =
    NatOrder.left-≤-max
      {m = tailIndex ε}
      {n = suc zero}

  one≤approximation :
    (ε : ℚ⁺) →
    NatOrder._≤_ (suc zero) (approximationIndex ε)
  one≤approximation ε =
    NatOrder.right-≤-max
      {n = suc zero}
      {m = tailIndex ε}

  closeAt :
    (ε : ℚ⁺) →
    sum ∼[ ε ] a zero
  closeAt ε =
    subst
      (λ partial → sum ∼[ ε ] partial)
      (powerSeriesPartialSum-at-zero-positive
        a
        (approximationIndex ε)
        (one≤approximation ε))
      (seriesSumFromFiniteTailBoundConvergesAt
        (powerSeriesTerm a 0ᶜ)
        μ
        (HasPowerSeriesOnBallWith.tailBound convergence 0ᶜ zero-bound)
        (HasPowerSeriesOnBallWith.antitoneModulus convergence)
        ε
        (approximationIndex ε)
        (tailIndex≤approximation ε))


centeredDisplacement-center :
  (c : ℝᶜ) →
  centeredDisplacement c c ≡ 0ᶜ
centeredDisplacement-center c =
  cong (centeredDisplacement c) (sym (add-zero-right c)) ∙
  centeredDisplacement-center-plus c 0ᶜ


centeredPowerSeriesSumOnBall-center :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  (c : ℝᶜ) →
  (c-inBall : InPowerSeriesBall c ρ c) →
  centeredPowerSeriesSumOnBall a c ρ μ convergence c c-inBall ≡
  a zero
centeredPowerSeriesSumOnBall-center
  {a = a}
  {ρ = ρ}
  {μ = μ}
  convergence
  c
  c-inBall =
  powerSeriesSumOnBall-center-path
    convergence
    (centeredDisplacement-center c)
    (InPowerSeriesBall.displacementBound c-inBall)
    (bounded-byᶜ-zero ρ) ∙
  powerSeriesSumOnBall-zero
    convergence
    (bounded-byᶜ-zero ρ)


centeredPowerSeriesSumEverywhere-center :
  {a : PowerSeries} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (c : ℝᶜ) →
  centeredPowerSeriesSumEverywhere a c radiusData c ≡
  a zero
centeredPowerSeriesSumEverywhere-center
  {a = a}
  radiusData
  c =
  centeredPowerSeriesSumEverywhere-bound-path
    a
    c
    radiusData
    1⁺
    c
    c-inBall ∙
  centeredPowerSeriesSumOnBall-center
    (radiusData 1⁺ .snd)
    c
    c-inBall
  where
  c-inBall : InPowerSeriesBall c 1⁺ c
  c-inBall =
    record
      { displacementBound =
          subst
            (BoundedByᶜ 1⁺)
            (sym (centeredDisplacement-center c))
            (bounded-byᶜ-zero 1⁺)
      }


negPowerSeriesOnBallWith :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesOnBallWith a ρ μ →
  HasPowerSeriesOnBallWith (negPowerSeries a) ρ μ
negPowerSeriesOnBallWith {a = a} {μ = μ} convergence =
  hasPowerSeriesOnBallWith
    (HasPowerSeriesOnBallWith.antitoneModulus convergence)
    (λ h h-bound →
      subst
        (λ u → TailBound u μ)
        (sym (funExt (negPowerSeriesTerm a h)))
        (tailBound-neg
          (HasPowerSeriesOnBallWith.tailBound convergence h h-bound)))


negPowerSeriesOnBall :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBall a ρ →
  HasPowerSeriesOnBall (negPowerSeries a) ρ
negPowerSeriesOnBall (μ , convergence) =
  μ , negPowerSeriesOnBallWith convergence


powerSeriesSumOnBall-neg :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    (negPowerSeries a)
    ρ
    μ
    (negPowerSeriesOnBallWith convergence)
    h
    h-bound
  ≡
  -ᶜ powerSeriesSumOnBall a ρ μ convergence h h-bound
powerSeriesSumOnBall-neg
  {a = a}
  {ρ = ρ}
  {μ = μ}
  convergence
  h
  h-bound =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    leftSum
    rightSum
    (λ ε →
      subst
        (λ κ → MetricSpace.Close CauchyRealsMetricSpace leftSum κ rightSum)
        (half⁺+half⁺≡ ε)
        (MetricSpace.close-triangle
          CauchyRealsMetricSpace
          (leftTail ε)
          (MetricSpace.close-sym CauchyRealsMetricSpace (rightTail ε))))
  where
  negConvergence :
    HasPowerSeriesOnBallWith (negPowerSeries a) ρ μ
  negConvergence =
    negPowerSeriesOnBallWith convergence

  approximationIndex :
    ℚ⁺ →
    ℕ
  approximationIndex ε =
    μ (quarter⁺ (half⁺ (half⁺ ε)))

  leftSum : ℝᶜ
  leftSum =
    powerSeriesSumOnBall
      (negPowerSeries a)
      ρ
      μ
      negConvergence
      h
      h-bound

  rightSum : ℝᶜ
  rightSum =
    -ᶜ powerSeriesSumOnBall a ρ μ convergence h h-bound

  leftTail :
    (ε : ℚ⁺) →
    MetricSpace.Close CauchyRealsMetricSpace
      leftSum
      (half⁺ ε)
      (-ᶜ powerSeriesPartialSum a h (approximationIndex ε))
  leftTail ε =
    subst
      (λ partial →
        MetricSpace.Close CauchyRealsMetricSpace
          leftSum
          (half⁺ ε)
          partial)
      (powerSeriesPartialSum-neg a h (approximationIndex ε))
      (seriesSumFromFiniteTailBoundConvergesAt
        (powerSeriesTerm (negPowerSeries a) h)
        μ
        (HasPowerSeriesOnBallWith.tailBound
          negConvergence
          h
          h-bound)
        (HasPowerSeriesOnBallWith.antitoneModulus negConvergence)
        (half⁺ ε)
        (approximationIndex ε)
        NatOrder.≤-refl)

  rightTail :
    (ε : ℚ⁺) →
    MetricSpace.Close CauchyRealsMetricSpace
      rightSum
      (half⁺ ε)
      (-ᶜ powerSeriesPartialSum a h (approximationIndex ε))
  rightTail ε =
    neg-close
      (seriesSumFromFiniteTailBoundConvergesAt
        (powerSeriesTerm a h)
        μ
        (HasPowerSeriesOnBallWith.tailBound
          convergence
          h
          h-bound)
        (HasPowerSeriesOnBallWith.antitoneModulus convergence)
        (half⁺ ε)
        (approximationIndex ε)
        NatOrder.≤-refl)


powerSeriesSumOnBallFrom-neg :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  (convergence : HasPowerSeriesOnBall a ρ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBallFrom
    (negPowerSeries a)
    ρ
    (negPowerSeriesOnBall convergence)
    h
    h-bound
  ≡
  -ᶜ powerSeriesSumOnBallFrom a ρ convergence h h-bound
powerSeriesSumOnBallFrom-neg (μ , convergence) h h-bound =
  powerSeriesSumOnBall-neg convergence h h-bound
