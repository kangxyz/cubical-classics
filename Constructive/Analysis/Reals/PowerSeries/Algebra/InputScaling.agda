{-

Scaling the input of a power series

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Algebra.InputScaling where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Metric
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.CommRing
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.Series
  using
    ( TailBound
    ; partialSum
    ; seriesSumFromFiniteTailBoundConvergesAt
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower)
open import Constructive.Data.PositiveRationals


private
  module SolverHelpers {ℓ : Level} (𝒩 : CommRing ℓ) where
    open CommRingStr (𝒩 .snd)

    power-step :
      (r h pr ph : 𝒩 .fst) →
      (r · h) · (pr · ph) ≡ (r · pr) · (h · ph)
    power-step _ _ _ _ =
      solve! 𝒩

    term-path :
      (a pr ph : 𝒩 .fst) →
      (a · pr) · ph ≡ a · (pr · ph)
    term-path _ _ _ =
      solve! 𝒩


inputScalePowerSeries :
  ℝᶜ →
  PowerSeries →
  PowerSeries
inputScalePowerSeries r a n =
  a n ·ᶜ realPower r n


realPower-mul :
  (r h : ℝᶜ) →
  (n : ℕ) →
  realPower (r ·ᶜ h) n ≡
  realPower r n ·ᶜ realPower h n
realPower-mul r h zero =
  sym (mulᶜ-one-left 1ᶜ)
realPower-mul r h (suc n) =
  cong ((r ·ᶜ h) ·ᶜ_) (realPower-mul r h n) ∙
  SolverHelpers.power-step
    CauchyRealsCommRing
    r
    h
    (realPower r n)
    (realPower h n)


inputScalePowerSeriesTerm :
  (r : ℝᶜ) →
  (a : PowerSeries) →
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesTerm (inputScalePowerSeries r a) h n ≡
  powerSeriesTerm a (r ·ᶜ h) n
inputScalePowerSeriesTerm r a h n =
  SolverHelpers.term-path
    CauchyRealsCommRing
    (a n)
    (realPower r n)
    (realPower h n) ∙
  cong (a n ·ᶜ_) (sym (realPower-mul r h n))


inputScalePowerSeriesOnBallWith :
  (r : ℝᶜ) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ r →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesOnBallWith a (ρ *⁺ κ) μ →
  HasPowerSeriesOnBallWith
    (inputScalePowerSeries r a)
    ρ
    μ
inputScalePowerSeriesOnBallWith
    r
    κ
    r-bound
    {a = a}
    {ρ = ρ}
    {μ = μ}
    convergence =
  hasPowerSeriesOnBallWith
    (HasPowerSeriesOnBallWith.antitoneModulus convergence)
    (λ h h-bound →
      subst
        (λ u → TailBound u μ)
        (sym (funExt (inputScalePowerSeriesTerm r a h)))
        (HasPowerSeriesOnBallWith.tailBound
          convergence
          (r ·ᶜ h)
          (subst
            (λ θ → BoundedByᶜ θ (r ·ᶜ h))
            (*⁺-comm κ ρ)
            (bounded-byᶜ-mul κ ρ r h r-bound h-bound))))


powerSeriesPartialSum-inputScale :
  (r : ℝᶜ) →
  (a : PowerSeries) →
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesPartialSum (inputScalePowerSeries r a) h n ≡
  powerSeriesPartialSum a (r ·ᶜ h) n
powerSeriesPartialSum-inputScale r a h n =
  cong
    (λ u → partialSum u n)
    (funExt (inputScalePowerSeriesTerm r a h))


powerSeriesSumOnBall-inputScale :
  (r : ℝᶜ) →
  (κ : ℚ⁺) →
  (r-bound : BoundedByᶜ κ r) →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a (ρ *⁺ κ) μ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    (inputScalePowerSeries r a)
    ρ
    μ
    (inputScalePowerSeriesOnBallWith r κ r-bound convergence)
    h
    h-bound
  ≡
  powerSeriesSumOnBall
    a
    (ρ *⁺ κ)
    μ
    convergence
    (r ·ᶜ h)
    (subst
      (λ θ → BoundedByᶜ θ (r ·ᶜ h))
      (*⁺-comm κ ρ)
      (bounded-byᶜ-mul κ ρ r h r-bound h-bound))
powerSeriesSumOnBall-inputScale
    r
    κ
    r-bound
    {a = a}
    {ρ = ρ}
    {μ = μ}
    convergence
    h
    h-bound =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    scaledSum
    sourceSum
    closeAt
  where
  scaledConvergence =
    inputScalePowerSeriesOnBallWith r κ r-bound convergence

  rh-bound : BoundedByᶜ (ρ *⁺ κ) (r ·ᶜ h)
  rh-bound =
    subst
      (λ θ → BoundedByᶜ θ (r ·ᶜ h))
      (*⁺-comm κ ρ)
      (bounded-byᶜ-mul κ ρ r h r-bound h-bound)

  scaledSum : ℝᶜ
  scaledSum =
    powerSeriesSumOnBall
      (inputScalePowerSeries r a)
      ρ
      μ
      scaledConvergence
      h
      h-bound

  sourceSum : ℝᶜ
  sourceSum =
    powerSeriesSumOnBall a (ρ *⁺ κ) μ convergence (r ·ᶜ h) rh-bound

  approximationIndex : ℚ⁺ → ℕ
  approximationIndex ε =
    μ (quarter⁺ (half⁺ (half⁺ ε)))

  scaledTail :
    (ε : ℚ⁺) →
    scaledSum ∼[ half⁺ ε ]
    powerSeriesPartialSum
      (inputScalePowerSeries r a)
      h
      (approximationIndex ε)
  scaledTail ε =
    seriesSumFromFiniteTailBoundConvergesAt
      (powerSeriesTerm (inputScalePowerSeries r a) h)
      μ
      (HasPowerSeriesOnBallWith.tailBound scaledConvergence h h-bound)
      (HasPowerSeriesOnBallWith.antitoneModulus scaledConvergence)
      (half⁺ ε)
      (approximationIndex ε)
      NatOrder.≤-refl

  sourceTail :
    (ε : ℚ⁺) →
    sourceSum ∼[ half⁺ ε ]
    powerSeriesPartialSum a (r ·ᶜ h) (approximationIndex ε)
  sourceTail ε =
    seriesSumFromFiniteTailBoundConvergesAt
      (powerSeriesTerm a (r ·ᶜ h))
      μ
      (HasPowerSeriesOnBallWith.tailBound convergence (r ·ᶜ h) rh-bound)
      (HasPowerSeriesOnBallWith.antitoneModulus convergence)
      (half⁺ ε)
      (approximationIndex ε)
      NatOrder.≤-refl

  closeAt :
    (ε : ℚ⁺) →
    scaledSum ∼[ ε ] sourceSum
  closeAt ε =
    subst
      (λ θ → scaledSum ∼[ θ ] sourceSum)
      (half⁺+half⁺≡ ε)
      (MetricSpace.close-triangle
        CauchyRealsMetricSpace
        (scaledTail ε)
        (MetricSpace.close-sym
          CauchyRealsMetricSpace
          (subst
            (λ partial → sourceSum ∼[ half⁺ ε ] partial)
            (sym
              (powerSeriesPartialSum-inputScale
                r a h (approximationIndex ε)))
            (sourceTail ε))))
