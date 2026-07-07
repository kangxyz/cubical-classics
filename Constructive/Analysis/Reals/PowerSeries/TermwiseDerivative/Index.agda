{-

Part of Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Index where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; max ; suc ; zero)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.Calculus.Derivative
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.CommRing
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base using (_≤ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.Series
  using
    ( partialSum
    ; partialSum-add
    ; seriesSumFromFiniteTailBoundConvergesAt
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower ; realPowerBoundsFromBound)
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
  using (positivePower)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( addPowerSeries
    ; addPowerSeriesTerm
    ; bounded-byᶜ-zero
    ; powerSeriesPartialSum-add
    ; powerSeriesPartialSum-shift
    ; shiftPowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.Analytic
  using
    ( HasPowerSeriesAtWith
    ; centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using
    ( derivativePowerSeries
    ; derivativePrimitivePowerSeries
    ; naturalReal
    ; primitivePowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence
  using (derivativePrimitivePowerSeriesInfiniteRadius)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open ClosenessOf RationalsMetricSpace

open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Internal

TermwiseDerivativeIndex : Type₀
TermwiseDerivativeIndex =
  ℚ⁺ → ℚ⁺ → ℕ


powerSeriesTermwiseBoundIndex :
  (ℚ⁺ → ℕ) →
  ℚ⁺ →
  ℕ
powerSeriesTermwiseBoundIndex ν θ =
  ν (quarter⁺ (half⁺ (half⁺ θ)))


PowerSeriesTermwiseSumBoundIndexLarge :
  (ℚ⁺ → ℕ) →
  TermwiseDerivativeIndex →
  Type₀
PowerSeriesTermwiseSumBoundIndexLarge ν χ =
  (ε η : ℚ⁺) →
  NatOrder._≤_
    (powerSeriesTermwiseBoundIndex ν (quarter⁺ (ε *⁺ η)))
    (χ ε η)


PowerSeriesTermwiseDerivativeValueIndexLarge :
  (ℚ⁺ → ℕ) →
  TermwiseDerivativeIndex →
  Type₀
PowerSeriesTermwiseDerivativeValueIndexLarge ν χ =
  (ε η : ℚ⁺) →
  NatOrder._≤_
    (powerSeriesTermwiseBoundIndex ν (quarter⁺ ε))
    (χ ε η)


termwiseConvergenceIndex :
  (ℚ⁺ → ℕ) →
  (ℚ⁺ → ℕ) →
  TermwiseDerivativeIndex
termwiseConvergenceIndex ν τ ε η =
  max
    (powerSeriesTermwiseBoundIndex ν (quarter⁺ (ε *⁺ η)))
    (powerSeriesTermwiseBoundIndex τ (quarter⁺ ε))


termwiseConvergenceIndex-sumLarge :
  {ν τ : ℚ⁺ → ℕ} →
  PowerSeriesTermwiseSumBoundIndexLarge
    ν
    (termwiseConvergenceIndex ν τ)
termwiseConvergenceIndex-sumLarge {ν = ν} {τ = τ} ε η =
  NatOrder.left-≤-max
    {m = powerSeriesTermwiseBoundIndex ν (quarter⁺ (ε *⁺ η))}
    {n = powerSeriesTermwiseBoundIndex τ (quarter⁺ ε)}


termwiseConvergenceIndex-derivativeValueLarge :
  {ν τ : ℚ⁺ → ℕ} →
  PowerSeriesTermwiseDerivativeValueIndexLarge
    τ
    (termwiseConvergenceIndex ν τ)
termwiseConvergenceIndex-derivativeValueLarge {ν = ν} {τ = τ} ε η =
  NatOrder.right-≤-max
    {n = powerSeriesTermwiseBoundIndex τ (quarter⁺ ε)}
    {m = powerSeriesTermwiseBoundIndex ν (quarter⁺ (ε *⁺ η))}


powerSeriesForwardInBallFromCenterMargin :
  {x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  BoundedByᶜ σ x →
  ((ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  (ε η : ℚ⁺) →
  radius η ℚOrder.≤ radius (μ ε) →
  (h : ℝᶜ) →
  BoundedByᶜ η h →
  BoundedByᶜ ρ (x +ᶜ h)
powerSeriesForwardInBallFromCenterMargin
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  x-bound
  margin
  ε
  η
  η≤με
  h
  h-bound =
  bounded-byᶜ-monotone
    σ+η≤ρ
    (bounded-byᶜ-add σ η x h x-bound h-bound)
  where
  η+σ≤με+σ :
    radius η ℚ.+ radius σ ℚOrder.≤
    radius (μ ε) ℚ.+ radius σ
  η+σ≤με+σ =
    ℚOrder.≤-+o
      (radius η)
      (radius (μ ε))
      (radius σ)
      η≤με

  σ+η≤σ+με :
    radius (σ +⁺ η) ℚOrder.≤ radius (σ +⁺ μ ε)
  σ+η≤σ+με =
    subst2
      ℚOrder._≤_
      (ℚ.+Comm (radius η) (radius σ))
      (ℚ.+Comm (radius (μ ε)) (radius σ))
      η+σ≤με+σ

  σ+η≤ρ :
    radius (σ +⁺ η) ℚOrder.≤ radius ρ
  σ+η≤ρ =
    Rational.≤-trans
      {p = radius (σ +⁺ η)}
      {q = radius (σ +⁺ μ ε)}
      {r = radius ρ}
      σ+η≤σ+με
      (margin ε)


powerSeriesCenterInBallFromMargin :
  {x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  BoundedByᶜ σ x →
  ((ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  BoundedByᶜ ρ x
powerSeriesCenterInBallFromMargin
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  x-bound
  margin =
  bounded-byᶜ-monotone
    σ≤ρ
    x-bound
  where
  σ≤ρ : radius σ ℚOrder.≤ radius ρ
  σ≤ρ =
    Rational.≤-trans
      {p = radius σ}
      {q = radius (σ +⁺ μ 1⁺)}
      {r = radius ρ}
      (summand-left≤sum σ (μ 1⁺))
      (margin 1⁺)


powerSeriesApproximationForwardErrorBoundFromConvergence :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {ν : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a ρ ν) →
  (θ : ℚ⁺) →
  (y : ℝᶜ) →
  (y-bound : BoundedByᶜ ρ y) →
  (n : ℕ) →
  NatOrder._≤_ (powerSeriesTermwiseBoundIndex ν θ) n →
  BoundedByᶜ
    θ
    (powerSeriesSumOnBall a ρ ν convergence y y-bound +ᶜ
      (-ᶜ powerSeriesPartialSum a y n))
powerSeriesApproximationForwardErrorBoundFromConvergence
  {a = a}
  {ρ = ρ}
  {ν = ν}
  convergence
  θ
  y
  y-bound
  n
  index-large =
  close→difference-bounded-byᶜ
    (powerSeriesSumOnBall a ρ ν convergence y y-bound)
    (powerSeriesPartialSum a y n)
    (half< θ)
    sum∼partial
  where
  sum∼partial :
    powerSeriesSumOnBall a ρ ν convergence y y-bound
    ∼[ half⁺ θ ]
    powerSeriesPartialSum a y n
  sum∼partial =
    seriesSumFromFiniteTailBoundConvergesAt
      (powerSeriesTerm a y)
      ν
      (HasPowerSeriesOnBallWith.tailBound convergence y y-bound)
      (HasPowerSeriesOnBallWith.antitoneModulus convergence)
      (half⁺ θ)
      n
      index-large


powerSeriesApproximationReverseErrorBoundFromConvergence :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {ν : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a ρ ν) →
  (θ : ℚ⁺) →
  (y : ℝᶜ) →
  (y-bound : BoundedByᶜ ρ y) →
  (n : ℕ) →
  NatOrder._≤_ (powerSeriesTermwiseBoundIndex ν θ) n →
  BoundedByᶜ
    θ
    (powerSeriesPartialSum a y n +ᶜ
      (-ᶜ powerSeriesSumOnBall a ρ ν convergence y y-bound))
powerSeriesApproximationReverseErrorBoundFromConvergence
  {a = a}
  {ρ = ρ}
  {ν = ν}
  convergence
  θ
  y
  y-bound
  n
  index-large =
  close→difference-bounded-byᶜ
    (powerSeriesPartialSum a y n)
    (powerSeriesSumOnBall a ρ ν convergence y y-bound)
    (half< θ)
    (close-sym sum∼partial)
  where
  sum∼partial :
    powerSeriesSumOnBall a ρ ν convergence y y-bound
    ∼[ half⁺ θ ]
    powerSeriesPartialSum a y n
  sum∼partial =
    seriesSumFromFiniteTailBoundConvergesAt
      (powerSeriesTerm a y)
      ν
      (HasPowerSeriesOnBallWith.tailBound convergence y y-bound)
      (HasPowerSeriesOnBallWith.antitoneModulus convergence)
      (half⁺ θ)
      n
      index-large
