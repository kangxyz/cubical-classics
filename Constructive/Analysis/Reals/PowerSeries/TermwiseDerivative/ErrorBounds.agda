{-

Part of Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.ErrorBounds where

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
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Index
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Finite
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Rules
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.PartialSums
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.IteratedBounds

PowerSeriesTermwiseCenterErrorBoundWith :
  (ℝᶜ → ℝᶜ) →
  PowerSeries →
  ℝᶜ →
  TermwiseDerivativeIndex →
  PrecisionModulus →
  Type₀
PowerSeriesTermwiseCenterErrorBoundWith f a x χ μ =
  (ε η : ℚ⁺) →
  radius η ℚOrder.≤ radius (μ ε) →
  (h : ℝᶜ) →
  BoundedByᶜ η h →
  BoundedByᶜ
    (quarter⁺ (ε *⁺ η))
    (powerSeriesTermwiseCenterError f a x χ ε η)


PowerSeriesTermwiseDerivativeLinearErrorBoundWith :
  PowerSeries →
  ℝᶜ →
  ℝᶜ →
  TermwiseDerivativeIndex →
  PrecisionModulus →
  Type₀
PowerSeriesTermwiseDerivativeLinearErrorBoundWith da x d χ μ =
  (ε η : ℚ⁺) →
  radius η ℚOrder.≤ radius (μ ε) →
  (h : ℝᶜ) →
  BoundedByᶜ η h →
  BoundedByᶜ
    (quarter⁺ (ε *⁺ η))
    (powerSeriesTermwiseDerivativeLinearError da x d χ ε η h)


PowerSeriesTermwiseDerivativeValueErrorBoundWith :
  PowerSeries →
  ℝᶜ →
  ℝᶜ →
  TermwiseDerivativeIndex →
  PrecisionModulus →
  Type₀
PowerSeriesTermwiseDerivativeValueErrorBoundWith da x d χ μ =
  (ε η : ℚ⁺) →
  radius η ℚOrder.≤ radius (μ ε) →
  (h : ℝᶜ) →
  BoundedByᶜ η h →
  BoundedByᶜ
    (quarter⁺ ε)
    (d +ᶜ (-ᶜ powerSeriesPartialSum da x (χ ε η)))


PowerSeriesFormalDerivativeValueErrorBoundWith :
  PowerSeries →
  ℝᶜ →
  ℝᶜ →
  TermwiseDerivativeIndex →
  PrecisionModulus →
  Type₀
PowerSeriesFormalDerivativeValueErrorBoundWith a =
  PowerSeriesTermwiseDerivativeValueErrorBoundWith (derivativePowerSeries a)


powerSeriesTermwiseForwardErrorBoundFromConvergence :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {x : ℝᶜ} →
  {ρ : ℚ⁺} →
  {ν : ℚ⁺ → ℕ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  (convergence : HasPowerSeriesOnBallWith a ρ ν) →
  (forwardInBall :
    (ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (μ ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    BoundedByᶜ ρ (x +ᶜ h)) →
  ((ε η : ℚ⁺) →
    (η≤με : radius η ℚOrder.≤ radius (μ ε)) →
    (h : ℝᶜ) →
    (h-bound : BoundedByᶜ η h) →
    f (x +ᶜ h) ≡
    powerSeriesSumOnBall
      a
      ρ
      ν
      convergence
      (x +ᶜ h)
      (forwardInBall ε η η≤με h h-bound)) →
  PowerSeriesTermwiseSumBoundIndexLarge ν χ →
  PowerSeriesTermwiseForwardErrorBoundWith f a x χ μ
powerSeriesTermwiseForwardErrorBoundFromConvergence
  {f = f}
  {a = a}
  {x = x}
  {ρ = ρ}
  {ν = ν}
  {χ = χ}
  convergence
  forwardInBall
  expansion
  index-large
  ε
  η
  η≤με
  h
  h-bound =
  subst
    (λ z →
      BoundedByᶜ
        piecePrecision
        (z +ᶜ (-ᶜ powerSeriesPartialSum a (x +ᶜ h) (suc n))))
    (sym (expansion ε η η≤με h h-bound))
    sumErrorBound
  where
  piecePrecision : ℚ⁺
  piecePrecision =
    quarter⁺ (ε *⁺ η)

  n : ℕ
  n =
    χ ε η

  y-bound : BoundedByᶜ ρ (x +ᶜ h)
  y-bound =
    forwardInBall ε η η≤με h h-bound

  sumErrorBound :
    BoundedByᶜ
      piecePrecision
      (powerSeriesSumOnBall a ρ ν convergence (x +ᶜ h) y-bound +ᶜ
        (-ᶜ powerSeriesPartialSum a (x +ᶜ h) (suc n)))
  sumErrorBound =
    powerSeriesApproximationForwardErrorBoundFromConvergence
      convergence
      piecePrecision
      (x +ᶜ h)
      y-bound
      (suc n)
      (NatOrder.≤-trans (index-large ε η) (n≤sucn n))


powerSeriesTermwiseCenterErrorBoundFromConvergence :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {x : ℝᶜ} →
  {ρ : ℚ⁺} →
  {ν : ℚ⁺ → ℕ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  (convergence : HasPowerSeriesOnBallWith a ρ ν) →
  (x-bound : BoundedByᶜ ρ x) →
  f x ≡ powerSeriesSumOnBall a ρ ν convergence x x-bound →
  PowerSeriesTermwiseSumBoundIndexLarge ν χ →
  PowerSeriesTermwiseCenterErrorBoundWith f a x χ μ
powerSeriesTermwiseCenterErrorBoundFromConvergence
  {f = f}
  {a = a}
  {x = x}
  {ρ = ρ}
  {ν = ν}
  {χ = χ}
  convergence
  x-bound
  expansion
  index-large
  ε
  η
  _
  h
  _ =
  subst
    (λ z →
      BoundedByᶜ
        piecePrecision
        (powerSeriesPartialSum a x (suc n) +ᶜ (-ᶜ z)))
    (sym expansion)
    reverseErrorBound
  where
  piecePrecision : ℚ⁺
  piecePrecision =
    quarter⁺ (ε *⁺ η)

  n : ℕ
  n =
    χ ε η

  reverseErrorBound :
    BoundedByᶜ
      piecePrecision
      (powerSeriesPartialSum a x (suc n) +ᶜ
        (-ᶜ powerSeriesSumOnBall a ρ ν convergence x x-bound))
  reverseErrorBound =
    powerSeriesApproximationReverseErrorBoundFromConvergence
      convergence
      piecePrecision
      x
      x-bound
      (suc n)
      (NatOrder.≤-trans (index-large ε η) (n≤sucn n))


powerSeriesTermwiseDerivativeValueErrorBoundFromConvergence :
  {da : PowerSeries} →
  {x d : ℝᶜ} →
  {ρ : ℚ⁺} →
  {ν : ℚ⁺ → ℕ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  (convergence : HasPowerSeriesOnBallWith da ρ ν) →
  (x-bound : BoundedByᶜ ρ x) →
  d ≡ powerSeriesSumOnBall da ρ ν convergence x x-bound →
  PowerSeriesTermwiseDerivativeValueIndexLarge ν χ →
  PowerSeriesTermwiseDerivativeValueErrorBoundWith da x d χ μ
powerSeriesTermwiseDerivativeValueErrorBoundFromConvergence
  {da = da}
  {x = x}
  {d = d}
  {ρ = ρ}
  {ν = ν}
  {χ = χ}
  convergence
  x-bound
  valuePath
  index-large
  ε
  η
  _
  h
  _ =
  subst
    (λ z →
      BoundedByᶜ
        piecePrecision
        (z +ᶜ (-ᶜ powerSeriesPartialSum da x n)))
    (sym valuePath)
    sumErrorBound
  where
  piecePrecision : ℚ⁺
  piecePrecision =
    quarter⁺ ε

  n : ℕ
  n =
    χ ε η

  sumErrorBound :
    BoundedByᶜ
      piecePrecision
      (powerSeriesSumOnBall da ρ ν convergence x x-bound +ᶜ
        (-ᶜ powerSeriesPartialSum da x n))
  sumErrorBound =
    powerSeriesApproximationForwardErrorBoundFromConvergence
      convergence
      piecePrecision
      x
      x-bound
      n
      (index-large ε η)


powerSeriesFormalDerivativeValueErrorBoundFromConvergence :
  {a : PowerSeries} →
  {x d : ℝᶜ} →
  {ρ : ℚ⁺} →
  {ν : ℚ⁺ → ℕ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  (convergence : HasPowerSeriesOnBallWith (derivativePowerSeries a) ρ ν) →
  (x-bound : BoundedByᶜ ρ x) →
  d ≡
  powerSeriesSumOnBall
    (derivativePowerSeries a)
    ρ
    ν
    convergence
    x
    x-bound →
  PowerSeriesTermwiseDerivativeValueIndexLarge ν χ →
  PowerSeriesFormalDerivativeValueErrorBoundWith a x d χ μ
powerSeriesFormalDerivativeValueErrorBoundFromConvergence =
  powerSeriesTermwiseDerivativeValueErrorBoundFromConvergence


derivativeValueErrorBound→linearErrorBound :
  {da : PowerSeries} →
  {x d : ℝᶜ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  PowerSeriesTermwiseDerivativeValueErrorBoundWith da x d χ μ →
  PowerSeriesTermwiseDerivativeLinearErrorBoundWith da x d χ μ
derivativeValueErrorBound→linearErrorBound
  {da = da}
  {x = x}
  {d = d}
  {χ = χ}
  derivativeValueBound
  ε
  η
  η≤με
  h
  h-bound =
  subst
    (λ κ →
      BoundedByᶜ
        κ
        (powerSeriesTermwiseDerivativeLinearError da x d χ ε η h))
    (quarter-product≡ ε η)
    (bounded-byᶜ-neg
      (quarter⁺ ε *⁺ η)
      (derivativeErrorTerm ·ᶜ h)
      (bounded-byᶜ-mul
        (quarter⁺ ε)
        η
        derivativeErrorTerm
        h
        derivativeErrorBound
        h-bound))
  where
  derivativeErrorTerm : ℝᶜ
  derivativeErrorTerm =
    d +ᶜ (-ᶜ powerSeriesPartialSum da x (χ ε η))

  derivativeErrorBound :
    BoundedByᶜ (quarter⁺ ε) derivativeErrorTerm
  derivativeErrorBound =
    derivativeValueBound ε η η≤με h h-bound


abstract
  powerSeriesTermwisePieceBounds→decomposedRemainderBound :
    {f : ℝᶜ → ℝᶜ} →
    {a da : PowerSeries} →
    {x d : ℝᶜ} →
    {χ : TermwiseDerivativeIndex} →
    {μ : PrecisionModulus} →
    PowerSeriesTermwiseForwardErrorBoundWith f a x χ μ →
    PowerSeriesPartialDerivativeRemainderBoundWith a da x χ μ →
    PowerSeriesTermwiseCenterErrorBoundWith f a x χ μ →
    PowerSeriesTermwiseDerivativeLinearErrorBoundWith da x d χ μ →
    (ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (μ ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    BoundedByᶜ
      (ε *⁺ η)
      (powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h)
  powerSeriesTermwisePieceBounds→decomposedRemainderBound
    {f = f}
    {a = a}
    {da = da}
    {x = x}
    {d = d}
    {χ = χ}
    forwardBoundWith
    partialBoundWith
    centerBoundWith
    derivativeLinearBoundWith
    ε
    η
    η≤με
    h
    h-bound =
    subst
      (λ κ →
        BoundedByᶜ
          κ
          (powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h))
      (four-quarters≡ (ε *⁺ η))
      combinedBound
    where
    piecePrecision : ℚ⁺
    piecePrecision =
      quarter⁺ (ε *⁺ η)

    forwardTerm : ℝᶜ
    forwardTerm =
      powerSeriesTermwiseForwardError f a x χ ε η h

    partialTerm : ℝᶜ
    partialTerm =
      powerSeriesTermwisePartialRemainder a da x χ ε η h

    centerTerm : ℝᶜ
    centerTerm =
      powerSeriesTermwiseCenterError f a x χ ε η

    derivativeLinearTerm : ℝᶜ
    derivativeLinearTerm =
      powerSeriesTermwiseDerivativeLinearError da x d χ ε η h

    forwardBound :
      BoundedByᶜ piecePrecision forwardTerm
    forwardBound =
      forwardBoundWith ε η η≤με h h-bound

    partialBound :
      BoundedByᶜ piecePrecision partialTerm
    partialBound =
      partialBoundWith ε η η≤με h h-bound

    centerBound :
      BoundedByᶜ piecePrecision centerTerm
    centerBound =
      centerBoundWith ε η η≤με h h-bound

    derivativeLinearBound :
      BoundedByᶜ piecePrecision derivativeLinearTerm
    derivativeLinearBound =
      derivativeLinearBoundWith ε η η≤με h h-bound

    firstTwoBound :
      BoundedByᶜ
        (piecePrecision +⁺ piecePrecision)
        (forwardTerm +ᶜ partialTerm)
    firstTwoBound =
      bounded-byᶜ-add
        piecePrecision
        piecePrecision
        forwardTerm
        partialTerm
        forwardBound
        partialBound

    firstThreeBound :
      BoundedByᶜ
        ((piecePrecision +⁺ piecePrecision) +⁺ piecePrecision)
        ((forwardTerm +ᶜ partialTerm) +ᶜ centerTerm)
    firstThreeBound =
      bounded-byᶜ-add
        (piecePrecision +⁺ piecePrecision)
        piecePrecision
        (forwardTerm +ᶜ partialTerm)
        centerTerm
        firstTwoBound
        centerBound

    combinedBound :
      BoundedByᶜ
        (((piecePrecision +⁺ piecePrecision) +⁺ piecePrecision) +⁺
          piecePrecision)
        (powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h)
    combinedBound =
      bounded-byᶜ-add
        ((piecePrecision +⁺ piecePrecision) +⁺ piecePrecision)
        piecePrecision
        ((forwardTerm +ᶜ partialTerm) +ᶜ centerTerm)
        derivativeLinearTerm
        firstThreeBound
        derivativeLinearBound
