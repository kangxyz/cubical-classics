{-

Second-derivative estimates with an explicit segment margin

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Calculus.SecondOrderLocal where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax)

open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.DerivativeData
open import Constructive.Analysis.Reals.Calculus.SegmentEstimates
open import Constructive.Analysis.Reals.Calculus.SecondOrderRemainder
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational
import Constructive.Data.Rationals.Archimedean as RationalArch


boundedSecondDerivativeMarginModulus :
  ℚ⁺ →
  ℚ⁺ →
  PrecisionModulus
boundedSecondDerivativeMarginModulus ζ Γ ε =
  min⁺
    ζ
    (min⁺ 1⁺ (posInv⁺ (Γ +⁺ 1⁺) *⁺ quarter⁺ ε))


private
  segmentPointBoundMargin :
    (σ ζ η : ℚ⁺) →
    (x h : ℝᶜ) →
    BoundedByᶜ σ x →
    BoundedByᶜ η h →
    radius η ℚOrder.≤ radius ζ →
    (q : ℚ) →
    Rational.0ℚ ℚOrder.≤ q →
    q ℚOrder.≤ Rational.1ℚ →
    BoundedByᶜ (σ +⁺ ζ) (segmentPoint x h q)
  segmentPointBoundMargin σ ζ η x h x-bound h-bound η≤ζ q 0≤q q≤1 =
    bounded-byᶜ-monotone
      (ℚOrder.≤Monotone+
        (radius σ)
        (radius σ)
        (radius η)
        (radius ζ)
        (Rational.≤-refl (radius σ))
        η≤ζ)
      (segmentPointBound σ η x h x-bound h-bound q 0≤q q≤1)

  unitFractionGridPointBoundMargin :
    (σ ζ η : ℚ⁺) →
    (x h : ℝᶜ) →
    BoundedByᶜ σ x →
    BoundedByᶜ η h →
    radius η ℚOrder.≤ radius ζ →
    (n k : ℕ) →
    NatOrder._≤_ k (suc n) →
    BoundedByᶜ
      (σ +⁺ ζ)
      (gridPointFrom
        x
        (scalarMulᶜ (RationalArch.unitFraction n) h)
        k)
  unitFractionGridPointBoundMargin
    σ ζ η x h x-bound h-bound η≤ζ n k k≤sucn =
    subst
      (BoundedByᶜ (σ +⁺ ζ))
      (sym
        (gridPointFrom-scalarMul
          x
          h
          (RationalArch.unitFraction n)
          k))
      (segmentPointBoundMargin
        σ
        ζ
        η
        x
        h
        x-bound
        h-bound
        η≤ζ
        (RationalArch.natMul k (RationalArch.unitFraction n))
        (natMul-unitFraction-nonnegative n k)
        (natMul-unitFraction≤1 n k k≤sucn))

  boundedSecondDerivativeLinearRemainderMarginSubdivision :
    {f g dg : ℝᶜ → ℝᶜ} →
    {μ ν : PrecisionModulus} →
    (σ ζ Γ α β η : ℚ⁺) →
    HasDerivativeOnBallWith f g (σ +⁺ ζ) μ →
    HasDerivativeOnBallWith g dg (σ +⁺ ζ) ν →
    BoundedOnBallWith dg (σ +⁺ ζ) Γ →
    (x h : ℝᶜ) →
    BoundedByᶜ σ x →
    BoundedByᶜ η h →
    radius η ℚOrder.≤ radius ζ →
    (n : ℕ) →
    radius (unitFraction⁺ n *⁺ η) ℚOrder.≤ radius (μ α) →
    radius (unitFraction⁺ n *⁺ η) ℚOrder.≤ radius (ν β) →
    BoundedByᶜ
      (linearSubdivisionBound
        (α *⁺ (unitFraction⁺ n *⁺ η))
        (((Γ *⁺ (unitFraction⁺ n *⁺ η)) +⁺
          (β *⁺ (unitFraction⁺ n *⁺ η))) *⁺ η)
        (suc n))
      (linearRemainder f x (g x) h)
  boundedSecondDerivativeLinearRemainderMarginSubdivision
    {f = f}
    {g = g}
    {dg = dg}
    {μ = μ}
    {ν = ν}
    σ
    ζ
    Γ
    α
    β
    η
    firstDerivative
    secondDerivative
    secondBound
    x
    h
    x-bound
    h-bound
    η≤ζ
    n
    δ≤μα
    δ≤νβ =
    subst
      (λ z →
        BoundedByᶜ
          (linearSubdivisionBound
            (α *⁺ δ)
            (((Γ *⁺ δ) +⁺ (β *⁺ δ)) *⁺ η)
            (suc n))
          (linearRemainder f x (g x) z))
      (gridDisplacement-unitFraction h n)
      subdivision
    where
    δ : ℚ⁺
    δ =
      unitFraction⁺ n *⁺ η

    step : ℝᶜ
    step =
      scalarMulᶜ (RationalArch.unitFraction n) h

    subdivision =
      boundedSecondDerivativeLinearRemainderSubdivision
        {f = f}
        {g = g}
        {dg = dg}
        {ρ = σ +⁺ ζ}
        {μ = μ}
        {ν = ν}
        Γ
        α
        β
        δ
        η
        firstDerivative
        secondDerivative
        secondBound
        step
        (unitFractionStepBound n h-bound)
        δ≤μα
        δ≤νβ
        (suc n)
        x
        (λ k k≤sucn →
          unitFractionGridPointBoundMargin
            σ ζ η x h x-bound h-bound η≤ζ n k k≤sucn)
        (λ k k≤sucn →
          unitFractionGridDisplacementBound n k k≤sucn h-bound)


boundedSecondDerivativeHasDerivativeAtWithFromSecondBoundOnMargin :
  {f g dg : ℝᶜ → ℝᶜ} →
  {μ ν : PrecisionModulus} →
  (σ ζ Γ : ℚ⁺) →
  HasDerivativeOnBallWith f g (σ +⁺ ζ) μ →
  HasDerivativeOnBallWith g dg (σ +⁺ ζ) ν →
  BoundedOnBallWith dg (σ +⁺ ζ) Γ →
  (x : ℝᶜ) →
  BoundedByᶜ σ x →
  HasDerivativeAtWith
    f
    x
    (g x)
    (boundedSecondDerivativeMarginModulus ζ Γ)
boundedSecondDerivativeHasDerivativeAtWithFromSecondBoundOnMargin
  {f = f}
  {g = g}
  {dg = dg}
  {μ = μ}
  {ν = ν}
  σ
  ζ
  Γ
  firstDerivative
  secondDerivative
  secondBound
  x
  x-bound
  ε
  η
  η≤canonical
  h
  h-bound =
  bounded-byᶜ-monotone total≤εη rawBound
  where
  α β : ℚ⁺
  α =
    quarter⁺ ε
  β =
    1⁺

  innerCanonical : ℚ⁺
  innerCanonical =
    min⁺ 1⁺ (posInv⁺ (Γ +⁺ 1⁺) *⁺ quarter⁺ ε)

  η≤ζ : radius η ℚOrder.≤ radius ζ
  η≤ζ =
    Rational.≤-trans
      {p = radius η}
      {q = radius (min⁺ ζ innerCanonical)}
      {r = radius ζ}
      η≤canonical
      (min⁺≤left ζ innerCanonical)

  η≤inner : radius η ℚOrder.≤ radius innerCanonical
  η≤inner =
    Rational.≤-trans
      {p = radius η}
      {q = radius (min⁺ ζ innerCanonical)}
      {r = radius innerCanonical}
      η≤canonical
      (min⁺≤right ζ innerCanonical)

  η≤1 : radius η ℚOrder.≤ Rational.1ℚ
  η≤1 =
    Rational.≤-trans
      {p = radius η}
      {q = radius innerCanonical}
      {r = Rational.1ℚ}
      η≤inner
      (min⁺≤left 1⁺ (posInv⁺ (Γ +⁺ 1⁺) *⁺ quarter⁺ ε))

  stepTarget : ℚ⁺
  stepTarget =
    min⁺ (μ α) (ν β)

  stepSearch :
    Σ[ n ∈ ℕ ] RationalArch.unitFraction n ℚOrder.< radius stepTarget
  stepSearch =
    RationalArch.archimedean-unit-fraction
      (radius stepTarget)
      (stepTarget .snd)

  n : ℕ
  n =
    stepSearch .fst

  δ≤target :
    radius (unitFraction⁺ n *⁺ η) ℚOrder.≤ radius stepTarget
  δ≤target =
    unitFractionTimes≤ n η stepTarget η≤1 (stepSearch .snd)

  δ≤μα : radius (unitFraction⁺ n *⁺ η) ℚOrder.≤ radius (μ α)
  δ≤μα =
    Rational.≤-trans δ≤target (min⁺≤left (μ α) (ν β))

  δ≤νβ : radius (unitFraction⁺ n *⁺ η) ℚOrder.≤ radius (ν β)
  δ≤νβ =
    Rational.≤-trans δ≤target (min⁺≤right (μ α) (ν β))

  rawBound =
    boundedSecondDerivativeLinearRemainderMarginSubdivision
      σ ζ Γ α β η
      firstDerivative
      secondDerivative
      secondBound
      x h x-bound h-bound η≤ζ n δ≤μα δ≤νβ

  linear≤target =
    unitLinearSubdivisionBound≤ Γ α β η n

  target≤εη =
    canonicalSecondBoundTarget≤ Γ ε η η≤inner

  total≤εη =
    Rational.≤-trans linear≤target target≤εη
