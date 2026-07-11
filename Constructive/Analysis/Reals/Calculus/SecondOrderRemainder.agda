{-

Second-order remainder estimates for HoTT Cauchy reals.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Calculus.SecondOrderRemainder where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Nat using (ℕ ; suc ; zero)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.DerivativeData
open import Constructive.Analysis.Reals.Calculus.SegmentEstimates
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Structures
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational
import Constructive.Data.Rationals.Archimedean as RationalArch
import Constructive.Data.Rationals.Factorial as RationalFactorial



boundedSecondDerivativeLinearRemainderUnitSubdivision :
  {f g dg : ℝᶜ → ℝᶜ} →
  {μ ν : PrecisionModulus} →
  (σ Γ α β η : ℚ⁺) →
  HasDerivativeOnBallWith f g (σ +⁺ 1⁺) μ →
  HasDerivativeOnBallWith g dg (σ +⁺ 1⁺) ν →
  BoundedOnBallWith dg (σ +⁺ 1⁺) Γ →
  (x h : ℝᶜ) →
  BoundedByᶜ σ x →
  BoundedByᶜ η h →
  radius η ℚOrder.≤ 1ℚ →
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


boundedSecondDerivativeHasDerivativeAtWithFromSecondBound :
  {f g dg : ℝᶜ → ℝᶜ} →
  {μ ν : PrecisionModulus} →
  (σ Γ : ℚ⁺) →
  HasDerivativeOnBallWith f g (σ +⁺ 1⁺) μ →
  HasDerivativeOnBallWith g dg (σ +⁺ 1⁺) ν →
  BoundedOnBallWith dg (σ +⁺ 1⁺) Γ →
  (x : ℝᶜ) →
  BoundedByᶜ σ x →
  HasDerivativeAtWith
    f
    x
    (g x)
    (λ ε → min⁺ 1⁺ (posInv⁺ (Γ +⁺ 1⁺) *⁺ quarter⁺ ε))
boundedSecondDerivativeHasDerivativeAtWithFromSecondBound
  {f = f}
  {g = g}
  {dg = dg}
  {μ = μ}
  {ν = ν}
  σ
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
  bounded-byᶜ-monotone
    total≤εη
    rawBound
  where
  α β : ℚ⁺
  α =
    quarter⁺ ε
  β =
    1⁺

  canonical : ℚ⁺
  canonical =
    min⁺ 1⁺ (posInv⁺ (Γ +⁺ 1⁺) *⁺ quarter⁺ ε)

  η≤1 :
    radius η ℚOrder.≤ 1ℚ
  η≤1 =
    Rational.≤-trans
      {p = radius η}
      {q = radius canonical}
      {r = 1ℚ}
      η≤canonical
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

  unit<target :
    RationalArch.unitFraction n ℚOrder.< radius stepTarget
  unit<target =
    stepSearch .snd

  δ≤target :
    radius (unitFraction⁺ n *⁺ η) ℚOrder.≤ radius stepTarget
  δ≤target =
    unitFractionTimes≤ n η stepTarget η≤1 unit<target

  δ≤μα :
    radius (unitFraction⁺ n *⁺ η) ℚOrder.≤ radius (μ α)
  δ≤μα =
    Rational.≤-trans
      {p = radius (unitFraction⁺ n *⁺ η)}
      {q = radius stepTarget}
      {r = radius (μ α)}
      δ≤target
      (min⁺≤left (μ α) (ν β))

  δ≤νβ :
    radius (unitFraction⁺ n *⁺ η) ℚOrder.≤ radius (ν β)
  δ≤νβ =
    Rational.≤-trans
      {p = radius (unitFraction⁺ n *⁺ η)}
      {q = radius stepTarget}
      {r = radius (ν β)}
      δ≤target
      (min⁺≤right (μ α) (ν β))

  rawBound :
    BoundedByᶜ
      (linearSubdivisionBound
        (α *⁺ (unitFraction⁺ n *⁺ η))
        (((Γ *⁺ (unitFraction⁺ n *⁺ η)) +⁺
          (β *⁺ (unitFraction⁺ n *⁺ η))) *⁺ η)
        (suc n))
      (linearRemainder f x (g x) h)
  rawBound =
    boundedSecondDerivativeLinearRemainderUnitSubdivision
      σ
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
      η≤1
      n
      δ≤μα
      δ≤νβ

  linear≤target :
    radius
      (linearSubdivisionBound
        (α *⁺ (unitFraction⁺ n *⁺ η))
        (((Γ *⁺ (unitFraction⁺ n *⁺ η)) +⁺
          (β *⁺ (unitFraction⁺ n *⁺ η))) *⁺ η)
        (suc n))
    ℚOrder.≤
    radius
      ((α *⁺ η) +⁺ (((Γ +⁺ β) *⁺ η) *⁺ η))
  linear≤target =
    unitLinearSubdivisionBound≤ Γ α β η n

  target≤εη :
    radius
      ((α *⁺ η) +⁺ (((Γ +⁺ β) *⁺ η) *⁺ η))
    ℚOrder.≤
    radius (ε *⁺ η)
  target≤εη =
    canonicalSecondBoundTarget≤ Γ ε η η≤canonical

  total≤εη :
    radius
      (linearSubdivisionBound
        (α *⁺ (unitFraction⁺ n *⁺ η))
        (((Γ *⁺ (unitFraction⁺ n *⁺ η)) +⁺
          (β *⁺ (unitFraction⁺ n *⁺ η))) *⁺ η)
        (suc n))
    ℚOrder.≤
    radius (ε *⁺ η)
  total≤εη =
    Rational.≤-trans
      {p = radius
        (linearSubdivisionBound
          (α *⁺ (unitFraction⁺ n *⁺ η))
          (((Γ *⁺ (unitFraction⁺ n *⁺ η)) +⁺
            (β *⁺ (unitFraction⁺ n *⁺ η))) *⁺ η)
          (suc n))}
      {q = radius
        ((α *⁺ η) +⁺ (((Γ +⁺ β) *⁺ η) *⁺ η))}
      {r = radius (ε *⁺ η)}
      linear≤target
      target≤εη



boundedSecondDerivativeLinearRemainderSubdivision :
  {f g dg : ℝᶜ → ℝᶜ} →
  {ρ : ℚ⁺} →
  {μ ν : PrecisionModulus} →
  (Γ α β δ η : ℚ⁺) →
  HasDerivativeOnBallWith f g ρ μ →
  HasDerivativeOnBallWith g dg ρ ν →
  BoundedOnBallWith dg ρ Γ →
  (step : ℝᶜ) →
  BoundedByᶜ δ step →
  radius δ ℚOrder.≤ radius (μ α) →
  radius δ ℚOrder.≤ radius (ν β) →
  (m : ℕ) →
  (p : ℝᶜ) →
  ((k : ℕ) → NatOrder._≤_ k m → BoundedByᶜ ρ (gridPointFrom p step k)) →
  ((k : ℕ) → NatOrder._≤_ k m → BoundedByᶜ η (gridDisplacement step k)) →
  BoundedByᶜ
    (linearSubdivisionBound
      (α *⁺ δ)
      (((Γ *⁺ δ) +⁺ (β *⁺ δ)) *⁺ η)
      m)
    (linearRemainder f p (g p) (gridDisplacement step m))
boundedSecondDerivativeLinearRemainderSubdivision
  {f = f}
  {g = g}
  {dg = dg}
  {ρ = ρ}
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
  step-bound
  δ≤μα
  δ≤νβ
  m
  p
  pointBound
  displacementBound =
  go m p pointBound displacementBound
  where
  local : ℚ⁺
  local =
    α *⁺ δ

  variation : ℚ⁺
  variation =
    ((Γ *⁺ δ) +⁺ (β *⁺ δ)) *⁺ η

  go :
    (m : ℕ) →
    (p : ℝᶜ) →
    ((k : ℕ) → NatOrder._≤_ k m → BoundedByᶜ ρ (gridPointFrom p step k)) →
    ((k : ℕ) → NatOrder._≤_ k m → BoundedByᶜ η (gridDisplacement step k)) →
    BoundedByᶜ
      (linearSubdivisionBound local variation m)
      (linearRemainder f p (g p) (gridDisplacement step m))
  go zero p pointBound displacementBound =
    subst
      (BoundedByᶜ 1⁺)
      (sym (linearRemainderZero-path f p (g p)))
      (bounded-byᶜ-zero 1⁺)
  go (suc zero) p pointBound displacementBound =
    subst
      (BoundedByᶜ local)
      (cong (linearRemainder f p (g p)) (sym (add-zero-right step)))
      (firstDerivative
        p
        (pointBound zero NatOrder.zero-≤)
        α
        δ
        δ≤μα
        step
        step-bound)
  go (suc (suc n)) p pointBound displacementBound =
    subst
      (BoundedByᶜ
        (local +⁺ (linearSubdivisionBound local variation (suc n) +⁺
          variation)))
      (linearRemainderStep-path f g p step (gridDisplacement step (suc n)))
      (bounded-byᶜ-add
        local
        (linearSubdivisionBound local variation (suc n) +⁺ variation)
        (linearRemainder f p (g p) step)
        (linearRemainder f (p +ᶜ step) (g (p +ᶜ step))
          (gridDisplacement step (suc n)) +ᶜ
          ((g (p +ᶜ step) +ᶜ (-ᶜ g p)) ·ᶜ
            gridDisplacement step (suc n)))
        localRemainder
        (bounded-byᶜ-add
          (linearSubdivisionBound local variation (suc n))
          variation
          (linearRemainder f (p +ᶜ step) (g (p +ᶜ step))
            (gridDisplacement step (suc n)))
          ((g (p +ᶜ step) +ᶜ (-ᶜ g p)) ·ᶜ
            gridDisplacement step (suc n))
          (go
            (suc n)
            (p +ᶜ step)
            (λ k k≤sucn → pointBound (suc k) (NatOrder.suc-≤-suc k≤sucn))
            (λ k k≤sucn → displacementBound k (NatOrder.≤-suc k≤sucn)))
          derivativeVariation))
    where
    localRemainder :
      BoundedByᶜ
        local
        (linearRemainder f p (g p) step)
    localRemainder =
      firstDerivative
        p
        (pointBound zero NatOrder.zero-≤)
        α
        δ
        δ≤μα
        step
        step-bound

    derivativeIncrement :
      BoundedByᶜ
        ((Γ *⁺ δ) +⁺ (β *⁺ δ))
        (g (p +ᶜ step) +ᶜ (-ᶜ g p))
    derivativeIncrement =
      boundedDerivativeIncrementOneStep
        {f = g}
        {x = p}
        {d = dg p}
        {μ = ν}
        Γ
        (secondDerivative p (pointBound zero NatOrder.zero-≤))
        (secondBound p (pointBound zero NatOrder.zero-≤))
        β
        δ
        δ≤νβ
        step
        step-bound

    derivativeVariation :
      BoundedByᶜ
        variation
        ((g (p +ᶜ step) +ᶜ (-ᶜ g p)) ·ᶜ
          gridDisplacement step (suc n))
    derivativeVariation =
      bounded-byᶜ-mul
        ((Γ *⁺ δ) +⁺ (β *⁺ δ))
        η
        (g (p +ᶜ step) +ᶜ (-ᶜ g p))
        (gridDisplacement step (suc n))
        derivativeIncrement
        (displacementBound (suc n) (NatOrder.≤-suc NatOrder.≤-refl))


boundedSecondDerivativeLinearRemainderUnitSubdivision
  {f = f}
  {g = g}
  {dg = dg}
  {μ = μ}
  {ν = ν}
  σ
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
  η≤1
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

  subdivision :
    BoundedByᶜ
      (linearSubdivisionBound
        (α *⁺ δ)
        (((Γ *⁺ δ) +⁺ (β *⁺ δ)) *⁺ η)
        (suc n))
      (linearRemainder f x (g x) (gridDisplacement step (suc n)))
  subdivision =
    boundedSecondDerivativeLinearRemainderSubdivision
      {f = f}
      {g = g}
      {dg = dg}
      {ρ = σ +⁺ 1⁺}
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
        unitFractionGridPointBoundOne
          σ
          η
          x
          h
          x-bound
          h-bound
          η≤1
          n
          k
          k≤sucn)
      (λ k k≤sucn →
        unitFractionGridDisplacementBound
          n
          k
          k≤sucn
          h-bound)
