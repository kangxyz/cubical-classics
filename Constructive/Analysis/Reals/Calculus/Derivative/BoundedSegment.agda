{-

Bounded one-step derivative estimates for HoTT Cauchy reals.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Calculus.Derivative.BoundedSegment where

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
open import Constructive.Analysis.Reals.Calculus.Derivative
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.CommRing
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational
import Constructive.Data.Rationals.Archimedean as RationalArch
import Constructive.Data.Rationals.Factorial as RationalFactorial


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    increment-from-linear-remainder :
      (Fh Fx d h : 𝓡 .fst) →
      (d · h) + ((Fh + (- Fx)) + (- (d · h))) ≡ Fh + (- Fx)
    increment-from-linear-remainder _ _ _ _ =
      solve! 𝓡

    increment-compose :
      (F₀ F₁ F₂ : 𝓡 .fst) →
      (F₁ + (- F₀)) + (F₂ + (- F₁)) ≡ F₂ + (- F₀)
    increment-compose _ _ _ =
      solve! 𝓡

    linear-remainder-step :
      (F₀ F₁ F₂ g₀ g₁ s d : 𝓡 .fst) →
      (((F₁ + (- F₀)) + (- (g₀ · s))) +
       (((F₂ + (- F₁)) + (- (g₁ · d))) +
        ((g₁ + (- g₀)) · d))) ≡
      (F₂ + (- F₀)) + (- (g₀ · (s + d)))
    linear-remainder-step _ _ _ _ _ _ _ =
      solve! 𝓡

    linear-remainder-zero :
      (F d : 𝓡 .fst) →
      (F + (- F)) + (- (d · 0r)) ≡ 0r
    linear-remainder-zero _ _ =
      solve! 𝓡

    unit-subdivision-summand :
      (u α β Γ η : 𝓡 .fst) →
      (α · (u · η)) +
        (((Γ · (u · η)) + (β · (u · η))) · η)
      ≡
      u · ((α · η) + (((Γ + β) · η) · η))
    unit-subdivision-summand _ _ _ _ _ =
      solve! 𝓡


isPropHasDerivativeAtWith :
  (f : ℝᶜ → ℝᶜ) →
  (x d : ℝᶜ) →
  (μ : PrecisionModulus) →
  isProp (HasDerivativeAtWith f x d μ)
isPropHasDerivativeAtWith f x d μ =
  isPropΠ λ ε →
  isPropΠ λ η →
  isPropΠ λ η≤με →
  isPropΠ λ h →
  isPropΠ λ h-bound →
    isPropBoundedByᶜ
      (ε *⁺ η)
      (linearRemainder f x d h)


hasDerivativeAtWith-submodulus :
  {f : ℝᶜ → ℝᶜ} →
  {x d : ℝᶜ} →
  {μ ν : PrecisionModulus} →
  ((ε : ℚ⁺) → radius (ν ε) ℚOrder.≤ radius (μ ε)) →
  HasDerivativeAtWith f x d μ →
  HasDerivativeAtWith f x d ν
hasDerivativeAtWith-submodulus {μ = μ} {ν = ν} ν≤μ derivative ε η η≤νε h h-bound =
  derivative
    ε
    η
    (Rational.≤-trans
      {p = radius η}
      {q = radius (ν ε)}
      {r = radius (μ ε)}
      η≤νε
      (ν≤μ ε))
    h
    h-bound


HasDerivativeOnBallWith :
  (ℝᶜ → ℝᶜ) →
  (ℝᶜ → ℝᶜ) →
  ℚ⁺ →
  PrecisionModulus →
  Type₀
HasDerivativeOnBallWith f f' ρ μ =
  (x : ℝᶜ) →
  BoundedByᶜ ρ x →
  HasDerivativeAtWith f x (f' x) μ


BoundedOnBallWith :
  (ℝᶜ → ℝᶜ) →
  ℚ⁺ →
  ℚ⁺ →
  Type₀
BoundedOnBallWith f ρ Γ =
  (x : ℝᶜ) →
  BoundedByᶜ ρ x →
  BoundedByᶜ Γ (f x)


unitFraction⁺ :
  ℕ →
  ℚ⁺
unitFraction⁺ n =
  RationalArch.unitFraction n ,
  RationalArch.unitFraction-positive n


segmentPoint :
  ℝᶜ →
  ℝᶜ →
  ℚ →
  ℝᶜ
segmentPoint x h q =
  x +ᶜ scalarMulᶜ q h


gridPointFrom :
  ℝᶜ →
  ℝᶜ →
  ℕ →
  ℝᶜ
gridPointFrom p step zero =
  p
gridPointFrom p step (suc n) =
  gridPointFrom (p +ᶜ step) step n


gridDisplacement :
  ℝᶜ →
  ℕ →
  ℝᶜ
gridDisplacement step zero =
  0ᶜ
gridDisplacement step (suc n) =
  step +ᶜ gridDisplacement step n


gridDisplacement-scalarMul :
  (q : ℚ) →
  (h : ℝᶜ) →
  (m : ℕ) →
  gridDisplacement (scalarMulᶜ q h) m ≡
  scalarMulᶜ (RationalArch.natMul m q) h
gridDisplacement-scalarMul q h zero =
  sym (scalarMulᶜ-zero h) ∙
  cong
    (λ r → scalarMulᶜ r h)
    (sym (RationalArch.natMul-zero q))
gridDisplacement-scalarMul q h (suc n) =
  cong
    (scalarMulᶜ q h +ᶜ_)
    (gridDisplacement-scalarMul q h n) ∙
  sym
    (scalarMulᶜ-distrib-scalar-add
      q
      (RationalArch.natMul n q)
      h) ∙
  cong
    (λ r → scalarMulᶜ r h)
    (ℚ.+Comm q (RationalArch.natMul n q) ∙
     sym (RationalArch.natMul-suc n q))


gridDisplacement-unitFraction :
  (h : ℝᶜ) →
  (n : ℕ) →
  gridDisplacement
    (scalarMulᶜ (RationalArch.unitFraction n) h)
    (suc n)
  ≡ h
gridDisplacement-unitFraction h n =
  gridDisplacement-scalarMul (RationalArch.unitFraction n) h (suc n) ∙
  cong
    (λ q → scalarMulᶜ q h)
    (RationalArch.natMul-unitFraction n) ∙
  scalarMulᶜ-one h


gridPointFrom-displacement :
  (p step : ℝᶜ) →
  (m : ℕ) →
  gridPointFrom p step m ≡ p +ᶜ gridDisplacement step m
gridPointFrom-displacement p step zero =
  sym (add-zero-right p)
gridPointFrom-displacement p step (suc n) =
  gridPointFrom-displacement (p +ᶜ step) step n ∙
  sym (add-assoc p step (gridDisplacement step n))


gridPointFrom-scalarMul :
  (x h : ℝᶜ) →
  (q : ℚ) →
  (m : ℕ) →
  gridPointFrom x (scalarMulᶜ q h) m ≡
  segmentPoint x h (RationalArch.natMul m q)
gridPointFrom-scalarMul x h q m =
  gridPointFrom-displacement x (scalarMulᶜ q h) m ∙
  cong (x +ᶜ_) (gridDisplacement-scalarMul q h m)


repeatPositive :
  ℚ⁺ →
  ℕ →
  ℚ⁺
repeatPositive κ zero =
  1⁺
repeatPositive κ (suc zero) =
  κ
repeatPositive κ (suc (suc n)) =
  κ +⁺ repeatPositive κ (suc n)


linearSubdivisionBound :
  ℚ⁺ →
  ℚ⁺ →
  ℕ →
  ℚ⁺
linearSubdivisionBound local variation zero =
  1⁺
linearSubdivisionBound local variation (suc zero) =
  local
linearSubdivisionBound local variation (suc (suc n)) =
  local +⁺ (linearSubdivisionBound local variation (suc n) +⁺ variation)


repeatPositive-suc-radius :
  (κ : ℚ⁺) →
  (n : ℕ) →
  radius (repeatPositive κ (suc n)) ≡
  RationalArch.natMul (suc n) (radius κ)
repeatPositive-suc-radius κ zero =
  sym (RationalArch.natMul-one (radius κ))
repeatPositive-suc-radius κ (suc n) =
  cong (λ q → radius κ ℚ.+ q) (repeatPositive-suc-radius κ n) ∙
  ℚ.+Comm (radius κ) (RationalArch.natMul (suc n) (radius κ)) ∙
  sym (RationalArch.natMul-suc (suc n) (radius κ))


linearSubdivisionBound≤repeat :
  (local variation : ℚ⁺) →
  (n : ℕ) →
  radius (linearSubdivisionBound local variation (suc n))
    ℚOrder.≤
  radius (repeatPositive (local +⁺ variation) (suc n))
linearSubdivisionBound≤repeat local variation zero =
  Rational.<→≤
    {p = radius local}
    {q = radius (local +⁺ variation)}
    (summand-left<sum local variation)
linearSubdivisionBound≤repeat local variation (suc n) =
  subst
    (λ q →
      radius local ℚ.+
        (radius (linearSubdivisionBound local variation (suc n)) ℚ.+
         radius variation)
      ℚOrder.≤ q)
    reorder
    step≤
  where
  κ : ℚ⁺
  κ =
    local +⁺ variation

  step≤ :
    radius local ℚ.+
      (radius (linearSubdivisionBound local variation (suc n)) ℚ.+
       radius variation)
    ℚOrder.≤
    radius local ℚ.+
      (radius (repeatPositive κ (suc n)) ℚ.+
       radius variation)
  step≤ =
    ℚOrder.≤Monotone+
      (radius local)
      (radius local)
      (radius (linearSubdivisionBound local variation (suc n)) ℚ.+
       radius variation)
      (radius (repeatPositive κ (suc n)) ℚ.+
       radius variation)
      (Rational.≤-refl (radius local))
      (ℚOrder.≤Monotone+
        (radius (linearSubdivisionBound local variation (suc n)))
        (radius (repeatPositive κ (suc n)))
        (radius variation)
        (radius variation)
        (linearSubdivisionBound≤repeat local variation n)
        (Rational.≤-refl (radius variation)))

  reorder :
    radius local ℚ.+
      (radius (repeatPositive κ (suc n)) ℚ.+
       radius variation)
    ≡
    radius κ ℚ.+ radius (repeatPositive κ (suc n))
  reorder =
    cong
      (radius local ℚ.+_)
      (ℚ.+Comm (radius (repeatPositive κ (suc n))) (radius variation)) ∙
    ℚ.+Assoc
      (radius local)
      (radius variation)
      (radius (repeatPositive κ (suc n)))


unitSubdivisionSummand-path :
  (Γ α β η : ℚ⁺) →
  (n : ℕ) →
  (α *⁺ (unitFraction⁺ n *⁺ η)) +⁺
    (((Γ *⁺ (unitFraction⁺ n *⁺ η)) +⁺
      (β *⁺ (unitFraction⁺ n *⁺ η))) *⁺ η)
  ≡
  unitFraction⁺ n *⁺
    ((α *⁺ η) +⁺ (((Γ +⁺ β) *⁺ η) *⁺ η))
unitSubdivisionSummand-path Γ α β η n =
  ℚ⁺Path
    (SolverHelpers.unit-subdivision-summand
      ℚCommRing
      (RationalArch.unitFraction n)
      (radius α)
      (radius β)
      (radius Γ)
      (radius η))


unitFractionRepeat-path :
  (κ : ℚ⁺) →
  (n : ℕ) →
  RationalArch.natMul
    (suc n)
    (radius (unitFraction⁺ n *⁺ κ))
  ≡
  radius κ
unitFractionRepeat-path κ n =
  cong
    (RationalArch.natMul (suc n))
    (ℚ.·Comm (RationalArch.unitFraction n) (radius κ)) ∙
  RationalArch.natMul-mul-left
    (suc n)
    (radius κ)
    (RationalArch.unitFraction n) ∙
  cong
    (radius κ ℚ.·_)
    (RationalArch.natMul-unitFraction n) ∙
  ℚ.·IdR (radius κ)


unitLinearSubdivisionBound≤ :
  (Γ α β η : ℚ⁺) →
  (n : ℕ) →
  radius
    (linearSubdivisionBound
      (α *⁺ (unitFraction⁺ n *⁺ η))
      (((Γ *⁺ (unitFraction⁺ n *⁺ η)) +⁺
        (β *⁺ (unitFraction⁺ n *⁺ η))) *⁺ η)
      (suc n))
    ℚOrder.≤
  radius ((α *⁺ η) +⁺ (((Γ +⁺ β) *⁺ η) *⁺ η))
unitLinearSubdivisionBound≤ Γ α β η n =
  Rational.≤-trans
    {p = radius linearBound}
    {q = radius (repeatPositive summand (suc n))}
    {r = radius target}
    (linearSubdivisionBound≤repeat local variation n)
    repeat≤target
  where
  δ : ℚ⁺
  δ =
    unitFraction⁺ n *⁺ η

  local variation summand target : ℚ⁺
  local =
    α *⁺ δ
  variation =
    (((Γ *⁺ δ) +⁺ (β *⁺ δ)) *⁺ η)
  summand =
    local +⁺ variation
  target =
    (α *⁺ η) +⁺ (((Γ +⁺ β) *⁺ η) *⁺ η)

  linearBound : ℚ⁺
  linearBound =
    linearSubdivisionBound local variation (suc n)

  repeatPath :
    radius (repeatPositive summand (suc n)) ≡ radius target
  repeatPath =
    repeatPositive-suc-radius summand n ∙
    cong
      (RationalArch.natMul (suc n))
      (cong radius (unitSubdivisionSummand-path Γ α β η n)) ∙
    unitFractionRepeat-path target n

  repeat≤target :
    radius (repeatPositive summand (suc n)) ℚOrder.≤ radius target
  repeat≤target =
    subst
      (λ q → q ℚOrder.≤ radius target)
      (sym repeatPath)
      (Rational.≤-refl (radius target))


unitFractionTimes≤ :
  (n : ℕ) →
  (η target : ℚ⁺) →
  radius η ℚOrder.≤ 1ℚ →
  RationalArch.unitFraction n ℚOrder.< radius target →
  radius (unitFraction⁺ n *⁺ η) ℚOrder.≤ radius target
unitFractionTimes≤ n η target η≤1 unit<target =
  Rational.≤-trans
    {p = RationalArch.unitFraction n ℚ.· radius η}
    {q = RationalArch.unitFraction n}
    {r = radius target}
    unitη≤unit
    (Rational.<→≤
      {p = RationalArch.unitFraction n}
      {q = radius target}
      unit<target)
  where
  unit : ℚ
  unit =
    RationalArch.unitFraction n

  0≤unit : 0ℚ ℚOrder.≤ unit
  0≤unit =
    Rational.<→≤
      {p = 0ℚ}
      {q = unit}
      (RationalArch.unitFraction-positive n)

  unitη≤unit :
    unit ℚ.· radius η ℚOrder.≤ unit
  unitη≤unit =
    subst
      (λ q → unit ℚ.· radius η ℚOrder.≤ q)
      (ℚ.·IdR unit)
      (Rational.mul-left-nonnegative-≤
        {a = unit}
        {b = radius η}
        {c = 1ℚ}
        0≤unit
        η≤1)


gammaInvQuarter-path :
  (Γ ε : ℚ⁺) →
  radius ((Γ +⁺ 1⁺) *⁺
    (posInv⁺ (Γ +⁺ 1⁺) *⁺ quarter⁺ ε))
  ≡
  radius (quarter⁺ ε)
gammaInvQuarter-path Γ ε =
  ℚ.·Assoc
    (radius (Γ +⁺ 1⁺))
    (radius (posInv⁺ (Γ +⁺ 1⁺)))
    (radius (quarter⁺ ε)) ∙
  cong
    (λ q → q ℚ.· radius (quarter⁺ ε))
    (Rational.posInv-right
      (radius (Γ +⁺ 1⁺))
      ((Γ +⁺ 1⁺) .snd)) ∙
  ℚ.·IdL (radius (quarter⁺ ε))


canonicalSecondBoundTarget≤ :
  (Γ ε η : ℚ⁺) →
  radius η ℚOrder.≤
    radius (min⁺ 1⁺ (posInv⁺ (Γ +⁺ 1⁺) *⁺ quarter⁺ ε)) →
  radius
    ((quarter⁺ ε *⁺ η) +⁺
     (((Γ +⁺ 1⁺) *⁺ η) *⁺ η))
  ℚOrder.≤
  radius (ε *⁺ η)
canonicalSecondBoundTarget≤ Γ ε η η≤canonical =
  Rational.≤-trans
    {p = radius target}
    {q = radius doubleQuarter}
    {r = radius (ε *⁺ η)}
    target≤doubleQuarter
    doubleQuarter≤εη
  where
  quarterη second target doubleQuarter : ℚ⁺
  quarterη =
    quarter⁺ ε *⁺ η
  second =
    ((Γ +⁺ 1⁺) *⁺ η) *⁺ η
  target =
    quarterη +⁺ second
  doubleQuarter =
    quarterη +⁺ quarterη

  η≤invQuarter :
    radius η ℚOrder.≤
    radius (posInv⁺ (Γ +⁺ 1⁺) *⁺ quarter⁺ ε)
  η≤invQuarter =
    Rational.≤-trans
      {p = radius η}
      {q = radius
        (min⁺ 1⁺ (posInv⁺ (Γ +⁺ 1⁺) *⁺ quarter⁺ ε))}
      {r = radius (posInv⁺ (Γ +⁺ 1⁺) *⁺ quarter⁺ ε)}
      η≤canonical
      (min⁺≤right 1⁺ (posInv⁺ (Γ +⁺ 1⁺) *⁺ quarter⁺ ε))

  gammaη≤quarter :
    radius ((Γ +⁺ 1⁺) *⁺ η) ℚOrder.≤ radius (quarter⁺ ε)
  gammaη≤quarter =
    subst
      (λ q → radius ((Γ +⁺ 1⁺) *⁺ η) ℚOrder.≤ q)
      (gammaInvQuarter-path Γ ε)
      (Rational.mul-left-nonnegative-≤
        {a = radius (Γ +⁺ 1⁺)}
        {b = radius η}
        {c = radius (posInv⁺ (Γ +⁺ 1⁺) *⁺ quarter⁺ ε)}
        (Rational.<→≤
          {p = 0ℚ}
          {q = radius (Γ +⁺ 1⁺)}
          ((Γ +⁺ 1⁺) .snd))
        η≤invQuarter)

  second≤quarterη :
    radius second ℚOrder.≤ radius quarterη
  second≤quarterη =
    ℚOrder.≤-·o
      (radius ((Γ +⁺ 1⁺) *⁺ η))
      (radius (quarter⁺ ε))
      (radius η)
      (Rational.<→≤
        {p = 0ℚ}
        {q = radius η}
        (η .snd))
      gammaη≤quarter

  target≤doubleQuarter :
    radius target ℚOrder.≤ radius doubleQuarter
  target≤doubleQuarter =
    ℚOrder.≤Monotone+
      (radius quarterη)
      (radius quarterη)
      (radius second)
      (radius quarterη)
      (Rational.≤-refl (radius quarterη))
      second≤quarterη

  doubleQuarterProductPath :
    radius doubleQuarter ≡ radius ((quarter⁺ ε +⁺ quarter⁺ ε) *⁺ η)
  doubleQuarterProductPath =
    sym
      (ℚ.·DistR+
        (radius (quarter⁺ ε))
        (radius (quarter⁺ ε))
        (radius η))

  doubleQuarter≤εη :
    radius doubleQuarter ℚOrder.≤ radius (ε *⁺ η)
  doubleQuarter≤εη =
    Rational.<→≤
      {p = radius doubleQuarter}
      {q = radius (ε *⁺ η)}
      (subst
        (λ q → q ℚOrder.< radius (ε *⁺ η))
        (sym doubleQuarterProductPath)
        (ℚOrder.<-·o
          (radius (quarter⁺ ε +⁺ quarter⁺ ε))
          (radius ε)
          (radius η)
          (η .snd)
          (quarter-sum< ε)))


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


bounded-byᶜ-zero :
  (ε : ℚ⁺) →
  BoundedByᶜ ε 0ᶜ
bounded-byᶜ-zero ε =
  rational-closed-bound→boundedᶜ
    ε
    Rational.0ℚ
    (rational-closed-boundᶜ
      0≤ε
      (subst
        (λ q → q ℚOrder.≤ radius ε)
        (sym Rational.neg-zero)
        0≤ε))
  where
  0≤ε : Rational.0ℚ ℚOrder.≤ radius ε
  0≤ε =
    ℚOrder.<Weaken≤ Rational.0ℚ (radius ε) (ε .snd)


bounded-byᶜ-scale-unitInterval :
  (q : ℚ) →
  0ℚ ℚOrder.≤ q →
  q ℚOrder.≤ 1ℚ →
  {η : ℚ⁺} →
  {h : ℝᶜ} →
  BoundedByᶜ η h →
  BoundedByᶜ η (scalarMulᶜ q h)
bounded-byᶜ-scale-unitInterval q 0≤q q≤1 {η = η} {h = h} h-bound =
  subst
    (λ κ → BoundedByᶜ κ (scalarMulᶜ q h))
    (*⁺-identity-left η)
    (bounded-byᶜ-scale-nonnegative q η 1⁺ h 0≤q q≤1 h-bound)


segmentPointBound :
  (σ η : ℚ⁺) →
  (x h : ℝᶜ) →
  BoundedByᶜ σ x →
  BoundedByᶜ η h →
  (q : ℚ) →
  0ℚ ℚOrder.≤ q →
  q ℚOrder.≤ 1ℚ →
  BoundedByᶜ
    (σ +⁺ η)
    (segmentPoint x h q)
segmentPointBound σ η x h x-bound h-bound q 0≤q q≤1 =
  bounded-byᶜ-add
    σ
    η
    x
    (scalarMulᶜ q h)
    x-bound
    (bounded-byᶜ-scale-unitInterval q 0≤q q≤1 h-bound)


segmentPointBoundOne :
  (σ η : ℚ⁺) →
  (x h : ℝᶜ) →
  BoundedByᶜ σ x →
  BoundedByᶜ η h →
  radius η ℚOrder.≤ 1ℚ →
  (q : ℚ) →
  0ℚ ℚOrder.≤ q →
  q ℚOrder.≤ 1ℚ →
  BoundedByᶜ
    (σ +⁺ 1⁺)
    (segmentPoint x h q)
segmentPointBoundOne σ η x h x-bound h-bound η≤1 q 0≤q q≤1 =
  bounded-byᶜ-monotone
    σ+η≤σ+1
    (segmentPointBound σ η x h x-bound h-bound q 0≤q q≤1)
  where
  σ+η≤σ+1 :
    radius (σ +⁺ η) ℚOrder.≤ radius (σ +⁺ 1⁺)
  σ+η≤σ+1 =
    ℚOrder.≤Monotone+
      (radius σ)
      (radius σ)
      (radius η)
      1ℚ
      (Rational.≤-refl (radius σ))
      η≤1


natMul-unitFraction-nonnegative :
  (n k : ℕ) →
  0ℚ ℚOrder.≤
  RationalArch.natMul k (RationalArch.unitFraction n)
natMul-unitFraction-nonnegative n k =
  RationalArch.natMul-nonnegative
    k
    (RationalArch.unitFraction-positive n)


natMul-unitFraction≤1 :
  (n k : ℕ) →
  NatOrder._≤_ k (suc n) →
  RationalArch.natMul k (RationalArch.unitFraction n)
    ℚOrder.≤ 1ℚ
natMul-unitFraction≤1 n k k≤sucn =
  subst
    (λ q →
      RationalArch.natMul k (RationalArch.unitFraction n)
        ℚOrder.≤ q)
    (RationalArch.natMul-unitFraction n)
    (RationalArch.natMul-mono-≤
      k
      (suc n)
      (RationalArch.unitFraction-positive n)
      k≤sucn)


unitFractionStepBound :
  (n : ℕ) →
  {η : ℚ⁺} →
  {h : ℝᶜ} →
  BoundedByᶜ η h →
  BoundedByᶜ
    (unitFraction⁺ n *⁺ η)
    (scalarMulᶜ (RationalArch.unitFraction n) h)
unitFractionStepBound n {η = η} {h = h} h-bound =
  bounded-byᶜ-scale-nonnegative
    (RationalArch.unitFraction n)
    η
    (unitFraction⁺ n)
    h
    (Rational.<→≤
      {p = 0ℚ}
      {q = RationalArch.unitFraction n}
      (RationalArch.unitFraction-positive n))
    (Rational.≤-refl (RationalArch.unitFraction n))
    h-bound


unitFractionGridDisplacementBound :
  (n k : ℕ) →
  NatOrder._≤_ k (suc n) →
  {η : ℚ⁺} →
  {h : ℝᶜ} →
  BoundedByᶜ η h →
  BoundedByᶜ η
    (gridDisplacement
      (scalarMulᶜ (RationalArch.unitFraction n) h)
      k)
unitFractionGridDisplacementBound n k k≤sucn {η = η} {h = h} h-bound =
  subst
    (BoundedByᶜ η)
    (sym
      (gridDisplacement-scalarMul
        (RationalArch.unitFraction n)
        h
        k))
    (bounded-byᶜ-scale-unitInterval
      (RationalArch.natMul k (RationalArch.unitFraction n))
      (natMul-unitFraction-nonnegative n k)
      (natMul-unitFraction≤1 n k k≤sucn)
      h-bound)


unitFractionGridPointBoundOne :
  (σ η : ℚ⁺) →
  (x h : ℝᶜ) →
  BoundedByᶜ σ x →
  BoundedByᶜ η h →
  radius η ℚOrder.≤ 1ℚ →
  (n k : ℕ) →
  NatOrder._≤_ k (suc n) →
  BoundedByᶜ (σ +⁺ 1⁺)
    (gridPointFrom
      x
      (scalarMulᶜ (RationalArch.unitFraction n) h)
      k)
unitFractionGridPointBoundOne σ η x h x-bound h-bound η≤1 n k k≤sucn =
  subst
    (BoundedByᶜ (σ +⁺ 1⁺))
    (sym
      (gridPointFrom-scalarMul
        x
        h
        (RationalArch.unitFraction n)
        k))
    (segmentPointBoundOne
      σ
      η
      x
      h
      x-bound
      h-bound
      η≤1
      (RationalArch.natMul k (RationalArch.unitFraction n))
      (natMul-unitFraction-nonnegative n k)
      (natMul-unitFraction≤1 n k k≤sucn))


incrementFromLinearRemainder-path :
  (f : ℝᶜ → ℝᶜ) →
  (x d h : ℝᶜ) →
  d ·ᶜ h +ᶜ linearRemainder f x d h ≡
  f (x +ᶜ h) +ᶜ (-ᶜ f x)
incrementFromLinearRemainder-path f x d h =
  SolverHelpers.increment-from-linear-remainder
    CauchyRealsCommRing
    (f (x +ᶜ h))
    (f x)
    d
    h


incrementCompose-path :
  (F₀ F₁ F₂ : ℝᶜ) →
  (F₁ +ᶜ (-ᶜ F₀)) +ᶜ (F₂ +ᶜ (-ᶜ F₁)) ≡
  F₂ +ᶜ (-ᶜ F₀)
incrementCompose-path =
  SolverHelpers.increment-compose CauchyRealsCommRing


linearRemainderStep-path :
  (f g : ℝᶜ → ℝᶜ) →
  (p step disp : ℝᶜ) →
  (linearRemainder f p (g p) step +ᶜ
   (linearRemainder f (p +ᶜ step) (g (p +ᶜ step)) disp +ᶜ
    ((g (p +ᶜ step) +ᶜ (-ᶜ g p)) ·ᶜ disp))) ≡
  linearRemainder f p (g p) (step +ᶜ disp)
linearRemainderStep-path f g p step disp =
  SolverHelpers.linear-remainder-step
    CauchyRealsCommRing
    (f p)
    (f (p +ᶜ step))
    (f ((p +ᶜ step) +ᶜ disp))
    (g p)
    (g (p +ᶜ step))
    step
    disp ∙
  cong
    (λ z →
      (f z +ᶜ (-ᶜ f p)) +ᶜ
      (-ᶜ (g p ·ᶜ (step +ᶜ disp))))
    (sym (add-assoc p step disp))


linearRemainderZero-path :
  (f : ℝᶜ → ℝᶜ) →
  (p d : ℝᶜ) →
  linearRemainder f p d 0ᶜ ≡ 0ᶜ
linearRemainderZero-path f p d =
  cong
    (λ z → (f z +ᶜ (-ᶜ f p)) +ᶜ (-ᶜ (d ·ᶜ 0ᶜ)))
    (add-zero-right p) ∙
  SolverHelpers.linear-remainder-zero CauchyRealsCommRing (f p) d


boundedDerivativeIncrementOneStep :
  {f : ℝᶜ → ℝᶜ} →
  {x d : ℝᶜ} →
  {μ : PrecisionModulus} →
  (Γ : ℚ⁺) →
  HasDerivativeAtWith f x d μ →
  BoundedByᶜ Γ d →
  (ε η : ℚ⁺) →
  radius η ℚOrder.≤ radius (μ ε) →
  (h : ℝᶜ) →
  BoundedByᶜ η h →
  BoundedByᶜ
    ((Γ *⁺ η) +⁺ (ε *⁺ η))
    (f (x +ᶜ h) +ᶜ (-ᶜ f x))
boundedDerivativeIncrementOneStep
  {f = f}
  {x = x}
  {d = d}
  Γ
  derivative
  d-bound
  ε
  η
  η≤με
  h
  h-bound =
  subst
    (BoundedByᶜ ((Γ *⁺ η) +⁺ (ε *⁺ η)))
    (incrementFromLinearRemainder-path f x d h)
    incrementBound
  where
  productBound :
    BoundedByᶜ (Γ *⁺ η) (d ·ᶜ h)
  productBound =
    bounded-byᶜ-mul Γ η d h d-bound h-bound

  remainderBound :
    BoundedByᶜ (ε *⁺ η) (linearRemainder f x d h)
  remainderBound =
    derivative ε η η≤με h h-bound

  incrementBound :
    BoundedByᶜ
      ((Γ *⁺ η) +⁺ (ε *⁺ η))
      (d ·ᶜ h +ᶜ linearRemainder f x d h)
  incrementBound =
    bounded-byᶜ-add
      (Γ *⁺ η)
      (ε *⁺ η)
      (d ·ᶜ h)
      (linearRemainder f x d h)
      productBound
      remainderBound


boundedDerivativeIncrementSubdivision :
  {f f' : ℝᶜ → ℝᶜ} →
  {ρ : ℚ⁺} →
  {μ : PrecisionModulus} →
  (Γ α δ : ℚ⁺) →
  HasDerivativeOnBallWith f f' ρ μ →
  BoundedOnBallWith f' ρ Γ →
  (step : ℝᶜ) →
  BoundedByᶜ δ step →
  radius δ ℚOrder.≤ radius (μ α) →
  (m : ℕ) →
  (p : ℝᶜ) →
  ((k : ℕ) → NatOrder._≤_ k m → BoundedByᶜ ρ (gridPointFrom p step k)) →
  BoundedByᶜ
    (repeatPositive ((Γ *⁺ δ) +⁺ (α *⁺ δ)) m)
    (f (gridPointFrom p step m) +ᶜ (-ᶜ f p))
boundedDerivativeIncrementSubdivision
  {f = f}
  {f' = f'}
  {ρ = ρ}
  {μ = μ}
  Γ
  α
  δ
  derivative
  derivativeBound
  step
  step-bound
  δ≤μα
  m
  p
  pointBound =
  go m p pointBound
  where
  localBound : ℚ⁺
  localBound =
    (Γ *⁺ δ) +⁺ (α *⁺ δ)

  go :
    (m : ℕ) →
    (p : ℝᶜ) →
    ((k : ℕ) → NatOrder._≤_ k m → BoundedByᶜ ρ (gridPointFrom p step k)) →
    BoundedByᶜ
      (repeatPositive localBound m)
      (f (gridPointFrom p step m) +ᶜ (-ᶜ f p))
  go zero p pointBound =
    subst
      (BoundedByᶜ 1⁺)
      (sym (add-inverse-right (f p)))
      (bounded-byᶜ-zero 1⁺)
  go (suc zero) p pointBound =
    boundedDerivativeIncrementOneStep
      {f = f}
      {x = p}
      {d = f' p}
      {μ = μ}
      Γ
      (derivative p (pointBound zero NatOrder.zero-≤))
      (derivativeBound p (pointBound zero NatOrder.zero-≤))
      α
      δ
      δ≤μα
      step
      step-bound
  go (suc (suc n)) p pointBound =
    subst
      (BoundedByᶜ
        (localBound +⁺ repeatPositive localBound (suc n)))
      (incrementCompose-path
        (f p)
        (f (p +ᶜ step))
        (f (gridPointFrom (p +ᶜ step) step (suc n))))
      (bounded-byᶜ-add
        localBound
        (repeatPositive localBound (suc n))
        (f (p +ᶜ step) +ᶜ (-ᶜ f p))
        (f (gridPointFrom (p +ᶜ step) step (suc n)) +ᶜ
         (-ᶜ f (p +ᶜ step)))
        oneStep
        (go
          (suc n)
          (p +ᶜ step)
          (λ k k≤sucn → pointBound (suc k) (NatOrder.suc-≤-suc k≤sucn))))
    where
    oneStep :
      BoundedByᶜ
        localBound
        (f (p +ᶜ step) +ᶜ (-ᶜ f p))
    oneStep =
      boundedDerivativeIncrementOneStep
        {f = f}
        {x = p}
        {d = f' p}
        {μ = μ}
        Γ
        (derivative p (pointBound zero NatOrder.zero-≤))
        (derivativeBound p (pointBound zero NatOrder.zero-≤))
        α
        δ
        δ≤μα
        step
        step-bound


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
