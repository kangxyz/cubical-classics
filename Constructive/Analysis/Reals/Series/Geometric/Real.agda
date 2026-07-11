{-

Real geometric series from explicit power bounds

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Series.Geometric.Real where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat as Nat
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.GeometricDecay
open import Constructive.Analysis.GeometricDecay.Algebra
open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Modulus using (AntitoneNatModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Structures
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Quantitative
  using (bounded-byᶜ-abs≤rational)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Inverse
  using (HasRightInverseᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Power
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Metric
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using (absᶜ)
open import Constructive.Analysis.Reals.Series.Cauchy
open import Constructive.Analysis.Reals.Series.Neumann
open import Constructive.Analysis.Reals.Series.Comparison
open import Constructive.Analysis.Reals.Series.Finite
open import Constructive.Analysis.Reals.Series.Tail
open import Constructive.Analysis.Reals.Series.Geometric.Positive
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


record RealGeometricBound (x : ℝᶜ) : Type₀ where
  constructor real-geometric-bound
  no-eta-equality

  field
    ratioBound : ℚ⁺
    ratioBound<1 : radius ratioBound ℚOrder.< Rational.1ℚ
    termBound : BoundedByᶜ ratioBound x


open RealGeometricBound public


realGeometricFiniteIdentity :
  (x : ℝᶜ) →
  (n : ℕ) →
  (1ᶜ +ᶜ (-ᶜ x)) ·ᶜ partialSum (realPower x) n ≡
  1ᶜ +ᶜ (-ᶜ realPower x n)
realGeometricFiniteIdentity x zero =
  SolverHelpers.geometric-zero CauchyRealsCommRing x
realGeometricFiniteIdentity x (suc n) =
  cong
    ((1ᶜ +ᶜ (-ᶜ x)) ·ᶜ_)
    (partialSum-snoc (realPower x) n) ∙
  SolverHelpers.geometric-distrib CauchyRealsCommRing x S p ∙
  cong
    (λ q → q +ᶜ ((1ᶜ +ᶜ (-ᶜ x)) ·ᶜ p))
    (realGeometricFiniteIdentity x n) ∙
  SolverHelpers.geometric-step CauchyRealsCommRing x p
  where
  S : ℝᶜ
  S =
    partialSum (realPower x) n

  p : ℝᶜ
  p =
    realPower x n


private
  realGeometricPowerMajorizedByPositive :
    (x : ℝᶜ) →
    (bound : RealGeometricBound x) →
    SeriesMajorizedBy
      (realPower x)
      (positiveGeometricTerm (ratioBound bound))
  realGeometricPowerMajorizedByPositive x bound =
    termMajorized , majorantNonnegative
    where
    ρ : ℚ⁺
    ρ =
      ratioBound bound

    termMajorized :
      (m n : ℕ) →
      absᶜ (shift m (realPower x) n) ≤ᶜ
      shift m (positiveGeometricTerm ρ) n
    termMajorized m n =
      subst2
        (λ u v → absᶜ u ≤ᶜ v)
        (sym (shift-index m (realPower x) n))
        (sym (shift-index m (positiveGeometricTerm ρ) n))
        (bounded-byᶜ-abs≤rational
          (realPowerBoundsFromBound
            ρ
            x
            (termBound bound)
            (m Nat.+ n)))

    majorantNonnegative :
      (m n : ℕ) →
      0ᶜ ≤ᶜ shift m (positiveGeometricTerm ρ) n
    majorantNonnegative m n =
      subst
        (λ v → 0ᶜ ≤ᶜ v)
        (sym (shift-index m (positiveGeometricTerm ρ) n))
        (positiveGeometricTerm-nonnegative ρ (m Nat.+ n))


realGeometricPowerTailBound :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  TailBound
    (realPower x)
    (positiveGeometricPowerModulus
      (ratioBound bound)
      (ratioBound<1 bound))
realGeometricPowerTailBound x bound =
  comparisonTest
    (realGeometricPowerMajorizedByPositive x bound)
    (positiveGeometricFiniteTailBoundFromRatio
      (ratioBound bound)
      (ratioBound<1 bound))


realGeometricPowerSum :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  ℝᶜ
realGeometricPowerSum x bound =
  seriesSumFromFiniteTailBound
    (realPower x)
    μ
    (realGeometricPowerTailBound x bound)
    μ-antitone
  where
  μ : ℚ⁺ → ℕ
  μ =
    positiveGeometricPowerModulus
      (ratioBound bound)
      (ratioBound<1 bound)

  μ-antitone : AntitoneNatModulus μ
  μ-antitone =
    positiveGeometricPowerModulus-antitone
      (ratioBound bound)
      (ratioBound<1 bound)


realGeometricPowerConverges :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromFiniteTailBound
      (realPower x)
      (positiveGeometricPowerModulus
        (ratioBound bound)
        (ratioBound<1 bound))
      (realGeometricPowerTailBound x bound)
      (positiveGeometricPowerModulus-antitone
        (ratioBound bound)
        (ratioBound<1 bound)))
    (realGeometricPowerSum x bound)
realGeometricPowerConverges x bound =
  seriesSumFromFiniteTailBoundConverges
    (realPower x)
    (positiveGeometricPowerModulus
      (ratioBound bound)
      (ratioBound<1 bound))
    (realGeometricPowerTailBound x bound)
    (positiveGeometricPowerModulus-antitone
      (ratioBound bound)
      (ratioBound<1 bound))


realGeometricPowerNeumannRightInverse :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (1ᶜ +ᶜ (-ᶜ x)) →
  (1ᶜ +ᶜ (-ᶜ x)) ·ᶜ
    realGeometricPowerSum x bound
  ≡ 1ᶜ
realGeometricPowerNeumannRightInverse
  x
  bound
  κ
  factorBound =
  seriesSumFromFiniteTailBound-neumannRightInverse
    factor
    κ
    factorBound
    (realPower x)
    μ
    tailBound
    μ-antitone
    (λ n → n)
    (λ _ → NatOrder.≤-refl)
    (realGeometricFiniteIdentity x)
  where
  ρ : ℚ⁺
  ρ =
    ratioBound bound

  ρ<1 : radius ρ ℚOrder.< Rational.1ℚ
  ρ<1 =
    ratioBound<1 bound

  μ : ℚ⁺ → ℕ
  μ =
    positiveGeometricPowerModulus ρ ρ<1

  μ-antitone : AntitoneNatModulus μ
  μ-antitone =
    positiveGeometricPowerModulus-antitone ρ ρ<1

  tailBound : TailBound (realPower x) μ
  tailBound =
    realGeometricPowerTailBound x bound

  factor : ℝᶜ
  factor =
    1ᶜ +ᶜ (-ᶜ x)


realGeometricPowerNeumannHasRightInverse :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (1ᶜ +ᶜ (-ᶜ x)) →
  HasRightInverseᶜ (1ᶜ +ᶜ (-ᶜ x))
realGeometricPowerNeumannHasRightInverse
  x
  bound
  κ
  factorBound =
  realGeometricPowerSum x bound ,
  realGeometricPowerNeumannRightInverse
    x
    bound
    κ
    factorBound
