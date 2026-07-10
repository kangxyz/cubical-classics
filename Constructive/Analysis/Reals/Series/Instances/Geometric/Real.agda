{-

Real geometric series from explicit power bounds

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Series.Instances.Geometric.Real where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat as Nat
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (fst)

open import Constructive.Analysis.GeometricDecay
open import Constructive.Analysis.GeometricDecay.Algebra
open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Modulus using (AntitoneNatModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.CommRing
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Estimates
  using (bounded-byᶜ-abs≤rational)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Inverse
  using (HasRightInverseᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Metric
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using (absᶜ ; neg-zeroᶜ)
open import Constructive.Analysis.Reals.Series.Cauchy
open import Constructive.Analysis.Reals.Series.Comparison
open import Constructive.Analysis.Reals.Series.Finite
open import Constructive.Analysis.Reals.Series.Tail
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
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


realPower :
  ℝᶜ →
  ℕ →
  ℝᶜ
realPower x zero =
  1ᶜ
realPower x (suc n) =
  x ·ᶜ realPower x n


realPower-zero :
  (x : ℝᶜ) →
  realPower x zero ≡ 1ᶜ
realPower-zero x =
  refl


realPower-suc :
  (x : ℝᶜ) →
  (n : ℕ) →
  realPower x (suc n) ≡ x ·ᶜ realPower x n
realPower-suc x n =
  refl


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
  realGeometricPowerBound-one :
    (x : ℝᶜ) →
    BoundedByᶜ 1⁺ (realPower x zero)
  realGeometricPowerBound-one x =
    rational-closed-bound→boundedᶜ
      1⁺
      Rational.1ℚ
      (rational-closed-boundᶜ
        (Rational.≤-refl Rational.1ℚ)
        (Rational.<→≤
          {p = Rational.-1ℚ}
          {q = Rational.1ℚ}
          (ℚOrder.isTrans<
            Rational.-1ℚ
            Rational.0ℚ
            Rational.1ℚ
            Rational.-1<0
            Rational.0<1)))


realPowerBoundsFromBound :
  (ρ : ℚ⁺) →
  (x : ℝᶜ) →
  BoundedByᶜ ρ x →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower x n)
realPowerBoundsFromBound ρ x x-bound zero =
  realGeometricPowerBound-one x
realPowerBoundsFromBound ρ x x-bound (suc n) =
  bounded-byᶜ-mul
    ρ
    (positivePower ρ n)
    x
    (realPower x n)
    x-bound
    (realPowerBoundsFromBound ρ x x-bound n)


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
      absᶜ (drop m (realPower x) n) ≤ᶜ
      drop m (positiveGeometricTerm ρ) n
    termMajorized m n =
      subst2
        (λ u v → absᶜ u ≤ᶜ v)
        (sym (drop-index m (realPower x) n))
        (sym (drop-index m (positiveGeometricTerm ρ) n))
        (bounded-byᶜ-abs≤rational
          (realPowerBoundsFromBound
            ρ
            x
            (termBound bound)
            (m Nat.+ n)))

    majorantNonnegative :
      (m n : ℕ) →
      0ᶜ ≤ᶜ drop m (positiveGeometricTerm ρ) n
    majorantNonnegative m n =
      subst
        (λ v → 0ᶜ ≤ᶜ v)
        (sym (drop-index m (positiveGeometricTerm ρ) n))
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
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    product
    1ᶜ
    closeAt
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

  product : ℝᶜ
  product =
    factor ·ᶜ realGeometricPowerSum x bound

  closeAt :
    (ε : ℚ⁺) →
    product ∼[ ε ] 1ᶜ
  closeAt ε =
    subst
      (λ precision → product ∼[ precision ] 1ᶜ)
      (half⁺+half⁺≡ ε)
      (MetricSpace.close-triangle
        CauchyRealsMetricSpace
        product∼partial
        partial∼one)
    where
    η : ℚ⁺
    η =
      half⁺ ε

    productPrecision : ℚ⁺
    productPrecision =
      quarter⁺
        (half⁺
          (fst (mulᶜ-continuous-right-with-bound κ factor factorBound) η))

    tailPrecision : ℚ⁺
    tailPrecision =
      half⁺ η

    productIndex : ℕ
    productIndex =
      μ productPrecision

    tailIndex : ℕ
    tailIndex =
      μ tailPrecision

    n : ℕ
    n =
      productIndex Nat.+ tailIndex

    productIndex≤n : NatOrder._≤_ productIndex n
    productIndex≤n =
      tailIndex , Nat.+-comm tailIndex productIndex

    tailIndex≤n : NatOrder._≤_ tailIndex n
    tailIndex≤n =
      productIndex , refl

    product∼partial :
      product ∼[ η ] factor ·ᶜ partialSum (realPower x) n
    product∼partial =
      seriesSumFromFiniteTailBound-mul-left-convergesAt
        factor
        κ
        factorBound
        (realPower x)
        μ
        tailBound
        μ-antitone
        η
        n
        productIndex≤n

    powerTailBound :
      BoundedByᶜ tailPrecision (tailSum (realPower x) n (suc zero))
    powerTailBound =
      tailBound tailPrecision n (suc zero) tailIndex≤n

    powerBound :
      BoundedByᶜ tailPrecision (realPower x n)
    powerBound =
      subst
        (BoundedByᶜ tailPrecision)
        (tailSum-one (realPower x) n)
        powerTailBound

    power∼zero :
      realPower x n ∼[ η ] 0ᶜ
    power∼zero =
      bounded-byᶜ-close-zero
        tailPrecision
        η
        (realPower x n)
        powerBound
        (half< η)

    negPower∼zero :
      (-ᶜ realPower x n) ∼[ η ] 0ᶜ
    negPower∼zero =
      subst
        (λ z → (-ᶜ realPower x n) ∼[ η ] z)
        neg-zeroᶜ
        (neg-close power∼zero)

    oneMinusPower∼one :
      (1ᶜ +ᶜ (-ᶜ realPower x n)) ∼[ η ] 1ᶜ
    oneMinusPower∼one =
      subst
        (λ z → (1ᶜ +ᶜ (-ᶜ realPower x n)) ∼[ η ] z)
        (add-zero-right 1ᶜ)
        (add-close-right 1ᶜ negPower∼zero)

    partial∼one :
      factor ·ᶜ partialSum (realPower x) n ∼[ η ] 1ᶜ
    partial∼one =
      subst
        (λ z → z ∼[ η ] 1ᶜ)
        (sym (realGeometricFiniteIdentity x n))
        oneMinusPower∼one


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
