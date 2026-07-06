{-

Rational finite identities for geometric series

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Series.Instances.Geometric.Rational where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax)
import Cubical.Data.Sum as Sum
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Metric.Instances.CauchyReals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.Series
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open import Constructive.Analysis.Reals.Series.Instances.Geometric.Algebra

rationalPower :
  ℚ →
  ℕ →
  ℚ
rationalPower r zero =
  Rational.1ℚ
rationalPower r (suc n) =
  r ℚ.· rationalPower r n


rationalPower-zero :
  (r : ℚ) →
  rationalPower r zero ≡ Rational.1ℚ
rationalPower-zero r =
  refl


rationalPower-suc :
  (r : ℚ) →
  (n : ℕ) →
  rationalPower r (suc n) ≡ r ℚ.· rationalPower r n
rationalPower-suc r n =
  refl


realRationalPower :
  ℚ →
  ℕ →
  ℝᶜ
realRationalPower r n =
  rational (rationalPower r n)


rationalGeometricTerm :
  ℚ →
  ℕ →
  ℝᶜ
rationalGeometricTerm =
  realRationalPower


rationalGeometricPartialSumℚ :
  ℚ →
  ℕ →
  ℚ
rationalGeometricPartialSumℚ r zero =
  Rational.0ℚ
rationalGeometricPartialSumℚ r (suc n) =
  rationalGeometricPartialSumℚ r n ℚ.+ rationalPower r n


rationalGeometricPartialSumℚ-zero :
  (r : ℚ) →
  rationalGeometricPartialSumℚ r zero ≡ Rational.0ℚ
rationalGeometricPartialSumℚ-zero r =
  refl


rationalGeometricPartialSumℚ-suc :
  (r : ℚ) →
  (n : ℕ) →
  rationalGeometricPartialSumℚ r (suc n) ≡
  rationalGeometricPartialSumℚ r n ℚ.+ rationalPower r n
rationalGeometricPartialSumℚ-suc r n =
  refl


rationalGeometricFiniteIdentity :
  (r : ℚ) →
  (n : ℕ) →
  (Rational.1ℚ ℚ.- r) ℚ.· rationalGeometricPartialSumℚ r n ≡
  Rational.1ℚ ℚ.- rationalPower r n
rationalGeometricFiniteIdentity r zero =
  SolverHelpers.geometric-zero ℚCommRing r
rationalGeometricFiniteIdentity r (suc n) =
  SolverHelpers.geometric-distrib ℚCommRing r S p ∙
  cong
    (λ q → q ℚ.+ ((Rational.1ℚ ℚ.- r) ℚ.· p))
    (rationalGeometricFiniteIdentity r n) ∙
  SolverHelpers.geometric-step ℚCommRing r p
  where
  S : ℚ
  S =
    rationalGeometricPartialSumℚ r n

  p : ℚ
  p =
    rationalPower r n


rationalGeometricPartialSumᶜ :
  ℚ →
  ℕ →
  ℝᶜ
rationalGeometricPartialSumᶜ r n =
  rational (rationalGeometricPartialSumℚ r n)


rationalGeometricFiniteIdentityᶜ :
  (r : ℚ) →
  (n : ℕ) →
  (1ᶜ +ᶜ (-ᶜ rational r)) ·ᶜ rationalGeometricPartialSumᶜ r n ≡
  1ᶜ +ᶜ (-ᶜ rational (rationalPower r n))
rationalGeometricFiniteIdentityᶜ r n =
  cong
    (λ z → z ·ᶜ rationalGeometricPartialSumᶜ r n)
    (add-rational Rational.1ℚ (ℚ.- r)) ∙
  mulᶜ-rational-rational
    (Rational.1ℚ ℚ.- r)
    (rationalGeometricPartialSumℚ r n) ∙
  cong rational (rationalGeometricFiniteIdentity r n) ∙
  sym (add-rational Rational.1ℚ (ℚ.- rationalPower r n))


rationalGeometricSegmentSumℚ :
  ℚ →
  ℕ →
  ℕ →
  ℚ
rationalGeometricSegmentSumℚ r m zero =
  Rational.0ℚ
rationalGeometricSegmentSumℚ r m (suc k) =
  rationalPower r m ℚ.+ rationalGeometricSegmentSumℚ r (suc m) k


rationalGeometricSegmentSumᶜ :
  ℚ →
  ℕ →
  ℕ →
  ℝᶜ
rationalGeometricSegmentSumᶜ r m k =
  rational (rationalGeometricSegmentSumℚ r m k)


rationalGeometricSegmentTailSum :
  (r : ℚ) →
  (m k : ℕ) →
  tailSum (rationalGeometricTerm r) m k ≡
  rationalGeometricSegmentSumᶜ r m k
rationalGeometricSegmentTailSum r m zero =
  refl
rationalGeometricSegmentTailSum r m (suc k) =
  tailSum-suc-start (rationalGeometricTerm r) m k ∙
  cong
    (rationalGeometricTerm r m +ᶜ_)
    (rationalGeometricSegmentTailSum r (suc m) k) ∙
  add-rational
    (rationalPower r m)
    (rationalGeometricSegmentSumℚ r (suc m) k)


rationalGeometricSegmentFiniteIdentity :
  (r : ℚ) →
  (m k : ℕ) →
  (Rational.1ℚ ℚ.- r) ℚ.· rationalGeometricSegmentSumℚ r m k ≡
  rationalPower r m ℚ.- rationalPower r (m Nat.+ k)
rationalGeometricSegmentFiniteIdentity r m zero =
  SolverHelpers.segment-zero ℚCommRing r (rationalPower r m) ∙
  cong
    (λ p → rationalPower r m ℚ.- p)
    (cong (rationalPower r) (sym (Nat.+-zero m)))
rationalGeometricSegmentFiniteIdentity r m (suc k) =
  SolverHelpers.segment-distrib ℚCommRing r p S ∙
  cong
    (((Rational.1ℚ ℚ.- r) ℚ.· p) ℚ.+_)
    (rationalGeometricSegmentFiniteIdentity r (suc m) k) ∙
  SolverHelpers.segment-step ℚCommRing r p t ∙
  cong
    (λ q → p ℚ.- q)
    (cong (rationalPower r) (sym (Nat.+-suc m k)))
  where
  p : ℚ
  p =
    rationalPower r m

  S : ℚ
  S =
    rationalGeometricSegmentSumℚ r (suc m) k

  t : ℚ
  t =
    rationalPower r (suc m Nat.+ k)
