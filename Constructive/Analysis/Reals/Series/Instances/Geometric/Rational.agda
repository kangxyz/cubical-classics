{-

Rational geometric series embedded in the Cauchy reals

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Series.Instances.Geometric.Rational where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.Series.Finite
open import Constructive.Analysis.Reals.Series.Tail
import Constructive.Data.Rationals as Rational

open import Constructive.Analysis.GeometricDecay.Rational


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
