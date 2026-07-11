{-

Rational finite identities for geometric series

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.GeometricDecay.Rational where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Tactics.CommRingSolver.Reflection
import Constructive.Data.Rationals as Rational

open import Constructive.Analysis.GeometricDecay.Algebra


private
  module RatioSolverHelpers {ℓ : Level} (𝒩 : CommRing ℓ) where
    open CommRingStr (𝒩 .snd)

    power-step :
      (q qn s sn : 𝒩 .fst) →
      (q · qn) · (s · sn) ≡ (q · s) · (qn · sn)
    power-step _ _ _ _ =
      solve! 𝒩

rationalPower :
  ℚ →
  ℕ →
  ℚ
rationalPower r zero =
  Rational.1ℚ
rationalPower r (suc n) =
  r ℚ.· rationalPower r n


rationalRatioPowerTimesPower :
  (r s : ℚ) →
  (0<s : Rational.0ℚ ℚOrder.< s) →
  (n : ℕ) →
  rationalPower (r ℚ.· Rational.posInv s 0<s) n ℚ.·
    rationalPower s n
  ≡
  rationalPower r n
rationalRatioPowerTimesPower r s 0<s zero =
  ℚ.·IdL Rational.1ℚ
rationalRatioPowerTimesPower r s 0<s (suc n) =
  RatioSolverHelpers.power-step
    ℚCommRing
    q
    (rationalPower q n)
    s
    (rationalPower s n) ∙
  cong₂
    (λ x y → x ℚ.· y)
    q*s≡r
    (rationalRatioPowerTimesPower r s 0<s n)
  where
  q : ℚ
  q =
    r ℚ.· Rational.posInv s 0<s

  q*s≡r : q ℚ.· s ≡ r
  q*s≡r =
    sym (ℚ.·Assoc r (Rational.posInv s 0<s) s) ∙
    cong (r ℚ.·_) (Rational.posInv-left s 0<s) ∙
    ℚ.·IdR r


rationalGeometricPartialSumℚ :
  ℚ →
  ℕ →
  ℚ
rationalGeometricPartialSumℚ r zero =
  Rational.0ℚ
rationalGeometricPartialSumℚ r (suc n) =
  rationalGeometricPartialSumℚ r n ℚ.+ rationalPower r n


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


rationalGeometricSegmentSumℚ :
  ℚ →
  ℕ →
  ℕ →
  ℚ
rationalGeometricSegmentSumℚ r m zero =
  Rational.0ℚ
rationalGeometricSegmentSumℚ r m (suc k) =
  rationalPower r m ℚ.+ rationalGeometricSegmentSumℚ r (suc m) k


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
