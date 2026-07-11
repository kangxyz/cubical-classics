{-

Finite binomial algebra for re-centering power series.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Recenter.Binomial where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps as RingBigOps
import Cubical.Algebra.CommRing.BinomialThm as RingBinomial
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.FinData.Base using (Fin ; FinVec)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _∸_)
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Structures
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Power
  using (realPower)
import Constructive.Data.Rationals as Rational


module CRBinomial =
  RingBinomial.BinomialThm CauchyRealsCommRing

module CRPower =
  Exponentiation CauchyRealsCommRing

module CRSum =
  RingBigOps.Sum (CommRing→Ring CauchyRealsCommRing)


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    natMul-add-step :
      (a b one : 𝓡 .fst) →
      (a + b) + one ≡ (a + one) + b
    natMul-add-step _ _ _ = solve! 𝓡


binomialℕ :
  ℕ →
  ℕ →
  ℕ
binomialℕ =
  Nat._choose_


binomialᶜ :
  ℕ →
  ℕ →
  ℝᶜ
binomialᶜ =
  CRBinomial._choose_


binomialℕ-above-diagonal :
  (n k : ℕ) →
  binomialℕ n (suc (n Nat.+ k)) ≡ zero
binomialℕ-above-diagonal zero k =
  refl
binomialℕ-above-diagonal (suc n) k =
  cong₂
    Nat._+_
    (subst
      (λ m → binomialℕ n (suc m) ≡ zero)
      (Nat.+-suc n k)
      (binomialℕ-above-diagonal n (suc k)))
    (binomialℕ-above-diagonal n k)


binomialℕ-diagonal :
  (n : ℕ) →
  binomialℕ n n ≡ suc zero
binomialℕ-diagonal zero =
  refl
binomialℕ-diagonal (suc n) =
  cong₂
    Nat._+_
    (subst
      (λ m → binomialℕ n m ≡ zero)
      (cong suc (Nat.+-zero n))
      (binomialℕ-above-diagonal n zero))
    (binomialℕ-diagonal n)


natMul-one-+ :
  (m n : ℕ) →
  Rational.natMul (m Nat.+ n) Rational.1ℚ ≡
  Rational.natMul m Rational.1ℚ ℚ.+
  Rational.natMul n Rational.1ℚ
natMul-one-+ zero n =
  sym (ℚ.+IdL (Rational.natMul n Rational.1ℚ)) ∙
  cong
    (λ r → r ℚ.+ Rational.natMul n Rational.1ℚ)
    (sym (Rational.natMul-zero Rational.1ℚ))
natMul-one-+ (suc m) n =
  Rational.natMul-suc (m Nat.+ n) Rational.1ℚ ∙
  cong (λ r → r ℚ.+ Rational.1ℚ) (natMul-one-+ m n) ∙
  SolverHelpers.natMul-add-step
    ℚCommRing
    (Rational.natMul m Rational.1ℚ)
    (Rational.natMul n Rational.1ℚ)
    Rational.1ℚ ∙
  cong
    (λ r → r ℚ.+ Rational.natMul n Rational.1ℚ)
    (sym (Rational.natMul-suc m Rational.1ℚ))


binomialᶜ-natural :
  (n k : ℕ) →
  binomialᶜ n k ≡
  rational (Rational.natMul (binomialℕ n k) Rational.1ℚ)
binomialᶜ-natural zero zero =
  cong rational (sym (Rational.natMul-one Rational.1ℚ))
binomialᶜ-natural zero (suc k) =
  cong rational (sym (Rational.natMul-zero Rational.1ℚ))
binomialᶜ-natural (suc n) zero =
  cong rational (sym (Rational.natMul-one Rational.1ℚ))
binomialᶜ-natural (suc n) (suc k) =
  cong₂ _+ᶜ_
    (binomialᶜ-natural n (suc k))
    (binomialᶜ-natural n k) ∙
  add-rational left right ∙
  cong rational (sym (natMul-one-+ leftℕ rightℕ))
  where
  leftℕ : ℕ
  leftℕ =
    binomialℕ n (suc k)

  rightℕ : ℕ
  rightℕ =
    binomialℕ n k

  left : ℚ
  left =
    Rational.natMul leftℕ Rational.1ℚ

  right : ℚ
  right =
    Rational.natMul rightℕ Rational.1ℚ




binomialᶜ-diagonal :
  (n : ℕ) →
  binomialᶜ n n ≡ 1ᶜ
binomialᶜ-diagonal n =
  binomialᶜ-natural n n ∙
  cong
    (λ m → rational (Rational.natMul m Rational.1ℚ))
    (binomialℕ-diagonal n) ∙
  cong rational (Rational.natMul-one Rational.1ℚ)








ringPowerᶜ≡realPower :
  (x : ℝᶜ) →
  (n : ℕ) →
  CRPower._^_ x n ≡ realPower x n
ringPowerᶜ≡realPower x zero =
  refl
ringPowerᶜ≡realPower x (suc n) =
  cong (x ·ᶜ_) (ringPowerᶜ≡realPower x n)


binomialVecᶜ :
  (n : ℕ) →
  ℝᶜ →
  ℝᶜ →
  FinVec ℝᶜ (suc n)
binomialVecᶜ n x y i =
  binomialᶜ n (Fin.toℕ i) ·ᶜ
  realPower x (Fin.toℕ i) ·ᶜ
  realPower y (n ∸ Fin.toℕ i)


ringBinomialVec≡binomialVecᶜ :
  (n : ℕ) →
  (x y : ℝᶜ) →
  (i : Fin (suc n)) →
  CRBinomial.BinomialVec n x y i ≡
  binomialVecᶜ n x y i
ringBinomialVec≡binomialVecᶜ n x y i =
  cong₂
    (λ p q →
      binomialᶜ n (Fin.toℕ i) ·ᶜ p ·ᶜ q)
    (ringPowerᶜ≡realPower x (Fin.toℕ i))
    (ringPowerᶜ≡realPower y (n ∸ Fin.toℕ i))


binomialTheoremᶜ :
  (n : ℕ) →
  (x y : ℝᶜ) →
  realPower (x +ᶜ y) n ≡
  CRSum.∑ (binomialVecᶜ n x y)
binomialTheoremᶜ n x y =
  sym (ringPowerᶜ≡realPower (x +ᶜ y) n) ∙
  CRBinomial.BinomialThm n x y ∙
  CRSum.∑Ext (ringBinomialVec≡binomialVecᶜ n x y)
