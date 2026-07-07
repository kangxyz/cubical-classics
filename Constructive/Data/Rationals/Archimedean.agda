{-

Archimedean and natural-multiple lemmas for Cubical rationals

-}
{-# OPTIONS --safe #-}
module Constructive.Data.Rationals.Archimedean where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Int as ℤ using (pos)
import Cubical.Data.Int.Order as ℤOrder
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.NatPlusOne using (ℕ₊₁)
open import Cubical.Data.NatPlusOne.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁ ; ∣_∣₁)
open import Cubical.Relation.Nullary using (Dec)
open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection
open import Constructive.Algebra.LinearlyOrderedCommRing
open import Constructive.Algebra.LinearlyOrderedCommRing.Instances.Rationals
  using (ℚLinearlyOrderedCommRing)
import Constructive.Algebra.LinearlyOrderedCommRing.Instances.Rationals.Archimedean as ℚArch
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.Algebra.LinearlyOrderedField.Instances.Rationals
  using (ℚLinearlyOrderedField)


private
  module ℚLOR = LinearlyOrderedCommRingStr ℚLinearlyOrderedCommRing
  module ℚOF = LinearlyOrderedFieldStr ℚLinearlyOrderedField
  ℚCommRing = LinearlyOrderedCommRing→CommRing ℚLinearlyOrderedCommRing

  module RingSolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    mul-error-split :
      (lx ux ly uy : 𝓡 .fst) →
      ux · uy ≡ lx · ly + (((ux - lx) · uy) + (lx · (uy - ly)))
    mul-error-split _ _ _ _ = solve! 𝓡

open import Constructive.Data.Rationals.Base
open import Constructive.Data.Rationals.Multiplication

natMul : ℕ → ℚ → ℚ
natMul = ℚLOR._⋆_


archimedean :
  (q ε : ℚ) →
  0 ℚOrder.< ε →
  Σ[ n ∈ ℕ ] q ℚOrder.< natMul n ε
archimedean = ℚArch.isArchimedeanℚ


unitFraction : ℕ → ℚ
unitFraction n =
  ℚOF._/_ 1ℚ (1+ n)


unitFraction-positive :
  (n : ℕ) →
  0 ℚOrder.< unitFraction n
unitFraction-positive n =
  ℚOF.·-Pres>0
    {x = 1ℚ}
    {y = ℚOF.1/ (1+ n)}
    0<1
    (ℚOF.1/n>0 (1+ n))


divideBySuc : ℚ → ℕ → ℚ
divideBySuc q n =
  ℚOF._/_ q (1+ n)


divideBySuc-positive :
  {q : ℚ} →
  0ℚ ℚOrder.< q →
  (n : ℕ) →
  0ℚ ℚOrder.< divideBySuc q n
divideBySuc-positive {q = q} 0<q n =
  mul-positive
    {a = q}
    {b = ℚOF.1/ (1+ n)}
    0<q
    (ℚOF.1/n>0 (1+ n))


divideBySuc-as-unitFraction :
  (q : ℚ) →
  (n : ℕ) →
  divideBySuc q n ≡ q ℚ.· unitFraction n
divideBySuc-as-unitFraction q n =
  cong (q ℚ.·_) (sym (ℚ.·IdL (ℚOF.1/ (1+ n))))


natMul-divideBySuc :
  (q : ℚ) →
  (n : ℕ) →
  natMul (suc n) (divideBySuc q n) ≡ q
natMul-divideBySuc q n =
  ℚOF.·-/-lInv q (1+ n)


natMul-unitFraction :
  (n : ℕ) →
  natMul (suc n) (unitFraction n) ≡ 1ℚ
natMul-unitFraction n =
  cong (natMul (suc n)) (sym divideBySuc≡unit) ∙
  natMul-divideBySuc 1ℚ n
  where
  divideBySuc≡unit :
    divideBySuc 1ℚ n ≡ unitFraction n
  divideBySuc≡unit =
    divideBySuc-as-unitFraction 1ℚ n ∙
    ℚ.·IdL (unitFraction n)


abstract
  archimedean-unit-fraction :
    (ε : ℚ) →
    0 ℚOrder.< ε →
    Σ[ n ∈ ℕ ] unitFraction n ℚOrder.< ε
  archimedean-unit-fraction ε 0<ε with
      isArchimedean→isArchimedeanInv
        ℚLinearlyOrderedField
        ℚArch.isArchimedeanℚ
        ε
        1ℚ
        0<ε
        0<1
  ... | 1+ n , unit<ε =
    n , unit<ε


natMul-zero : (ε : ℚ) → natMul zero ε ≡ 0
natMul-zero = ℚLOR.0⋆q≡0


natMul-suc : (n : ℕ) (ε : ℚ) → natMul (suc n) ε ≡ natMul n ε ℚ.+ ε
natMul-suc = ℚLOR.sucn⋆q≡n⋆q+q


natMul-one : (ε : ℚ) → natMul (suc zero) ε ≡ ε
natMul-one ε =
  natMul-suc zero ε ∙
  cong (λ r → r ℚ.+ ε) (natMul-zero ε) ∙
  ℚ.+IdL ε


natMul-step< :
  (n : ℕ) {ε : ℚ} →
  0 ℚOrder.< ε →
  natMul n ε ℚOrder.< natMul (suc n) ε
natMul-step< n {ε = ε} 0<ε =
  subst (λ r → natMul n ε ℚOrder.< r)
    (sym (natMul-suc n ε))
    (q<q+positive (natMul n ε) ε 0<ε)


natMul-step≤ :
  (n : ℕ) {ε : ℚ} →
  0 ℚOrder.< ε →
  natMul n ε ℚOrder.≤ natMul (suc n) ε
natMul-step≤ n {ε = ε} 0<ε =
  ℚOrder.<Weaken≤
    (natMul n ε)
    (natMul (suc n) ε)
    (natMul-step< n 0<ε)


shift-bound-suc :
  (p ε : ℚ) (n : ℕ) →
  p ℚ.+ natMul (suc (suc n)) ε ≡
  (p ℚ.+ ε) ℚ.+ natMul (suc n) ε
shift-bound-suc p ε n =
  cong (p ℚ.+_) (natMul-suc (suc n) ε) ∙
  cong (p ℚ.+_) (ℚ.+Comm (natMul (suc n) ε) ε) ∙
  ℚ.+Assoc p ε (natMul (suc n) ε)


natMul-suc-positive :
  (n : ℕ) {ε : ℚ} →
  0 ℚOrder.< ε →
  0 ℚOrder.< natMul (suc n) ε
natMul-suc-positive n 0<ε = ℚLOR.sucn⋆q>0 n _ 0<ε


natMul-nonnegative :
  (n : ℕ) {ε : ℚ} →
  0 ℚOrder.< ε →
  0 ℚOrder.≤ natMul n ε
natMul-nonnegative n 0<ε = ℚLOR.n⋆q≥0 n _ 0<ε


natMul-mono-≤ :
  (n m : ℕ) {ε : ℚ} →
  0 ℚOrder.< ε →
  NatOrder._≤_ n m →
  natMul n ε ℚOrder.≤ natMul m ε
natMul-mono-≤ zero m {ε = ε} 0<ε _ =
  subst
    (λ q → q ℚOrder.≤ natMul m ε)
    (sym (natMul-zero ε))
    (natMul-nonnegative m 0<ε)
natMul-mono-≤ (suc n) zero 0<ε sn≤0 =
  Empty.rec (NatOrder.¬-<-zero sn≤0)
natMul-mono-≤ (suc n) (suc m) {ε = ε} 0<ε sn≤sm =
  subst2
    ℚOrder._≤_
    (sym (natMul-suc n ε))
    (sym (natMul-suc m ε))
    (ℚOrder.≤Monotone+
      (natMul n ε)
      (natMul m ε)
      ε ε
      (natMul-mono-≤ n m 0<ε (NatOrder.pred-≤-pred sn≤sm))
      (≤-refl ε))


natMul-factor-mono-≤ :
  (n : ℕ) →
  {ε δ : ℚ} →
  ε ℚOrder.≤ δ →
  natMul n ε ℚOrder.≤ natMul n δ
natMul-factor-mono-≤ zero {ε = ε} {δ = δ} ε≤δ =
  subst2
    ℚOrder._≤_
    (sym (natMul-zero ε))
    (sym (natMul-zero δ))
    (≤-refl 0ℚ)
natMul-factor-mono-≤ (suc n) {ε = ε} {δ = δ} ε≤δ =
  subst2
    ℚOrder._≤_
    (sym (natMul-suc n ε))
    (sym (natMul-suc n δ))
    (ℚOrder.≤Monotone+
      (natMul n ε)
      (natMul n δ)
      ε δ
      (natMul-factor-mono-≤ n ε≤δ)
      ε≤δ)


natMul-mul-left :
  (n : ℕ) →
  (a b : ℚ) →
  natMul n (a ℚ.· b) ≡ a ℚ.· natMul n b
natMul-mul-left zero a b =
  natMul-zero (a ℚ.· b) ∙
  sym (ℚ.·AnnihilR a) ∙
  cong (a ℚ.·_) (sym (natMul-zero b))
natMul-mul-left (suc n) a b =
  natMul-suc n (a ℚ.· b) ∙
  cong (λ q → q ℚ.+ (a ℚ.· b)) (natMul-mul-left n a b) ∙
  sym (ℚ.·DistL+ a (natMul n b) b) ∙
  cong (a ℚ.·_) (sym (natMul-suc n b))
