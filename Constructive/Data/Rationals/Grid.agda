{-

Rational grid and half-step lemmas

-}
{-# OPTIONS --safe #-}
module Constructive.Data.Rationals.Grid where

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
open import Constructive.Data.Rationals.Archimedean

positive-half :
  {ε : ℚ} →
  0 ℚOrder.< ε →
  0 ℚOrder.< ε ℚ.· 1/2
positive-half {ε = ε} 0<ε =
  subst (λ q → q ℚOrder.< ε ℚ.· 1/2)
    (ℚ.·AnnihilL 1/2)
    (ℚOrder.<-·o 0 ε 1/2 0<1/2 0<ε)


half+half : (ε : ℚ) → (ε ℚ.· 1/2) ℚ.+ (ε ℚ.· 1/2) ≡ ε
half+half ε =
  sym (ℚ.·DistL+ ε 1/2 1/2) ∙
  (λ i → ε ℚ.· 1/2+1/2≡1 i) ∙
  ℚ.·IdR ε


half<whole :
  {ε : ℚ} →
  0 ℚOrder.< ε →
  ε ℚ.· 1/2 ℚOrder.< ε
half<whole {ε = ε} 0<ε =
  subst (λ r → ε ℚ.· 1/2 ℚOrder.< r)
    (half+half ε)
    (q<q+positive (ε ℚ.· 1/2) (ε ℚ.· 1/2) (positive-half {ε = ε} 0<ε))


grid : ℚ → ℚ → ℕ → ℚ
grid a δ n = a ℚ.+ natMul n δ


grid-zero : (a δ : ℚ) → grid a δ zero ≡ a
grid-zero a δ =
  cong (a ℚ.+_) (natMul-zero δ) ∙
  ℚ.+IdR a


grid-suc :
  (a δ : ℚ) (n : ℕ) →
  grid a δ (suc n) ≡ grid a δ n ℚ.+ δ
grid-suc a δ n =
  cong (a ℚ.+_) (natMul-suc n δ) ∙
  ℚ.+Assoc a (natMul n δ) δ


grid-step< :
  {a δ : ℚ} (n : ℕ) →
  0 ℚOrder.< δ →
  grid a δ n ℚOrder.< grid a δ (suc n)
grid-step< {a = a} {δ = δ} n 0<δ =
  subst (λ r → grid a δ n ℚOrder.< r)
    (sym (grid-suc a δ n))
    (q<q+positive (grid a δ n) δ 0<δ)


grid-two-step :
  (a δ : ℚ) (n : ℕ) →
  grid a δ (suc (suc n)) ≡ grid a δ n ℚ.+ (δ ℚ.+ δ)
grid-two-step a δ n =
  grid-suc a δ (suc n) ∙
  cong (λ r → r ℚ.+ δ) (grid-suc a δ n) ∙
  sym (ℚ.+Assoc (grid a δ n) δ δ)


grid-two-half :
  (a ε : ℚ) (n : ℕ) →
  grid a (ε ℚ.· 1/2) (suc (suc n)) ≡ grid a (ε ℚ.· 1/2) n ℚ.+ ε
grid-two-half a ε n =
  grid-two-step a (ε ℚ.· 1/2) n ∙
  cong (grid a (ε ℚ.· 1/2) n ℚ.+_) (half+half ε)
