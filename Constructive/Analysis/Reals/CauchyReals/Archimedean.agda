{-

Archimedean property for HoTT Cauchy reals

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.CauchyReals.Archimedean where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

import Constructive.Algebra.OrderedCommRing.Archimedean as OrderedArch
import Constructive.Algebra.OrderedCommRing.Properties as OrderedProperties
open import Constructive.Algebra.LinearlyOrderedCommRing.Instances.Rationals
  using (ℚLinearlyOrderedCommRing)
open import Constructive.Algebra.LinearlyOrderedCommRing.Instances.Rationals.Archimedean
  using (isArchimedeanℚ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarOrder
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Order.Density
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
open import Constructive.Data.PositiveRationals


module ℚOrdered =
  OrderedProperties.OrderedCommRingTheory (ℚLinearlyOrderedCommRing .fst)

module CauchyOrdered =
  OrderedProperties.OrderedCommRingTheory CauchyRealsOrderedCommRing


private
  neg-zeroᶜ : -ᶜ 0ᶜ ≡ 0ᶜ
  neg-zeroᶜ =
    inverse-unique-right 0ᶜ 0ᶜ (add-zero-right 0ᶜ)

  diff-zero-rightᶜ : (x : ℝᶜ) → x +ᶜ (-ᶜ 0ᶜ) ≡ x
  diff-zero-rightᶜ x =
    cong (x +ᶜ_) neg-zeroᶜ ∙
    add-zero-right x

  nat-rational :
    (n : ℕ) →
    CauchyOrdered.ℕ→R-Pos n ≡ rational (ℚOrdered.ℕ→R-Pos n)
  nat-rational zero =
    refl
  nat-rational (suc zero) =
    refl
  nat-rational (suc (suc n)) =
    cong (1ᶜ +ᶜ_) (nat-rational (suc n)) ∙
    add-rational 1ℚ (ℚOrdered.ℕ→R-Pos (suc n))

  nat-scalar :
    (n : ℕ) (x : ℝᶜ) →
    CauchyOrdered._⋆_ n x ≡ scalarMulᶜ (ℚOrdered.ℕ→R-Pos n) x
  nat-scalar n x =
    cong (_·ᶜ x) (nat-rational n) ∙
    mulᶜ-rational-left (ℚOrdered.ℕ→R-Pos n) x

  nat-scalar-rational :
    (n : ℕ) (q : ℚ) →
    CauchyOrdered._⋆_ n (rational q) ≡
    rational (ℚOrdered._⋆_ n q)
  nat-scalar-rational n q =
    nat-scalar n (rational q) ∙
    scalarMulᶜ-rational (ℚOrdered.ℕ→R-Pos n) q

  nat-scalar-mono :
    (n : ℕ) {x y : ℝᶜ} →
    x ≤ᶜ y →
    CauchyOrdered._⋆_ n x ≤ᶜ CauchyOrdered._⋆_ n y
  nat-scalar-mono n {x = x} {y = y} x≤y =
    subst2
      _≤ᶜ_
      (sym (nat-scalar n x))
      (sym (nat-scalar n y))
      (scalarMulᶜ-pres≤ᶜ-nonnegative
        (ℚOrdered.ℕ→R-Pos n)
        (ℚOrdered.ℕ→R-Pos≥0 n)
        x≤y)


isArchimedean∥∥CauchyRealsOrderedCommRing :
  OrderedArch.isArchimedean∥∥ CauchyRealsOrderedCommRing
isArchimedean∥∥CauchyRealsOrderedCommRing q ε ε>0 =
  Prop.rec2 squash₁ step ε>0 (rational-approximation q θ)
  where
  θ : ℚ⁺
  θ =
    half⁺ 1⁺

  θ<1 : θ <⁺ 1⁺
  θ<1 =
    half< 1⁺

  step :
    Σ[ δ ∈ ℚ⁺ ] rational (radius δ) ≤ᶜ (ε +ᶜ (-ᶜ 0ᶜ)) →
    Σ[ p ∈ ℚ ] q ∼[ θ ] rational p →
    ∥ Σ[ n ∈ ℕ ] CauchyOrdered._⋆_ n ε >ᶜ q ∥₁
  step (δ , δ≤ε-0) (p , q∼p) =
    ∣ n , q<nε ∣₁
    where
    δ≤ε : rational (radius δ) ≤ᶜ ε
    δ≤ε =
      subst
        (λ y → rational (radius δ) ≤ᶜ y)
        (diff-zero-rightᶜ ε)
        δ≤ε-0

    upper : ℚ
    upper =
      p ℚ.+ radius 1⁺

    q≤upper : q ≤ᶜ rational upper
    q≤upper =
      close-rational-upper-bound q p θ 1⁺ θ<1 q∼p

    archℚ : Σ[ m ∈ ℕ ] ℚOrdered._⋆_ m (radius δ) ℚOrder.> upper
    archℚ =
      isArchimedeanℚ upper (radius δ) (δ .snd)

    n : ℕ
    n =
      archℚ .fst

    upper<nδ : rational upper <ᶜ rational (ℚOrdered._⋆_ n (radius δ))
    upper<nδ =
      <ℚ→<ᶜ (archℚ .snd)

    nδ≤nε : rational (ℚOrdered._⋆_ n (radius δ)) ≤ᶜ CauchyOrdered._⋆_ n ε
    nδ≤nε =
      subst
        (λ x → x ≤ᶜ CauchyOrdered._⋆_ n ε)
        (nat-scalar-rational n (radius δ))
        (nat-scalar-mono n δ≤ε)

    q<nδ : q <ᶜ rational (ℚOrdered._⋆_ n (radius δ))
    q<nδ =
      ≤ᶜ-<ᶜ-trans q (rational upper) (rational (ℚOrdered._⋆_ n (radius δ)))
        q≤upper
        upper<nδ

    q<nε : q <ᶜ CauchyOrdered._⋆_ n ε
    q<nε =
      <ᶜ-≤ᶜ-trans q (rational (ℚOrdered._⋆_ n (radius δ))) (CauchyOrdered._⋆_ n ε)
        q<nδ
        nδ≤nε
