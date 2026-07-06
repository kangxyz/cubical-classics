{-

Inverse-facing helpers for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Arithmetic.Inverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax; _,_; Σ≡Prop)
open import Cubical.Data.Sum as Sum using (_⊎_; inl; inr)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; squash₁)

open import Constructive.CauchyReals.Arithmetic.Base
open import Constructive.CauchyReals.Arithmetic.Internal.BoundedReciprocal
open import Constructive.CauchyReals.Arithmetic.Addition
open import Constructive.CauchyReals.Arithmetic.Multiplication
open import Constructive.CauchyReals.Arithmetic.Negation
open import Constructive.CauchyReals.Base
open import Constructive.Analysis.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Instances.Rationals
open ClosenessOf RationalsMetricSpace
open ComputedOf RationalsMetricSpace
open RoundedOf RationalsMetricSpace
open import Constructive.CauchyReals.Order.StrictPositive
import Constructive.Data.Rationals as Rational


HasRightInverseᶜ : ℝᶜ → Type₀
HasRightInverseᶜ x =
  Σ[ y ∈ ℝᶜ ] x ·ᶜ y ≡ 1ᶜ


right-inverse-uniqueᶜ :
  {x y z : ℝᶜ} →
  x ·ᶜ y ≡ 1ᶜ →
  x ·ᶜ z ≡ 1ᶜ →
  y ≡ z
right-inverse-uniqueᶜ {x = x} {y = y} {z = z} xy≡1 xz≡1 =
  sym (mulᶜ-one-left y) ∙
  cong (_·ᶜ y) (sym xz≡1) ∙
  sym (mulᶜ-assoc x z y) ∙
  cong (x ·ᶜ_) (mulᶜ-comm z y) ∙
  mulᶜ-assoc x y z ∙
  cong (_·ᶜ z) xy≡1 ∙
  mulᶜ-one-left z


isPropHasRightInverseᶜ :
  (x : ℝᶜ) →
  isProp (HasRightInverseᶜ x)
isPropHasRightInverseᶜ x a b =
  Σ≡Prop
    (λ y → isSetCompletion (x ·ᶜ y) 1ᶜ)
    (right-inverse-uniqueᶜ
      {x = x}
      {y = a .fst}
      {z = b .fst}
      (a .snd)
      (b .snd))


mulᶜ-neg-left :
  (x y : ℝᶜ) →
  (-ᶜ x) ·ᶜ y ≡ -ᶜ (x ·ᶜ y)
mulᶜ-neg-left x y =
  mulᶜ-comm (-ᶜ x) y ∙
  mulᶜ-neg-right y x ∙
  cong -ᶜ_ (mulᶜ-comm y x)


neg-right-inverseᶜ :
  (x : ℝᶜ) →
  HasRightInverseᶜ (-ᶜ x) →
  HasRightInverseᶜ x
neg-right-inverseᶜ x (y , -x*y≡1) =
  -ᶜ y ,
  mulᶜ-neg-right x y ∙
  sym (mulᶜ-neg-left x y) ∙
  -x*y≡1


rational-positive-right-inverseᶜ :
  (q : ℚ) →
  0ℚ ℚOrder.< q →
  HasRightInverseᶜ (rational q)
rational-positive-right-inverseᶜ q 0<q =
  rationalInv₊ᶜ q 0<q ,
  rationalInv₊ᶜ-right q 0<q


PositiveRightInverseProviderᶜ : Type₀
PositiveRightInverseProviderᶜ =
  (x : ℝᶜ) →
  0ᶜ <ᶜ x →
  HasRightInverseᶜ x


positive-right-inverseᶜ :
  PositiveRightInverseProviderᶜ
positive-right-inverseᶜ x 0<x =
  Prop.rec (isPropHasRightInverseᶜ x) step
    (positiveSepᶜ→merelyBoundedAwayPositiveᶜ x positive-x)
  where
  positive-x : PositiveSepᶜ x
  positive-x =
    subst
      PositiveSepᶜ
      (cong (x +ᶜ_) neg-zero ∙ add-zero-right x)
      0<x
    where
    neg-zero : -ᶜ 0ᶜ ≡ 0ᶜ
    neg-zero =
      neg-rational 0ℚ ∙
      cong rational Rational.neg-zero

  step :
    Σ[ ε ∈ ℚ⁺ ] BoundedAwayPositiveᶜ ε x →
    HasRightInverseᶜ x
  step (ε , x-bound) =
    boundedAwayReciprocalᶜ ε x x-bound ,
    boundedAwayReciprocalᶜ-right ε x x-bound


inv#ᶜ-from-positive :
  PositiveRightInverseProviderᶜ →
  (x : ℝᶜ) →
  x #ᶜ 0ᶜ →
  HasRightInverseᶜ x
inv#ᶜ-from-positive inv₊ x (inl x<0) =
  neg-right-inverseᶜ x
    (inv₊ (-ᶜ x) (negativeᶜ→positive-negᶜ x x<0))
inv#ᶜ-from-positive inv₊ x (inr 0<x) =
  inv₊ x 0<x
