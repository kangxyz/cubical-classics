{-

The Real Numbers ℝ

-}
{-# OPTIONS --safe #-}
module Classical.Analysis.Real.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Literals public
open import Cubical.Data.Rationals using (ℚ)
open import Cubical.Algebra.Ring

open import Classical.Axioms
open import Constructive.Algebra.OrderedCommRing.Morphism
open import Constructive.Algebra.OrderedField.Instances.Rationals
open import Constructive.Algebra.StrictlyOrderedCommRing
open import Constructive.Algebra.StrictlyOrderedCommRing.Morphism
open import Constructive.Algebra.OrderedField
open import Constructive.Algebra.OrderedField.Morphism
open import Classical.Algebra.OrderedField.Completeness
open import Classical.Algebra.OrderedField.Completion


module _ ⦃ 🤖 : Oracle ⦄ where


{-

  The Axioms of Real Numbers

-}

  module AxiomsOfRealNumber where

    open CompleteOrderedField

    -- The real numbers form a complete ordered field, as usual in classical mathematics.

    Reals : Type (ℓ-suc ℓ-zero)
    Reals = CompleteOrderedField ℓ-zero ℓ-zero

    open InclusionFromℚ
    open Completion ℚOrderedField isArchimedeanℚ

    -- Existence and uniqueness of the real numbers

    isContrReals : isContr Reals
    isContrReals .fst = complete
    isContrReals .snd 𝒦 i = uaCompleteOrderedField complete 𝒦 (extend 𝒦 (ℚ→KOrderedFieldHom (𝒦 .fst))) i


{-

  Basics of Real Numbers

-}

  open AxiomsOfRealNumber

  open CompleteOrderedField
  open InclusionFromℚ
  open OrderedCommRingHom


  abstract

    ℝCompleteOrderedField : CompleteOrderedField ℓ-zero ℓ-zero
    ℝCompleteOrderedField = isContrReals .fst

    ℚ→ℝOrderedFieldHom : OrderedFieldHom ℚOrderedField (ℝCompleteOrderedField .fst)
    ℚ→ℝOrderedFieldHom = ℚ→KOrderedFieldHom (ℝCompleteOrderedField .fst)


  ℝ : Type
  ℝ = ℝCompleteOrderedField .fst .fst .fst .fst

  ℚ→ℝ : ℚ → ℝ
  ℚ→ℝ = ℚ→ℝOrderedFieldHom .ring-hom .fst


  -- Natural number and negative integer literals for ℝ

  open StrictlyOrderedCommRingStr (ℝCompleteOrderedField .fst .fst)

  instance
    fromNatℝ : HasFromNat ℝ
    fromNatℝ = record { Constraint = λ _ → Unit ; fromNat = λ n → ℕ→R-Pos n }

  instance
    fromNegℝ : HasFromNeg ℝ
    fromNegℝ = record { Constraint = λ _ → Unit ; fromNeg = λ n → ℕ→R-Neg n }
