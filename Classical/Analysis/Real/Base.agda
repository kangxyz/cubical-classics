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
open import Constructive.Algebra.LinearlyOrderedField.Instances.Rationals
open import Constructive.Algebra.LinearlyOrderedCommRing
import Constructive.Algebra.LinearlyOrderedCommRing.Morphism as LinearMorphism
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.Algebra.LinearlyOrderedField.Morphism
open import Classical.Algebra.OrderedField.Completeness
open import Classical.Algebra.OrderedField.Completion


module _ ⦃ 🤖 : Oracle ⦄ where


{-

  The Axioms of Real Numbers

-}

  module AxiomsOfRealNumber where

    open MacNeilleCompleteOrderedField

    -- The real numbers form a MacNeille complete ordered field.
    -- Classically this is the usual Dedekind-complete ordered field axiom.

    Reals : Type (ℓ-suc ℓ-zero)
    Reals = MacNeilleCompleteOrderedField ℓ-zero ℓ-zero

    open InclusionFromℚ
    open Completion ℚLinearlyOrderedField isArchimedeanℚ

    -- Existence and uniqueness of the real numbers

    isContrReals : isContr Reals
    isContrReals .fst = complete
    isContrReals .snd 𝒦 i = uaMacNeilleCompleteOrderedField complete 𝒦 (extend 𝒦 (ℚ→KLinearlyOrderedFieldHom (𝒦 .fst))) i


{-

  Basics of Real Numbers

-}

  open AxiomsOfRealNumber

  open MacNeilleCompleteOrderedField
  open InclusionFromℚ
  open OrderedCommRingHom


  abstract

    ℝMacNeilleCompleteOrderedField : MacNeilleCompleteOrderedField ℓ-zero ℓ-zero
    ℝMacNeilleCompleteOrderedField = isContrReals .fst

    ℚ→ℝLinearlyOrderedFieldHom : LinearlyOrderedFieldHom ℚLinearlyOrderedField (ℝMacNeilleCompleteOrderedField .fst)
    ℚ→ℝLinearlyOrderedFieldHom = ℚ→KLinearlyOrderedFieldHom (ℝMacNeilleCompleteOrderedField .fst)

    ℚ→ℝOrderedFieldHom :
      OrderedFieldHom
        ℚOrderedField
        (LinearlyOrderedField→OrderedField (ℝMacNeilleCompleteOrderedField .fst))
    ℚ→ℝOrderedFieldHom = ℚ→ℝLinearlyOrderedFieldHom


  ℝ : Type
  ℝ = ℝMacNeilleCompleteOrderedField .fst .fst .fst .fst

  ℚ→ℝ : ℚ → ℝ
  ℚ→ℝ = ℚ→ℝLinearlyOrderedFieldHom .ring-hom .fst


  -- Natural number and negative integer literals for ℝ

  open LinearlyOrderedCommRingStr (ℝMacNeilleCompleteOrderedField .fst .fst)

  instance
    fromNatℝ : HasFromNat ℝ
    fromNatℝ = record { Constraint = λ _ → Unit ; fromNat = λ n → ℕ→R-Pos n }

  instance
    fromNegℝ : HasFromNeg ℝ
    fromNegℝ = record { Constraint = λ _ → Unit ; fromNeg = λ n → ℕ→R-Neg n }
