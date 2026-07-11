{-

The rational instance of constructive Dedekind completions

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.DedekindReals where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing using (CommRing)
open import Cubical.Algebra.OrderedCommRing using (OrderedCommRing)
open import Cubical.Data.Rationals using (ℚ)

import Constructive.Algebra.OrderedHeytingField.Base as OrderedHeytingField
open import Constructive.Algebra.LinearlyOrderedField.Instances.Rationals
  using (ℚLinearlyOrderedField ; ℚArchimedeanLinearlyOrderedField)
import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic as CompletionArithmetic
import Constructive.Analysis.Completions.DedekindCompletion.Base as CompletionBase

private
  variable
    ℓ : Level


  baseField = ℚLinearlyOrderedField

  archimedeanBaseField = ℚArchimedeanLinearlyOrderedField

  module RationalCompletion = CompletionBase.CompletionBase baseField


ℝᴰ : (ℓ : Level) → Type (ℓ-suc ℓ)
ℝᴰ = RationalCompletion.DedekindCompletion

ℚ→ℝᴰ : (ℓ : Level) → ℚ → ℝᴰ ℓ
ℚ→ℝᴰ = RationalCompletion.K→𝔻


ℝᴰCommRing : (ℓ : Level) → CommRing (ℓ-suc ℓ)
ℝᴰCommRing ℓ =
  CompletionArithmetic.CommRingStructure.DedekindCompletionCommRing
    archimedeanBaseField {ℓᴾ = ℓ}


ℝᴰOrderedCommRing : (ℓ : Level) → OrderedCommRing (ℓ-suc ℓ) ℓ
ℝᴰOrderedCommRing ℓ =
  CompletionArithmetic.OrderedCommRingStructure.DedekindCompletionOrderedCommRing
    archimedeanBaseField {ℓᴾ = ℓ}


ℝᴰOrderedHeytingField :
  (ℓ : Level) →
  OrderedHeytingField.OrderedHeytingField (ℓ-suc ℓ) ℓ
ℝᴰOrderedHeytingField ℓ =
  CompletionArithmetic.OrderedHeytingFieldStructure.DedekindCompletionOrderedHeytingField
    archimedeanBaseField {ℓᴾ = ℓ}
