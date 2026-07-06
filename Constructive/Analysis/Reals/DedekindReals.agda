{-

The rational instance of constructive Dedekind completions

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.DedekindReals where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals using (ℚ)

open import Constructive.Algebra.LinearlyOrderedField.Instances.Rationals
  using (ℚLinearlyOrderedField ; ℚArchimedeanLinearlyOrderedField)
import Constructive.Analysis.Completions.DedekindCompletion.Approximation as CompletionApproximation
import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic as CompletionArithmetic
import Constructive.Analysis.Completions.DedekindCompletion.Base as CompletionBase
import Constructive.Analysis.Completions.DedekindCompletion.Completeness as CompletionCompleteness
import Constructive.Analysis.Completions.DedekindCompletion.Order as CompletionOrder

private
  variable
    ℓ : Level


baseField = ℚLinearlyOrderedField

archimedeanBaseField = ℚArchimedeanLinearlyOrderedField


module Base = CompletionBase.CompletionBase baseField
module Order = CompletionOrder.CompletionOrder baseField
module ArithmeticBase = CompletionArithmetic.ArithmeticBase archimedeanBaseField


ℝᴰ : (ℓ : Level) → Type (ℓ-suc ℓ)
ℝᴰ = Base.DedekindCompletion

DedekindReals : (ℓ : Level) → Type (ℓ-suc ℓ)
DedekindReals = ℝᴰ


ℚ→ℝᴰ : (ℓ : Level) → ℚ → ℝᴰ ℓ
ℚ→ℝᴰ = Base.K→𝔻


module Approximation {ℓ : Level} =
  CompletionApproximation.CompletionApproximation archimedeanBaseField {ℓᴾ = ℓ}

module Completeness {ℓ : Level} =
  CompletionCompleteness.CompletionCompleteness archimedeanBaseField ℓ


module Addition {ℓ : Level} =
  ArithmeticBase.Addition {ℓ}

module Negation {ℓ : Level} =
  CompletionArithmetic.Negation archimedeanBaseField {ℓᴾ = ℓ}

module AdditiveGroup {ℓ : Level} =
  CompletionArithmetic.AdditiveGroup archimedeanBaseField {ℓᴾ = ℓ}

module Difference {ℓ : Level} =
  CompletionArithmetic.Difference archimedeanBaseField {ℓᴾ = ℓ}

module NonNegativeMultiplication {ℓ : Level} =
  CompletionArithmetic.NonNegativeMultiplication archimedeanBaseField {ℓᴾ = ℓ}

module NonNegativeProperties {ℓ : Level} =
  CompletionArithmetic.NonNegativeProperties archimedeanBaseField {ℓᴾ = ℓ}

module Multiplication {ℓ : Level} =
  CompletionArithmetic.Multiplication archimedeanBaseField {ℓᴾ = ℓ}

module Unit {ℓ : Level} =
  CompletionArithmetic.UnitProperties archimedeanBaseField {ℓᴾ = ℓ}

module Distributivity {ℓ : Level} =
  CompletionArithmetic.MultiplicationDistributivity archimedeanBaseField {ℓᴾ = ℓ}

module Associativity {ℓ : Level} =
  CompletionArithmetic.MultiplicationAssociativity archimedeanBaseField {ℓᴾ = ℓ}

module CommRing {ℓ : Level} =
  CompletionArithmetic.CommRingStructure archimedeanBaseField {ℓᴾ = ℓ}

module OrderProperties {ℓ : Level} =
  CompletionArithmetic.OrderProperties archimedeanBaseField {ℓᴾ = ℓ}

module OrderedCommRing {ℓ : Level} =
  CompletionArithmetic.OrderedCommRingStructure archimedeanBaseField {ℓᴾ = ℓ}

module Inverse {ℓ : Level} =
  CompletionArithmetic.Inverse archimedeanBaseField {ℓᴾ = ℓ}

module OrderedHeytingField {ℓ : Level} =
  CompletionArithmetic.OrderedHeytingFieldStructure archimedeanBaseField {ℓᴾ = ℓ}
