{-

Arithmetic structure for constructive Dedekind reals

This is the rational instance of generic Dedekind-completion arithmetic.

-}
{-# OPTIONS --safe #-}
module Constructive.DedekindReals.Arithmetic where

open import Cubical.Foundations.Prelude

open import Constructive.Algebra.LinearlyOrderedField.Instances.Rationals
open import Constructive.DedekindCompletion.Arithmetic.Sign public
import Constructive.DedekindCompletion.Arithmetic.Base as GBase
import Constructive.DedekindCompletion.Arithmetic.Negation as GNegation
import Constructive.DedekindCompletion.Arithmetic.AdditiveGroup as GAdditive
import Constructive.DedekindCompletion.Arithmetic.NonNegative as GNonNegative
import Constructive.DedekindCompletion.Arithmetic.Multiplication as GMultiplication
import Constructive.DedekindCompletion.Arithmetic.Unit as GUnit
import Constructive.DedekindCompletion.Arithmetic.Difference as GDifference
import Constructive.DedekindCompletion.Arithmetic.Distributivity as GDistributivity
import Constructive.DedekindCompletion.Arithmetic.Associativity as GAssociativity
import Constructive.DedekindCompletion.Arithmetic.CommRing as GCommRing
import Constructive.DedekindCompletion.Arithmetic.Order as GOrder
import Constructive.DedekindCompletion.Arithmetic.OrderedCommRing as GOrderedCommRing
import Constructive.DedekindCompletion.Arithmetic.Inverse as GInverse
import Constructive.DedekindCompletion.Arithmetic.OrderedHeytingField as GOrderedHeytingField

private
  variable
    ℓ : Level

  𝒜 = ℚArchimedeanLinearlyOrderedField

module ArithmeticBase = GBase.ArithmeticBase 𝒜


module Addition {ℓ : Level} where
  open ArithmeticBase.Addition {ℓ} public
    renaming (_+𝔻_ to _+_)


module NegationProperties {ℓ : Level} where
  open GNegation.Negation 𝒜 {ℓ} public
    hiding (𝒦)
    renaming (-𝔻_ to -_)


module AdditiveGroup {ℓ : Level} where
  open ArithmeticBase.Addition {ℓ} public
    renaming (_+𝔻_ to _+_)
  open GNegation.Negation 𝒜 {ℓ} public
    hiding (𝒦)
    renaming (-𝔻_ to -_)
  open GAdditive.AdditiveGroup 𝒜 {ℓ} public
    hiding (𝒦)
    renaming
      ( DedekindCompletionAbGroup to DedekindAbGroup )


module NonNegativeMultiplication {ℓ : Level} where
  open ArithmeticBase.Addition {ℓ} public
    renaming (_+𝔻_ to _+_)
  open GNegation.Negation 𝒜 {ℓ} public
    hiding (𝒦)
    renaming (-𝔻_ to -_)
  open GNonNegative.NonNegativeMultiplication 𝒜 {ℓ} public
    hiding (𝒦₀)


module NonNegativeProperties {ℓ : Level} where
  open NonNegativeMultiplication {ℓ} public
  open GNonNegative.NonNegativeProperties 𝒜 {ℓ} public
    hiding (baseField)


module Multiplication {ℓ : Level} where
  open GMultiplication.Multiplication 𝒜 {ℓ} public
    using
      ( posPart
      ; negPart
      ; posPart≥0
      ; negPart≥0
      ; neg-0𝔻
      ; posPart-0𝔻
      ; negPart-0𝔻
      ; ≥0→posPart≡id
      ; ≥0→negPart≡0
      ; posPart-mono-≤
      ; negPart-antitone-≤
      ; posProducts
      ; negProducts
      ; posProducts-comm
      ; negProducts-comm
      ; posProducts≥0
      ; negProducts≥0
      ; posProducts≡nnMul
      ; negProducts≡0
      ; rMul≥0
      ; posProducts-r≥0
      ; negProducts-r≥0
      ; posProducts-zeroR
      ; negProducts-zeroR
      )
    renaming
      ( _*𝔻_ to _*_
      ; *𝔻-comm to *-comm
      ; *𝔻-of-≥0 to *-of-≥0
      ; *𝔻-Pres≥0 to *-Pres≥0
      ; *𝔻-r≥0-form to *-r≥0-form
      ; *𝔻-rPosPres≤ to *-rPosPres≤
      ; *𝔻-lPosPres≤ to *-lPosPres≤
      ; *𝔻-zeroR to *-zeroR
      ; *𝔻-zeroL to *-zeroL
      )
  open GMultiplication.MultiplicationNegation 𝒜 {ℓ} public
    using
      ( posPart-neg
      ; negPart-neg
      ; posProducts-negL
      ; negProducts-negL
      )
    renaming
      ( *𝔻-negL to *-negL
      ; *𝔻-negR to *-negR
      ; *𝔻-negL-negR to *-negL-negR
      )


module UnitProperties {ℓ : Level} where
  open Multiplication {ℓ} public
  open GUnit.UnitProperties 𝒜 {ℓ} public
    using
      ( nnMul-idR
      ; nnMul-idL
      )
    renaming
      ( *𝔻-idR-≥0 to *-idR-≥0
      ; *𝔻-idL-≥0 to *-idL-≥0
      ; *𝔻-idR-positive-negative-form to *-idR-positive-negative-form
      ; *𝔻-idR to *-idR
      ; *𝔻-idL to *-idL
      )


module DifferenceProperties {ℓ : Level} where
  open UnitProperties {ℓ} public
  open GDifference.Difference 𝒜 {ℓ} public
    hiding (𝒦)
    renaming (_-𝔻_ to _-_)
  open GDifference.DifferenceProperties 𝒜 {ℓ} public
    hiding (baseField)


module MultiplicationDistributivity {ℓ : Level} where
  open DifferenceProperties {ℓ} public
  open GDistributivity.MultiplicationDistributivity 𝒜 {ℓ} public
    hiding (baseField)
    renaming
      ( *𝔻-right-decomposition-form to *-right-decomposition-form
      ; *𝔻-right-decomposition to *-right-decomposition
      ; *𝔻-distribR to *-distribR
      ; *𝔻-distribL to *-distribL
      )


module MultiplicationAssociativity {ℓ : Level} where
  open MultiplicationDistributivity {ℓ} public
  open GAssociativity.MultiplicationAssociativity 𝒜 {ℓ} public
    hiding (baseField)
    renaming
      ( *𝔻-assoc-two-r≥0 to *-assoc-two-r≥0
      ; *𝔻-assocR-≥0 to *-assocR-≥0
      ; *𝔻-assoc to *-assoc
      )


module CommRingStructure {ℓ : Level} where
  open MultiplicationAssociativity {ℓ} public
  open GCommRing.CommRingStructure 𝒜 {ℓ} public
    hiding (baseField)
    renaming (DedekindCompletionCommRing to DedekindCommRing)


module OrderProperties {ℓ : Level} where
  open CommRingStructure {ℓ} public
  open GOrder.OrderProperties 𝒜 {ℓ} public
    using
      ( K→<-pres
      ; 0𝔻<1𝔻
      ; +-monoR-<
      ; +-monoL-<
      ; >0→≥0
      ; ∃lower>0
      ; nnMul-Pres>0
      ; Diff>0𝔻
      ; Diff>0𝔻→<
      ; lower>0→>0
      ; posSum→pos∨pos
      )
    renaming
      ( _>0𝔻 to _>0
      ; *𝔻-Pres>0 to *-Pres>0
      ; *𝔻-right-difference to *-right-difference
      ; *𝔻-rPosPres< to *-rPosPres<
      )


module OrderedCommRingStructure {ℓ : Level} where
  open OrderProperties {ℓ} public
  open GOrderedCommRing.OrderedCommRingStructure 𝒜 {ℓ} public
    using ()
    renaming
      ( DedekindCompletionIsOrderedCommRing to DedekindIsOrderedCommRing
      ; DedekindCompletionOrderedCommRing to DedekindOrderedCommRing
      )


module Inverse {ℓ : Level} where
  open OrderedCommRingStructure {ℓ} public
  open GInverse.Inverse 𝒜 {ℓ} public
    using
      ( InvLowerWitness
      ; InvUpperWitness
      ; invLower
      ; invUpper
      ; isDedekindCutInv₊
      ; inv𝔻₊
      ; inv𝔻₊≥0
      ; ·-rInv𝔻₊
      ; neg-reverse<0
      ; HasInv#
      ; inv#
      )


module OrderedFieldStructure {ℓ : Level} where
  open Inverse {ℓ} public
  open GOrderedHeytingField.OrderedHeytingFieldStructure 𝒜 {ℓ} public
    using (orderedCommRing ; ·-lInv#' ; 0#1)
    renaming
      ( DedekindCompletionIsHeytingFieldOnOrderedCommRing to
        DedekindIsHeytingFieldOnOrderedCommRing
      ; DedekindCompletionOrderedHeytingField to
        DedekindOrderedHeytingField
      )
