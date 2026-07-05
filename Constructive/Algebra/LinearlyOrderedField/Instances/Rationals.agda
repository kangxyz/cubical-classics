{-

Rationals as a linearly ordered field

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.LinearlyOrderedField.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Rationals using (ℚ)
open import Cubical.Algebra.Field.Instances.Rationals
  using (ℚField)
import Cubical.Algebra.Field as CubicalField

open import Constructive.Algebra.LinearlyOrderedCommRing.Instances.Rationals
  using (ℚLinearlyOrderedCommRing)
open import Constructive.Algebra.LinearlyOrderedCommRing.Instances.Rationals.Archimedes
  using (isArchimedeanℚ) public
open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedes
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.Algebra.OrderedField.Instances.Rationals
  using (ℚOrderedField) public


-- ℚ is a linearly ordered field

ℚLinearlyOrderedField : LinearlyOrderedField ℓ-zero ℓ-zero
ℚLinearlyOrderedField =
  ℚLinearlyOrderedCommRing , ℚOrderedField .snd


-- Inclusions from natural numbers.

open LinearlyOrderedFieldStr ℚLinearlyOrderedField using (ℕ→R-Pos ; ℕ→R-Neg)

ℕ→ℚPos : ℕ → ℚ
ℕ→ℚPos = ℕ→R-Pos

ℕ→ℚNeg : ℕ → ℚ
ℕ→ℚNeg = ℕ→R-Neg
