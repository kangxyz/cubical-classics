{-

Rational Numbers

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.StrictlyOrderedField.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Rationals using (ℚ)
open import Cubical.Algebra.Field.Instances.Rationals
  using (ℚField)
import Cubical.Algebra.Field as CubicalField

open import Constructive.Algebra.StrictlyOrderedCommRing.Instances.Rationals
  using (ℚStrictlyOrderedCommRing)
open import Constructive.Algebra.StrictlyOrderedCommRing.Instances.Rationals.Archimedes
  using (isArchimedeanℚ) public
open import Constructive.Algebra.StrictlyOrderedCommRing.Archimedes
open import Constructive.Algebra.StrictlyOrderedField


-- ℚ is a totally ordered field.

ℚOrderedField : OrderedField ℓ-zero ℓ-zero
ℚOrderedField = ℚStrictlyOrderedCommRing , CubicalField.FieldStr.isField (ℚField .snd)

ℚStrictlyOrderedField : StrictlyOrderedField ℓ-zero ℓ-zero
ℚStrictlyOrderedField = ℚOrderedField


-- Inclusions from natural numbers.

open OrderedFieldStr ℚOrderedField using (ℕ→R-Pos ; ℕ→R-Neg)

ℕ→ℚPos : ℕ → ℚ
ℕ→ℚPos = ℕ→R-Pos

ℕ→ℚNeg : ℕ → ℚ
ℕ→ℚNeg = ℕ→R-Neg
