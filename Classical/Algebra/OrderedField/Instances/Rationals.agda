{-

Rational Numbers

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Rationals using (ℚ)
open import Cubical.Algebra.Field.Instances.Rationals
  using (ℚField)

open import Classical.Preliminary.Rationals.Order using (ℚStrictlyOrderedCommRing)
open import Classical.Preliminary.Rationals.Archimedes using (isArchimedeanℚ) public
open import Classical.Algebra.StrictlyOrderedCommRing.Archimedes
open import Classical.Algebra.OrderedField
open import Classical.Algebra.Field using (CubicalFieldStr)


-- ℚ is totally ordered field

ℚOrderedField : OrderedField ℓ-zero ℓ-zero
ℚOrderedField = ℚStrictlyOrderedCommRing , CubicalFieldStr.isField (ℚField .snd)


-- Inclusion from Natural Numbers

open OrderedFieldStr ℚOrderedField using (ℕ→R-Pos ; ℕ→R-Neg)

ℕ→ℚPos : ℕ → ℚ
ℕ→ℚPos = ℕ→R-Pos

ℕ→ℚNeg : ℕ → ℚ
ℕ→ℚNeg = ℕ→R-Neg
