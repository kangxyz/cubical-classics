{-

Rational Numbers

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.Instances.QuoQ where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Rationals using (ℚ)

open import Classical.Preliminary.QuoQ.Field using (isFieldℚ)
open import Classical.Preliminary.QuoQ.Order using (ℚOrderedRing)
open import Classical.Preliminary.QuoQ.Archimedes using (isArchimedeanℚ) public
open import Classical.Algebra.OrderedRing.Archimedes
open import Classical.Algebra.OrderedField


-- ℚ is totally ordered field

ℚOrderedField : OrderedField ℓ-zero ℓ-zero
ℚOrderedField = ℚOrderedRing , isFieldℚ


-- Inclusion from Natural Numbers

open OrderedFieldStr ℚOrderedField using (ℕ→R-Pos ; ℕ→R-Neg)

ℕ→ℚPos : ℕ → ℚ
ℕ→ℚPos = ℕ→R-Pos

ℕ→ℚNeg : ℕ → ℚ
ℕ→ℚNeg = ℕ→R-Neg
