{-

ℚ is a Field

-}
{-# OPTIONS --safe #-}
module Classical.Preliminary.Rationals.Field where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing

open import Cubical.Data.Sigma
open import Cubical.Data.Int
  using    (ℤ ; isSetℤ)
  renaming (_·_ to _·ℤ_)
import Cubical.Data.Int as ℤ
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals
  using    (ℚ ; ℕ₊₁→ℤ ; isEquivRel∼ ; eq/ ; eq/⁻¹ ; numerator0→0 ; ·CancelL)
open import Cubical.HITs.SetQuotients as SetQuot hiding (_/_)
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Algebra.CommRing.Instances.Rationals
open import Cubical.Algebra.Field.Instances.Rationals
  using    (hasInverseℚ)

open import Cubical.Relation.Nullary

open import Classical.Algebra.Field


-- A rational number is zero if and only if its numerator is zero

a/b≡0→a≡0 : (x : ℤ × ℕ₊₁) → [ x ] ≡ 0 → x .fst ≡ 0
a/b≡0→a≡0 (a , b) a/b≡0 =
  sym (ℤ.·IdR a) ∙ eq/⁻¹ (a , b) (0 , 1) a/b≡0 ∙ ℤ.·AnnihilL (ℕ₊₁→ℤ b)

a≡0→a/b≡0 : (x : ℤ × ℕ₊₁) → x .fst ≡ 0 → [ x ] ≡ 0
a≡0→a/b≡0 = numerator0→0


-- ℚ is a field

isFieldℚ : isField ℚCommRing
isFieldℚ = hasInverseℚ

ℚField : Field ℓ-zero
ℚField = ℚCommRing , isFieldℚ


{-

  Some properties about ℚ being a field

-}

open CommRingStr (ℚCommRing .snd)

1/n·n≡1 : (n : ℕ₊₁) →  [ 1 , n ] · [ ℕ₊₁→ℤ n , 1 ] ≡ 1
1/n·n≡1 n =
  (λ i → [ ℤ.·Comm 1 (ℕ₊₁→ℤ n) i , n ·₊₁ 1 ])
  ∙ ·CancelL {a = 1} {b = 1} n

_/_ : ℚ → ℕ₊₁ → ℚ
q / n = q · [ 1 , n ]

·-/-rInv : (q : ℚ)(n : ℕ₊₁) → (q / n) · [ ℕ₊₁→ℤ n , 1 ] ≡ q
·-/-rInv q n = sym (·Assoc q _ _) ∙ (λ i → q · 1/n·n≡1 n i) ∙ ·IdR q

·-/-lInv : (q : ℚ)(n : ℕ₊₁) → [ ℕ₊₁→ℤ n , 1 ] · (q / n) ≡ q
·-/-lInv q n = ·Comm _ (q / n) ∙ ·-/-rInv q n
