{-

  The Archimedean Property of ℚ

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.LinearlyOrderedCommRing.Instances.Rationals.Archimedes where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection

-- The ring solver has trouble with explicit rings here.
-- The following is a workaround.
private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (n c b : 𝓡 .fst) → n · (c · b) ≡ (n · c) · b
    helper1 _ _ _ = solve! 𝓡

    helper2 : (n : 𝓡 .fst) → (1r + n) · (1r · 1r) ≡ (1r · 1r + n · 1r) · (1r · 1r)
    helper2 _ = solve! 𝓡

    helper3 : (n q : 𝓡 .fst) → (1r + n) · q ≡ (n · q) + q
    helper3 _ _ = solve! 𝓡


open import Cubical.Foundations.HLevels
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
  using    (ℕ ; zero ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int
  using    (ℤ ; pos)
  renaming (_·_ to _·ℤ_ ; _+_ to _+ℤ_ ; -_ to -ℤ_)
import Cubical.Data.Int as Int
open import Cubical.Data.Rationals
  using    (ℚ ; ℕ₊₁→ℤ ; ·AnnihilL)
open import Cubical.HITs.SetQuotients as SetQuot
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Relation.Nullary

open import Constructive.Algebra.LinearlyOrderedCommRing.Instances.Int
  using    (ℤLinearlyOrderedCommRing ; ℕ₊₁→ℤ>0 ; -1·n≡-n)
  renaming (archimedes' to archimedesℤ)
open import Constructive.Algebra.LinearlyOrderedCommRing.Instances.Rationals
  using    (ℚLinearlyOrderedCommRing)
open import Constructive.Preliminary.Nat
open import Constructive.Algebra.LinearlyOrderedCommRing
open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedes


open CommRingStr    ((LinearlyOrderedCommRing→CommRing ℚLinearlyOrderedCommRing) .snd)
open LinearlyOrderedCommRingStr  ℚLinearlyOrderedCommRing renaming (_⋆_ to _⋆'_)
open LinearlyOrderedCommRingStr  ℤLinearlyOrderedCommRing using    ()
  renaming (_<_ to _<ℤ_ ; _>_ to _>ℤ_
           ; ·-Pres>0 to ·ℤ-Pres>0)

open Helpers (LinearlyOrderedCommRing→CommRing ℤLinearlyOrderedCommRing)
open Helpers (LinearlyOrderedCommRing→CommRing ℚLinearlyOrderedCommRing) using ()
  renaming (helper3 to helper3ℚ)

private
  one-den : pos 1 ≡ ℕ₊₁→ℤ 1
  one-den = refl

  one-den· : pos 1 ·ℤ pos 1 ≡ ℕ₊₁→ℤ (1 ·₊₁ 1)
  one-den· = sym (Int.pos·pos 1 1) ∙ refl

  path-helper : (n : ℕ)
    → pos (suc n) ·ℤ ℕ₊₁→ℤ (1 ·₊₁ 1)
    ≡ (pos 1 ·ℤ ℕ₊₁→ℤ 1 +ℤ pos n ·ℤ ℕ₊₁→ℤ 1) ·ℤ ℕ₊₁→ℤ 1
  path-helper n =
    cong₂ _·ℤ_ (Int.pos+ 1 n) (sym one-den·)
    ∙ helper2 (pos n)
    ∙ cong₂ _·ℤ_
        (cong₂ _+ℤ_ (cong (pos 1 ·ℤ_) one-den) (cong (pos n ·ℤ_) one-den))
        (sym (Int.pos·pos 1 1) ∙ one-den)


-- An alternative scalar multiplication by natural numbers

_⋆_ : ℕ → ℚ → ℚ
n ⋆ q = [ pos n , 1 ] · q

⋆-repr : (n : ℕ)(c : ℤ)(d : ℕ₊₁) → n ⋆ [ c , d ] ≡ [ pos n ·ℤ c , d ]
⋆-repr n c d i = [ pos n ·ℤ c , ·₊₁-identityˡ d i ]

neg-repr : (a : ℤ)(b : ℕ₊₁) → - [ a , b ] ≡ [ -ℤ a , b ]
neg-repr a b =
  (λ i → [ -1·n≡-n a i , 1 ·₊₁ b ])
  ∙ (λ i → [ -ℤ a , ·₊₁-identityˡ b i ])

⋆≡⋆' : (n : ℕ)(q : ℚ) → n ⋆ q ≡ n ⋆' q
⋆≡⋆' 0 q = ·AnnihilL q ∙ sym (0⋆q≡0 q)
⋆≡⋆' (suc n) q = sucn⋆q≡n⋆q+q' n q ∙ (λ i → ⋆≡⋆' n q i + q) ∙ sym (sucn⋆q≡n⋆q+q n q)
  where
  sucn⋆q≡n⋆q+q' : (n : ℕ)(q : ℚ) → (suc n) ⋆ q ≡ (n ⋆ q) + q
  sucn⋆q≡n⋆q+q' n q = (λ i → path n i · q) ∙ helper3ℚ ([ pos n , 1 ]) q
    where path : (n : ℕ) → [ pos (suc n) , 1 ] ≡ 1 + [ pos n , 1 ]
          path n = eq/ _ _ (path-helper n)


-- The Archimedean property of ℚ, using the alternative product

private
  archimedes-helper : (x y : ℤ × ℕ₊₁) → [ y ] > 0 → Σ[ n ∈ ℕ ] n ⋆ [ y ] > [ x ]
  archimedes-helper (a , b) (c , d) y>0 =
    let right = -ℤ a ·ℤ ℕ₊₁→ℤ d
        c>0 = y>0
        c>0' = subst (_>ℤ pos zero) (Int.·IdR c) c>0
        (n , ->-) =
          archimedesℤ right (c ·ℤ ℕ₊₁→ℤ b)
            (·ℤ-Pres>0 {x = c} {y = ℕ₊₁→ℤ b} c>0' (ℕ₊₁→ℤ>0 b))
        direct-core : pos n ·ℤ c ·ℤ ℕ₊₁→ℤ b +ℤ right >ℤ pos zero
        direct-core = subst (λ t → t +ℤ right >ℤ pos zero) (helper1 (pos n) c (ℕ₊₁→ℤ b)) ->-
        direct-normalized : ([ pos n ·ℤ c , d ] + [ -ℤ a , b ]) >0
        direct-normalized =
          subst (_>ℤ pos zero)
            (sym (Int.·IdR (pos n ·ℤ c ·ℤ ℕ₊₁→ℤ b +ℤ right))
              ∙ cong ((pos n ·ℤ c ·ℤ ℕ₊₁→ℤ b +ℤ right) ·ℤ_) one-den)
            direct-core
        direct : [ pos n ·ℤ c , d ] > [ a , b ]
        direct = Diff>0→> {x = [ pos n ·ℤ c , d ]} {y = [ a , b ]}
          (subst (_>0) (sym (cong ([ pos n ·ℤ c , d ] +_) (neg-repr a b))) direct-normalized)
    in  n , subst (_> [ a , b ]) (sym (⋆-repr n c d)) direct

∥archimedes∥ : (q ε : ℚ) → ε > 0 → ∥ Σ[ n ∈ ℕ ] n ⋆ ε > q ∥₁
∥archimedes∥ = SetQuot.elimProp2 (λ _ _ → isPropΠ (λ _ → squash₁))
  (λ x y h → ∣ archimedes-helper x y h ∣₁)

archimedes : (q ε : ℚ) → ε > 0 → Σ[ n ∈ ℕ ] n ⋆ ε > q
archimedes q ε ε>0 = case-split (dec< q (zero ⋆ ε))
  where
  case-split : Dec (zero ⋆ ε > q) → Σ[ n ∈ ℕ ] n ⋆ ε > q
  case-split (yes p) = zero , p
  case-split (no ¬p) = find (λ n → dec< q (n ⋆ ε)) (∥archimedes∥ q ε ε>0)


-- The Archimedean property of ℚ

isArchimedeanℚ : isArchimedean ℚLinearlyOrderedCommRing
isArchimedeanℚ = transport (λ i → (q ε : ℚ) → ε > 0 → Σ[ n ∈ ℕ ] ⋆≡⋆' n ε i > q) archimedes
