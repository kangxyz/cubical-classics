{-

Facts about Integers

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.LinearlyOrderedCommRing.Instances.Int where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection

-- The ring solver has trouble with explicit rings here.
-- The following is a workaround.
private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (x y : 𝓡 .fst) → (- x) · y ≡ - (x · y)
    helper1 _ _ = solve! 𝓡

    helper2 : (a b : 𝓡 .fst) → a - b ≡ (a - 1r) + 1r - b
    helper2 _ _ = solve! 𝓡

    helper3 : (b : 𝓡 .fst) → b + 1r - b ≡ 1r
    helper3 _ = solve! 𝓡


open import Cubical.Data.Nat
  using    (ℕ ; zero ; suc)
  renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order using ()
  renaming (_<_ to _<ℕ_ ; _>_ to _>ℕ_)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int as Int
  using    (ℤ ; pos ; negsuc ; pos+)
  renaming (_+_ to _+ℤ_ ; _·_ to _·ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Int.Order as IntOrder
  using    (zero-<sucPos ; isIrrefl< ; ¬pos≤negsuc)
  renaming (_≟_ to _≟ℤ_)
open import Cubical.Data.Rationals using (ℕ₊₁→ℤ)
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Algebra.OrderedCommRing.Instances.Int
  using (ℤOrderedCommRing)

open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum

open import Constructive.Algebra.LinearlyOrderedCommRing
open import Constructive.Algebra.LinearlyOrderedCommRing.Base
  using (Trichotomy ; lt ; eq ; gt)

private
  variable
    x y z : ℤ
    m n k : ℤ


open Helpers ℤCommRing
open CommRingStr (ℤCommRing .snd)


trichotomyℤ : (x y : ℤ) → Trichotomy ℤOrderedCommRing x y
trichotomyℤ x y with x ≟ℤ y
... | IntOrder.lt x<y = lt x<y
... | IntOrder.eq x≡y = eq x≡y
... | IntOrder.gt y<x = gt y<x


{-

  ℤ as a linearly ordered commutative ring

-}

ℤLinearlyOrderedCommRing : LinearlyOrderedCommRing _ _
ℤLinearlyOrderedCommRing = ℤOrderedCommRing , linearorderstr trichotomyℤ

open LinearlyOrderedCommRingStr ℤLinearlyOrderedCommRing

ℕ₊₁→ℤ>0 : (n : ℕ₊₁) → ℕ₊₁→ℤ n > 0
ℕ₊₁→ℤ>0 n = helper n
  where helper : (n : ℕ₊₁) → ℕ₊₁→ℤ n >0
        helper (1+ n) = zero-<sucPos

-1·n≡-n : (n : ℤ) → -1 · n ≡ - n
-1·n≡-n n = helper1 1 n ∙ (λ i → - (·IdL n i))


possucn-1≡1 : (n : ℕ) → pos (suc n) - 1 ≡ pos n
possucn-1≡1 n = refl

n>0→n≥1 : (n : ℤ) → n > 0 → n ≥ 1
n>0→n≥1 (pos zero) n>0 = Empty.rec (isIrrefl< n>0)
n>0→n≥1 (pos (suc zero)) _ = 0 , refl
n>0→n≥1 n@(pos (suc (suc a))) _ = suc a , sym (pos+ 1 (suc a))
n>0→n≥1 n@(negsuc _) n>0 = Empty.rec (¬pos≤negsuc n>0)

possucn>posn : (n : ℕ) → pos (suc n) > pos n
possucn>posn n = 0 , refl

n>0→posm≡n : (n : ℤ) → n > 0 → Σ[ m ∈ ℕ ] pos m ≡ n
n>0→posm≡n (pos n) _ = n , refl
n>0→posm≡n n@(negsuc _) n>0 = Empty.rec (¬pos≤negsuc n>0)


{-

  The Archimedean Property of ℤ

-}

archimedean : (a b : ℤ) → b > 0 → Σ[ n ∈ ℕ ] pos n · b > a
archimedean a (negsuc b) b>0 = Empty.rec (¬pos≤negsuc b>0)
archimedean a (pos b) b>0 with trichotomy a 0
... | lt a<0 = 1 , <-trans {x = a} {y = 0} {z = 1 · pos b} a<0 (subst (_> 0) (sym (·IdL (pos b))) b>0)
... | eq a≡0 = 1 , subst (1 · pos b >_) (sym a≡0) (subst (_> 0) (sym (·IdL (pos b))) b>0)
... | gt a>0 = suc an , subst (pos (suc an) · (pos b) >_) (·IdR a) posn·b>a·1
  where an = n>0→posm≡n a a>0 .fst
        p = n>0→posm≡n a a>0 .snd
        possucm>a : pos (suc an) > a
        possucm>a = subst (pos (suc an) >_) p (possucn>posn an)
        posn·b>a·1 : pos (suc an) · (pos b) > a · 1
        posn·b>a·1 = ·-PosPres>≥ {x = a} {y = pos (suc an)} a>0 1>0 possucm>a (n>0→n≥1 (pos b) b>0)

archimedean' : (a b : ℤ) → b > 0 → Σ[ n ∈ ℕ ] pos n · b + a > 0
archimedean' a b b>0 =
  let (n , posn·b>-a) = archimedean (- a) b b>0
      posn·b+a>-a+a : pos n · b + a > - a + a
      posn·b+a>-a+a = +-rPres< {x = - a} {y = pos n · b} {z = a} posn·b>-a
  in  n , subst (pos n · b + a >_) (+InvL a) posn·b+a>-a+a
