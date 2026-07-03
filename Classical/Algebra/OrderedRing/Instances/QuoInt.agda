{-

Facts about Integers

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedRing.Instances.QuoInt where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection

-- It seems there are bugs when applying ring solver to explicit ring.
-- The following is a work-around.
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
  using    (ℤ ; pos ; negsuc)
  renaming (_+_ to _+ℤ_ ; _·_ to _·ℤ_ ; -_ to -ℤ_)
open import Cubical.Data.Rationals using (ℕ₊₁→ℤ)
open import Cubical.Algebra.CommRing.Instances.Int

open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum

open import Classical.Algebra.OrderedRing

private
  variable
    x y z : ℤ
    m n k : ℤ


open Helpers ℤCommRing
open CommRingStr (ℤCommRing .snd)


-- Strictly larger than zero

_>0 : ℤ → Type
(pos zero) >0 = ⊥
(pos (suc y)) >0 = Unit
(negsuc _) >0 = ⊥

isProp>0 : (y : ℤ) → isProp (y >0)
isProp>0 (pos (suc y)) = isPropUnit

>0-asym : (y : ℤ) → y >0 → (- y) >0 → ⊥
>0-asym (pos zero) ()
>0-asym (pos (suc y)) _ p = p
>0-asym (negsuc y) ()

>0-+ : (x y : ℤ) → x >0 → y >0 → (x + y) >0
>0-+ (pos (suc x)) (pos (suc y)) _ _ =
  subst (_>0) (Int.pos+ (suc x) (suc y)) tt

>0-· : (x y : ℤ) → x >0 → y >0 → (x · y) >0
>0-· (pos (suc x)) (pos (suc y)) _ _ =
  subst (_>0) (Int.pos·pos (suc x) (suc y)) tt

trichotomy>0 : (x : ℤ) → Trichotomy>0 ℤCommRing _>0 x
trichotomy>0 (pos zero) = eq refl
trichotomy>0 (pos (suc _)) = gt _
trichotomy>0 (negsuc _) = lt _


{-

  ℤ as ordered ring

-}

ℤOrderedRing : OrderedRing _ _
ℤOrderedRing = ℤCommRing , orderstr _>0 isProp>0 _ >0-asym >0-+ >0-· trichotomy>0

open OrderedRingStr ℤOrderedRing

ℕ₊₁→ℤ>0 : (n : ℕ₊₁) → ℕ₊₁→ℤ n > 0
ℕ₊₁→ℤ>0 n = transport (>0≡>0r (ℕ₊₁→ℤ n)) (helper n)
  where helper : (n : ℕ₊₁) → ℕ₊₁→ℤ n >0
        helper (1+ n) = _

-1·n≡-n : (n : ℤ) → -1 · n ≡ - n
-1·n≡-n n = helper1 1 n ∙ (λ i → - (·IdL n i))


possucn-1≡1 : (n : ℕ) → pos (suc n) - 1 ≡ pos n
possucn-1≡1 n = refl

n>0→n≥1 : (n : ℤ) → n > 0 → n ≥ 1
n>0→n≥1 (pos zero) n>0 = Empty.rec (transport (sym (>0≡>0r 0)) n>0)
n>0→n≥1 (pos (suc zero)) _ = inr refl
n>0→n≥1 n@(pos (suc (suc a))) _ = inl (subst (_>0) (sym (possucn-1≡1 (suc a))) _)
n>0→n≥1 n@(negsuc _) n>0 = Empty.rec (transport (sym (>0≡>0r n)) n>0)

possucn>posn : (n : ℕ) → pos (suc n) > pos n
possucn>posn n = subst (_>0) (sym possucn-posn≡1) _
  where possucn-posn≡1 : pos (suc n) - pos n ≡ 1
        possucn-posn≡1 = helper2 (pos (suc n)) (pos n) ∙ (λ i → possucn-1≡1 n i + 1 - pos n) ∙ helper3 (pos n)

n>0→posm≡n : (n : ℤ) → n > 0 → Σ[ m ∈ ℕ ] pos m ≡ n
n>0→posm≡n (pos n) _ = n , refl
n>0→posm≡n n@(negsuc _) n>0 = Empty.rec (transport (sym (>0≡>0r n)) n>0)


{-

  "Archimedean-ness" of ℤ

-}

archimedes : (a b : ℤ) → b > 0 → Σ[ n ∈ ℕ ] pos n · b > a
archimedes a (negsuc b) b>0 = Empty.rec (transport (sym (>0≡>0r (negsuc b))) b>0)
archimedes a (pos b) b>0 with trichotomy a 0
... | lt a<0 = 1 , <-trans {x = a} {y = 0} {z = 1 · pos b} a<0 (subst (_> 0) (sym (·IdL (pos b))) b>0)
... | eq a≡0 = 1 , subst (1 · pos b >_) (sym a≡0) (subst (_> 0) (sym (·IdL (pos b))) b>0)
... | gt a>0 = suc an , subst (pos (suc an) · (pos b) >_) (·IdR a) posn·b>a·1
  where an = n>0→posm≡n a a>0 .fst
        p = n>0→posm≡n a a>0 .snd
        possucm>a : pos (suc an) > a
        possucm>a = subst (pos (suc an) >_) p (possucn>posn an)
        posn·b>a·1 : pos (suc an) · (pos b) > a · 1
        posn·b>a·1 = ·-PosPres>≥ {x = a} {y = pos (suc an)} a>0 _ possucm>a (n>0→n≥1 (pos b) b>0)

archimedes' : (a b : ℤ) → b > 0 → Σ[ n ∈ ℕ ] pos n · b + a > 0
archimedes' a b b>0 =
  let (n , posn·b>-a) = archimedes (- a) b b>0
      posn·b+a>-a+a : pos n · b + a > - a + a
      posn·b+a>-a+a = +-rPres< {x = - a} {y = pos n · b} {z = a} posn·b>-a
  in  n , subst (pos n · b + a >_) (+InvL a) posn·b+a>-a+a
