{-

  Homomorphism between Ordered Rings,
  namely ring homomorphism that preserves order relation

-}
{-# OPTIONS --safe --lossy-unification #-}
module Classical.Algebra.OrderedRing.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Int
  using    (ℤ ; pos ; neg ; negsuc ; sucℤ ; predℤ
           ; fromNatℤ ; fromNegℤ)
  renaming (_+_ to _+ℤ_ ; _·_ to _·ℤ_ ; -_ to -ℤ_ ; _-_ to _-ℤ_
           ; ·AnnihilL to ·AnnihilLℤ ; sucℤ· to sucℤ·ℤ ; -DistL· to -DistL·ℤ
           ; pos0+ to pos0+ℤ ; sucℤ+ to sucℤ+ℤ ; predℤ+ to predℤ+ℤ)

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Relation.Nullary

open import Cubical.Algebra.CommRing.Instances.Int
open import Classical.Algebra.OrderedRing.Instances.QuoInt
  using    (ℤOrderedRing)
  renaming (_>0 to _>ℤ0)
open import Classical.Algebra.OrderedRing

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    𝓡  : OrderedRing ℓ   ℓ'
    𝓡' : OrderedRing ℓ'' ℓ'''


private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : 1r ≡ 1r - 0r
    helper1 = solve! 𝓡

    helper2 : (x : 𝓡 .fst) → - x ≡ 1r - (1r + x)
    helper2 _ = solve! 𝓡

    helper3 : (x : 𝓡 .fst) → - (1r - x) ≡ - 1r + x
    helper3 _ = solve! 𝓡

    helper4 : (x : 𝓡 .fst) → x ≡ - 0r + x
    helper4 _ = solve! 𝓡

    helper5 : (x y : 𝓡 .fst) → - (x · y) ≡ (- x) · y
    helper5 _ _ = solve! 𝓡

    helper6 : (x y : 𝓡 .fst) → y + (x · y) ≡ (1r + x) · y
    helper6 _ _ = solve! 𝓡

    helper7 : (x : 𝓡 .fst) → x ≡ - 1r + (1r + x)
    helper7 _ = solve! 𝓡


-- The homomorphism between ordered rings is just ring homomorphism that preserves positive element

open OrderStrOnCommRing

record OrderedRingHom (𝓡 : OrderedRing ℓ ℓ')(𝓡' : OrderedRing ℓ'' ℓ''') : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓ''')) where
  field
    ring-hom : CommRingHom (𝓡 .fst) (𝓡' .fst)
    pres->0  : (x : 𝓡 .fst .fst) → 𝓡 .snd ._>0 x → 𝓡' .snd ._>0 (ring-hom .fst x)


{-

  Properties of ordered ring homomorphism

-}

module OrderedRingHomStr (f : OrderedRingHom 𝓡 𝓡') where

  private
    R  = 𝓡  .fst .fst
    R' = 𝓡' .fst .fst

  open OrderedRingStr 𝓡
  open OrderedRingStr 𝓡' using ()
    renaming ( _<_ to _<'_ ; _≤_ to _≤'_
             ; _>_ to _>'_ ; _≥_ to _≥'_
             ; trichotomy to trichotomy'
             ; >0≡>0r to >0≡>0r'
             ; <-arefl to <'-arefl
             ; <-asym  to <'-asym
             ; _⋆_ to _⋆'_
             ; 0⋆q≡0 to 0⋆'q≡0 ; 1⋆q≡q to 1⋆'q≡q
             ; sucn⋆q≡n⋆q+q to sucn⋆'q≡n⋆'q+q)

  open OrderedRingHom f

  open CommRingStr (𝓡  .fst .snd)
  open CommRingStr (𝓡' .fst .snd) using ()
    renaming (0r to 0r' ; _+_ to _+'_ ; _-_ to _-'_ ; -_ to -'_)
  open IsCommRingHom (ring-hom .snd)


  private
    hom-helper : (x y : R) → ring-hom .fst (y - x) ≡ (ring-hom .fst y) -' (ring-hom .fst x)
    hom-helper x y = pres+ y (- x) ∙ (λ i → ring-hom .fst y +' pres- x i)

  homPres< : (x y : R) → x < y → ring-hom .fst x <' ring-hom .fst y
  homPres< x y x<y = subst (𝓡' .snd ._>0) (hom-helper x y) (pres->0 (y - x) x<y)

  homPres≤ : (x y : R) → x ≤ y → ring-hom .fst x ≤' ring-hom .fst y
  homPres≤ x y (inl x<y) = inl (homPres< _ _ x<y)
  homPres≤ x y (inr x≡y) = inr (cong (ring-hom .fst) x≡y)


  homPres<0 : (x : R) → x < 0r → ring-hom .fst x <' 0r'
  homPres<0 x x<0 = subst (ring-hom .fst x <'_) pres0 (homPres< _ _ x<0)

  homPres>0 : (x : R) → x > 0r → ring-hom .fst x >' 0r'
  homPres>0 x x>0 = subst (ring-hom .fst x >'_) pres0 (homPres< _ _ x>0)

  homRefl>0 : (x : R) → ring-hom .fst x >' 0r' → x > 0r
  homRefl>0 x x>0 with trichotomy x 0r
  ... | lt x<0 = Empty.rec (<'-asym  (homPres<0 _ x<0) x>0)
  ... | eq x≡0 = Empty.rec (<'-arefl x>0 (sym pres0 ∙ cong (ring-hom .fst) (sym x≡0)))
  ... | gt x>0 = x>0


  homRefl>0' : (x : R) → 𝓡' .snd ._>0 (ring-hom .fst x) → 𝓡 .snd ._>0 x
  homRefl>0' x = transport (λ i → >0≡>0r' (ring-hom .fst x) (~ i) →  >0≡>0r x (~ i)) (homRefl>0 x)


  homRefl≡ : (x y : R) → ring-hom .fst x ≡ ring-hom .fst y → x ≡ y
  homRefl≡ x y fx≡fy with trichotomy x y
  ... | lt x<y = Empty.rec (<'-arefl (homPres< _ _ x<y) fx≡fy)
  ... | eq x≡y = x≡y
  ... | gt x>y = Empty.rec (<'-arefl (homPres< _ _ x>y) (sym fx≡fy))

  homRefl< : (x y : R) → ring-hom .fst x <' ring-hom .fst y → x < y
  homRefl< x y fx<fy with trichotomy x y
  ... | lt x<y = x<y
  ... | eq x≡y = Empty.rec (<'-arefl fx<fy (cong (ring-hom .fst) x≡y))
  ... | gt x>y = Empty.rec (<'-asym fx<fy (homPres< _ _ x>y))

  homRefl≤ : (x y : R) → ring-hom .fst x ≤' ring-hom .fst y → x ≤ y
  homRefl≤ x y (inl fx<fy) = inl (homRefl< _ _ fx<fy)
  homRefl≤ x y (inr fx≡fy) = inr (homRefl≡ _ _ fx≡fy)


  homPres⋆ : (n : ℕ)(ε : R) → ring-hom .fst (n ⋆ ε) ≡ n ⋆' ring-hom .fst ε
  homPres⋆ 0 ε = (λ i → ring-hom .fst (0⋆q≡0 ε i)) ∙ pres0 ∙ sym (0⋆'q≡0 _)
  homPres⋆ 1 ε = (λ i → ring-hom .fst (1⋆q≡q ε i)) ∙ sym (1⋆'q≡q _)
  homPres⋆ (suc (suc n)) ε = (λ i → ring-hom .fst (sucn⋆q≡n⋆q+q (suc n) ε i))
    ∙ pres+ _ _
    ∙ (λ i → homPres⋆ (suc n) ε i +' ring-hom .fst ε)
    ∙ sym (sucn⋆'q≡n⋆'q+q (suc n) _)


{-

  The Canonical Map from ℤ

-}

module InclusionFromℤ (𝓡 : OrderedRing ℓ ℓ') where

  open RingTheory (CommRing→Ring (𝓡 .fst))
  open CommRingStr   (𝓡 .fst .snd)
  open OrderedRingStr 𝓡

  open OrderedRingStr ℤOrderedRing using () renaming (_>_ to _>ℤ_ ; >0≡>0r to >0≡>0r-ℤ)

  open Helpers (𝓡 .fst)

  private
    R = 𝓡  .fst .fst
    isSetR = is-set


  ℤ→R : ℤ → R
  ℤ→R (pos n) = ℕ→R-Pos n
  ℤ→R (negsuc n) = ℕ→R-Neg (suc n)

  ℤ→R-Pres-1 : ℤ→R (pos 1) ≡ 1r
  ℤ→R-Pres-1 = refl

  ℤ→R-Suc : (n : ℤ) → ℤ→R (sucℤ n) ≡ 1r + ℤ→R n
  ℤ→R-Suc (pos n) = ℕ→R-PosSuc n
  ℤ→R-Suc (negsuc zero) = sym 0Selfinverse ∙ helper2 _ ∙ (λ i → 1r - ℤ→R-Suc (pos zero) (~ i))
  ℤ→R-Suc (negsuc (suc n)) = helper2 _ ∙ (λ i → 1r - ℤ→R-Suc (pos (suc n)) (~ i))

  ℤ→R-Negate : (n : ℤ) → ℤ→R (-ℤ n) ≡ - ℤ→R n
  ℤ→R-Negate (pos zero) = sym 0Selfinverse
  ℤ→R-Negate (pos (suc _)) = refl
  ℤ→R-Negate (negsuc _) = sym (-Idempotent _)

  ℤ→R-Pred : (n : ℤ) → ℤ→R (predℤ n) ≡ - 1r + ℤ→R n
  ℤ→R-Pred (pos zero) = sym (+IdR (- 1r))
  ℤ→R-Pred (pos (suc n)) = helper7 (ℕ→R-Pos n) ∙ (λ i → - 1r + ℕ→R-PosSuc n (~ i))
  ℤ→R-Pred (negsuc n) = ℕ→R-NegSuc (suc n)

  ℕ→R-Neg≡ℤ→Rneg : (n : ℕ) → ℕ→R-Neg n ≡ ℤ→R (neg n)
  ℕ→R-Neg≡ℤ→Rneg zero = 0Selfinverse
  ℕ→R-Neg≡ℤ→Rneg (suc _) = refl

  predℤ-neg : (n : ℕ) → predℤ (neg n) ≡ negsuc n
  predℤ-neg zero = refl
  predℤ-neg (suc _) = refl

  ℤ→R-Pres-+ : (m n : ℤ) → ℤ→R (m +ℤ n) ≡ ℤ→R m + ℤ→R n
  ℤ→R-Pres-+ (pos zero) n = (λ i → ℤ→R (pos0+ℤ n (~ i))) ∙ sym (+IdL (ℤ→R n))
  ℤ→R-Pres-+ (pos (suc m)) n = (λ i → ℤ→R (sucℤ+ℤ (pos m) n (~ i)))
    ∙ ℤ→R-Suc (pos m +ℤ n)
    ∙ (λ i → 1r + ℤ→R-Pres-+ (pos m) n i)
    ∙ +Assoc _ _ _ ∙ (λ i → ℕ→R-PosSuc m (~ i) + ℤ→R n)
  ℤ→R-Pres-+ (negsuc zero) n = (λ i → ℤ→R (predℤ-neg zero (~ i) +ℤ n))
    ∙ (λ i → ℤ→R (predℤ+ℤ (neg zero) n (~ i)))
    ∙ ℤ→R-Pred (neg zero +ℤ n)
    ∙ (λ i → - 1r + ℤ→R-Pres-+ (pos zero) n i)
    ∙ +Assoc _ _ _
    ∙ (λ i → (- 1r + ℕ→R-Neg≡ℤ→Rneg zero (~ i)) + ℤ→R n)
    ∙ (λ i → ℕ→R-NegSuc zero (~ i) + ℤ→R n)
  ℤ→R-Pres-+ (negsuc (suc m)) n = (λ i → ℤ→R (predℤ-neg (suc m) (~ i) +ℤ n))
    ∙ (λ i → ℤ→R (predℤ+ℤ (neg (suc m)) n (~ i)))
    ∙ ℤ→R-Pred (neg (suc m) +ℤ n)
    ∙ (λ i → - 1r + ℤ→R-Pres-+ (negsuc m) n i)
    ∙ +Assoc _ _ _
    ∙ (λ i → (- 1r + ℕ→R-Neg≡ℤ→Rneg (suc m) (~ i)) + ℤ→R n)
    ∙ (λ i → ℕ→R-NegSuc (suc m) (~ i) + ℤ→R n)


  ℤ→R-PresPos· : (m : ℕ)(n : ℤ) → ℤ→R (pos m ·ℤ n) ≡ ℤ→R (pos m) · ℤ→R n
  ℤ→R-PresPos· zero n = (λ i → ℤ→R (·AnnihilLℤ n i)) ∙ sym (0LeftAnnihilates _)
  ℤ→R-PresPos· (suc m) n = (λ i → ℤ→R (sucℤ·ℤ (pos m) n i))
    ∙ ℤ→R-Pres-+ n (pos m ·ℤ n)
    ∙ (λ i → ℤ→R n + ℤ→R-PresPos· m n i)
    ∙ helper6 _ _ ∙ (λ i → ℤ→R-Suc (pos m) (~ i) · ℤ→R n)

  ℤ→R-Pres-· : (m n : ℤ) → ℤ→R (m ·ℤ n) ≡ ℤ→R m · ℤ→R n
  ℤ→R-Pres-· (pos m) n = ℤ→R-PresPos· m n
  ℤ→R-Pres-· (negsuc m) n =
      (λ i → ℤ→R (-DistL·ℤ (pos (suc m)) n (~ i)))
    ∙ ℤ→R-Negate (pos (suc m) ·ℤ n)
    ∙ (λ i → - ℤ→R-PresPos· (suc m) n i) ∙ helper5 _ _
    ∙ (λ i → ℤ→R-Negate (pos (suc m)) (~ i) · ℤ→R n)


  ℤ→R-Pres>0' : (n : ℤ) → n >ℤ0 → ℤ→R n > 0r
  ℤ→R-Pres>0' (pos (suc zero)) _ = 1>0
  ℤ→R-Pres>0' (pos (suc (suc n))) _ = +-Pres>0 1>0 (ℤ→R-Pres>0' (pos (suc n)) _)

  ℤ→R-Pres>0'' : (n : ℤ) → n >ℤ pos 0 → ℤ→R n > 0r
  ℤ→R-Pres>0'' n n>0 = ℤ→R-Pres>0' n (transport (sym (>0≡>0r-ℤ _)) n>0)

  ℤ→R-Pres>0 : (n : ℤ) → n >ℤ0 → 𝓡 .snd ._>0 (ℤ→R n)
  ℤ→R-Pres>0 n h = transport (sym (>0≡>0r _)) (ℤ→R-Pres>0' n h)


  {-

    (Ordered) Ring Homomorphism Instance

  -}

  isRingHomℤ→R : IsRingHom (CommRing→Ring ℤCommRing .snd) ℤ→R (CommRing→Ring (𝓡 .fst) .snd)
  isRingHomℤ→R = makeIsRingHom ℤ→R-Pres-1 ℤ→R-Pres-+ ℤ→R-Pres-·

  ℤ→RCommRingHom : CommRingHom ℤCommRing (𝓡 .fst)
  ℤ→RCommRingHom = _ , IsRingHom→IsCommRingHom ℤCommRing (𝓡 .fst) ℤ→R isRingHomℤ→R

  open OrderedRingHom

  ℤ→ROrderedRingHom : OrderedRingHom ℤOrderedRing 𝓡
  ℤ→ROrderedRingHom .ring-hom = ℤ→RCommRingHom
  ℤ→ROrderedRingHom .pres->0  = ℤ→R-Pres>0
