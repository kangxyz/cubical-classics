{-

  Homomorphisms between ordered commutative rings

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.OrderedCommRing.Morphism where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Int
  using    (ℤ ; pos ; neg ; negsuc ; sucℤ ; predℤ)
  renaming (_+_ to _+ℤ_ ; _·_ to _·ℤ_ ; -_ to -ℤ_ ; _-_ to _-ℤ_
           ; ·AnnihilL to ·AnnihilLℤ ; sucℤ· to sucℤ·ℤ ; -DistL· to -DistL·ℤ
           ; pos0+ to pos0+ℤ ; sucℤ+ to sucℤ+ℤ ; predℤ+ to predℤ+ℤ)
open import Cubical.Data.Int.Order as IntOrder
  using    (zero-<sucPos ; isIrrefl< ; ¬pos≤negsuc)
  renaming (_≟_ to _≟ℤ_)

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Int
  using (ℤOrderedCommRing)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Algebra.OrderedCommRing.Properties

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    𝓡  : OrderedCommRing ℓ   ℓ'
    𝓡' : OrderedCommRing ℓ'' ℓ'''


private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (x : 𝓡 .fst) → - x ≡ 1r - (1r + x)
    helper1 _ = solve! 𝓡

    helper2 : (x y : 𝓡 .fst) → - (x · y) ≡ (- x) · y
    helper2 _ _ = solve! 𝓡

    helper3 : (x y : 𝓡 .fst) → y + (x · y) ≡ (1r + x) · y
    helper3 _ _ = solve! 𝓡

    helper4 : (x : 𝓡 .fst) → x ≡ - 1r + (1r + x)
    helper4 _ = solve! 𝓡


{-
An ordered commutative-ring homomorphism preserves both strict and non-strict
order.  In a weak ordered commutative ring, preservation of _<_ does not by
itself give preservation of _≤_: using _≤_ ≃ ¬ (y < x) would require reflecting
strict inequalities back along the homomorphism.
-}
record OrderedCommRingHom
  (𝓡 : OrderedCommRing ℓ ℓ')
  (𝓡' : OrderedCommRing ℓ'' ℓ''')
  : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓ''')) where
  field
    ring-hom : CommRingHom (OrderedCommRing→CommRing 𝓡) (OrderedCommRing→CommRing 𝓡')
    pres<    : (x y : 𝓡 .fst) → OrderedCommRingStr._<_ (𝓡 .snd) x y →
               OrderedCommRingStr._<_ (𝓡' .snd) (ring-hom .fst x) (ring-hom .fst y)
    pres≤    : (x y : 𝓡 .fst) → OrderedCommRingStr._≤_ (𝓡 .snd) x y →
               OrderedCommRingStr._≤_ (𝓡' .snd) (ring-hom .fst x) (ring-hom .fst y)


module OrderedCommRingHomProperties (f : OrderedCommRingHom 𝓡 𝓡') where

  private
    R  = 𝓡  .fst
    R' = 𝓡' .fst

  open OrderedCommRingTheory 𝓡
  open OrderedCommRingTheory 𝓡' using ()
    renaming ( _<_ to _<'_ ; _≤_ to _≤'_
             ; _>_ to _>'_ ; _≥_ to _≥'_
             ; _>0 to _>0'_
             ; _⋆_ to _⋆'_
             ; 0⋆q≡0 to 0⋆'q≡0 ; 1⋆q≡q to 1⋆'q≡q
             ; sucn⋆q≡n⋆q+q to sucn⋆'q≡n⋆'q+q)

  open OrderedCommRingHom f

  open CommRingStr (OrderedCommRing→CommRing 𝓡 .snd)
  open CommRingStr (OrderedCommRing→CommRing 𝓡' .snd) using ()
    renaming (0r to 0r' ; _+_ to _+'_)
  open IsCommRingHom (ring-hom .snd)

  homPres< : (x y : R) → x < y → ring-hom .fst x <' ring-hom .fst y
  homPres< = pres<

  homPres≤ : (x y : R) → x ≤ y → ring-hom .fst x ≤' ring-hom .fst y
  homPres≤ = pres≤

  homPres<0 : (x : R) → x < 0r → ring-hom .fst x <' 0r'
  homPres<0 x x<0 = subst (ring-hom .fst x <'_) pres0 (homPres< _ _ x<0)

  homPres>0 : (x : R) → x > 0r → ring-hom .fst x >' 0r'
  homPres>0 x x>0 = subst (_<' ring-hom .fst x) pres0 (homPres< _ _ x>0)

  homPres⋆ : (n : ℕ)(ε : R) → ring-hom .fst (n ⋆ ε) ≡ n ⋆' ring-hom .fst ε
  homPres⋆ 0 ε = (λ i → ring-hom .fst (0⋆q≡0 ε i)) ∙ pres0 ∙ sym (0⋆'q≡0 _)
  homPres⋆ 1 ε = (λ i → ring-hom .fst (1⋆q≡q ε i)) ∙ sym (1⋆'q≡q _)
  homPres⋆ (suc (suc n)) ε = (λ i → ring-hom .fst (sucn⋆q≡n⋆q+q (suc n) ε i))
    ∙ pres+ _ _
    ∙ (λ i → homPres⋆ (suc n) ε i +' ring-hom .fst ε)
    ∙ sym (sucn⋆'q≡n⋆'q+q (suc n) _)


{-

  The canonical map from ℤ

-}

module InclusionFromℤ (𝓡 : OrderedCommRing ℓ ℓ') where

  open RingTheory (CommRing→Ring (OrderedCommRing→CommRing 𝓡))
  open CommRingStr (OrderedCommRing→CommRing 𝓡 .snd)
  open OrderedCommRingTheory 𝓡

  open OrderedCommRingTheory ℤOrderedCommRing using ()
    renaming (_<_ to _<ℤ_ ; _>_ to _>ℤ_
             ; _≤_ to _≤ℤ_
             ; <→Diff>0 to <ℤ→Diff>0
             ; <≤-asym to <≤ℤ-asym)

  open Helpers (OrderedCommRing→CommRing 𝓡)

  private
    R = 𝓡 .fst


  ℤ→R : ℤ → R
  ℤ→R (pos n) = ℕ→R-Pos n
  ℤ→R (negsuc n) = ℕ→R-Neg (suc n)

  ℤ→R-Pres-1 : ℤ→R (pos 1) ≡ 1r
  ℤ→R-Pres-1 = refl

  ℤ→R-Suc : (n : ℤ) → ℤ→R (sucℤ n) ≡ 1r + ℤ→R n
  ℤ→R-Suc (pos n) = ℕ→R-PosSuc n
  ℤ→R-Suc (negsuc zero) = sym 0Selfinverse ∙ helper1 _ ∙ (λ i → 1r - ℤ→R-Suc (pos zero) (~ i))
  ℤ→R-Suc (negsuc (suc n)) = helper1 _ ∙ (λ i → 1r - ℤ→R-Suc (pos (suc n)) (~ i))

  ℤ→R-Negate : (n : ℤ) → ℤ→R (-ℤ n) ≡ - ℤ→R n
  ℤ→R-Negate (pos zero) = sym 0Selfinverse
  ℤ→R-Negate (pos (suc _)) = refl
  ℤ→R-Negate (negsuc _) = sym (-Idempotent _)

  ℤ→R-Pred : (n : ℤ) → ℤ→R (predℤ n) ≡ - 1r + ℤ→R n
  ℤ→R-Pred (pos zero) = sym (+IdR (- 1r))
  ℤ→R-Pred (pos (suc n)) = helper4 (ℕ→R-Pos n) ∙ (λ i → - 1r + ℕ→R-PosSuc n (~ i))
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
    ∙ helper3 _ _ ∙ (λ i → ℤ→R-Suc (pos m) (~ i) · ℤ→R n)

  ℤ→R-Pres-· : (m n : ℤ) → ℤ→R (m ·ℤ n) ≡ ℤ→R m · ℤ→R n
  ℤ→R-Pres-· (pos m) n = ℤ→R-PresPos· m n
  ℤ→R-Pres-· (negsuc m) n =
      (λ i → ℤ→R (-DistL·ℤ (pos (suc m)) n (~ i)))
    ∙ ℤ→R-Negate (pos (suc m) ·ℤ n)
    ∙ (λ i → - ℤ→R-PresPos· (suc m) n i) ∙ helper2 _ _
    ∙ (λ i → ℤ→R-Negate (pos (suc m)) (~ i) · ℤ→R n)

  ℤ→R-Pres>0 : (n : ℤ) → n >ℤ pos zero → ℤ→R n >0
  ℤ→R-Pres>0 (pos zero) h = Empty.rec (isIrrefl< h)
  ℤ→R-Pres>0 (pos (suc zero)) _ = 1>0
  ℤ→R-Pres>0 (pos (suc (suc n))) _ =
    +-Pres>0 1>0
      (ℤ→R-Pres>0 (pos (suc n)) zero-<sucPos)
  ℤ→R-Pres>0 (negsuc n) h = Empty.rec (¬pos≤negsuc h)

  ℤ→R-Pres-- : (m n : ℤ) → ℤ→R (m -ℤ n) ≡ ℤ→R m - ℤ→R n
  ℤ→R-Pres-- m n = ℤ→R-Pres-+ m (-ℤ n) ∙ (λ i → ℤ→R m + ℤ→R-Negate n i)

  ℤ→R-Pres< : (m n : ℤ) → m <ℤ n → ℤ→R m < ℤ→R n
  ℤ→R-Pres< m n m<n =
    Diff>0→< (subst (_>0) (ℤ→R-Pres-- n m) (ℤ→R-Pres>0 (n -ℤ m) (<ℤ→Diff>0 m<n)))

  ℤ→R-Pres≤ : (m n : ℤ) → m ≤ℤ n → ℤ→R m ≤ ℤ→R n
  ℤ→R-Pres≤ m n m≤n with m ≟ℤ n
  ... | IntOrder.lt m<n = <-≤-weaken (ℤ→R-Pres< m n m<n)
  ... | IntOrder.eq m≡n = ≤-refl (cong ℤ→R m≡n)
  ... | IntOrder.gt n<m = Empty.rec (<≤ℤ-asym n<m m≤n)


  {-

    Ordered ring homomorphism instance

  -}

  isRingHomℤ→R : IsRingHom (CommRing→Ring ℤCommRing .snd) ℤ→R (CommRing→Ring (OrderedCommRing→CommRing 𝓡) .snd)
  isRingHomℤ→R = makeIsRingHom ℤ→R-Pres-1 ℤ→R-Pres-+ ℤ→R-Pres-·

  ℤ→RCommRingHom : CommRingHom ℤCommRing (OrderedCommRing→CommRing 𝓡)
  ℤ→RCommRingHom =
    _ , IsRingHom→IsCommRingHom ℤCommRing (OrderedCommRing→CommRing 𝓡) ℤ→R isRingHomℤ→R

  open OrderedCommRingHom

  ℤ→ROrderedCommRingHom : OrderedCommRingHom ℤOrderedCommRing 𝓡
  ℤ→ROrderedCommRingHom .ring-hom = ℤ→RCommRingHom
  ℤ→ROrderedCommRingHom .pres<    = ℤ→R-Pres<
  ℤ→ROrderedCommRingHom .pres≤    = ℤ→R-Pres≤
