{-

  Properties of ordered commutative ring homomorphisms between strictly
  ordered commutative rings

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Algebra.LinearlyOrderedCommRing.Morphism where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty

open import Cubical.Algebra.CommRing

import Constructive.Algebra.OrderedCommRing.Morphism as OrderedMorphism
open OrderedMorphism using (OrderedCommRingHom)
open import Constructive.Algebra.LinearlyOrderedCommRing

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    𝓡  : LinearlyOrderedCommRing ℓ   ℓ'
    𝓡' : LinearlyOrderedCommRing ℓ'' ℓ'''


{-

  Properties using the trichotomy carried by linearly ordered commutative rings

-}

module OrderedCommRingHomProperties (f : OrderedCommRingHom (𝓡 .fst) (𝓡' .fst)) where

  private
    R  = 𝓡  .fst .fst
    R' = 𝓡' .fst .fst

  open OrderedMorphism.OrderedCommRingHomProperties f public

  open LinearlyOrderedCommRingStr 𝓡
  open LinearlyOrderedCommRingStr 𝓡' using ()
    renaming ( _<_ to _<'_ ; _≤_ to _≤'_
             ; _>_ to _>'_ ; _≥_ to _≥'_
             ; <-arefl to <'-arefl
             ; <-asym  to <'-asym
             ; <≤-asym to <≤'-asym)

  open OrderedMorphism.OrderedCommRingHom f

  open CommRingStr ((LinearlyOrderedCommRing→CommRing 𝓡) .snd)
  open CommRingStr ((LinearlyOrderedCommRing→CommRing 𝓡') .snd) using ()
    renaming (0r to 0r')
  open IsCommRingHom (ring-hom .snd)

  homRefl>0 : (x : R) → ring-hom .fst x >' 0r' → x > 0r
  homRefl>0 x x>0 with trichotomy x 0r
  ... | lt x<0 = Empty.rec (<'-asym  (homPres<0 _ x<0) x>0)
  ... | eq x≡0 = Empty.rec (<'-arefl x>0 (sym pres0 ∙ cong (ring-hom .fst) (sym x≡0)))
  ... | gt x>0 = x>0

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
  homRefl≤ x y fx≤fy with trichotomy x y
  ... | lt x<y = <-≤-weaken x<y
  ... | eq x≡y = ≤-refl x≡y
  ... | gt y<x = Empty.rec (<≤'-asym (homPres< _ _ y<x) fx≤fy)


module InclusionFromℤ {ℓ ℓ' : Level} (𝓡 : LinearlyOrderedCommRing ℓ ℓ') =
  OrderedMorphism.InclusionFromℤ (𝓡 .fst)
