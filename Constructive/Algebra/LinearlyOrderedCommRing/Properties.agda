{-

  Properties of linearly ordered commutative rings

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Algebra.LinearlyOrderedCommRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
  using (OrderedCommRing ; OrderedCommRingStr)
open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Relation.Nullary

open import Constructive.Algebra.OrderedCommRing.Properties as OrderedProperties
open import Constructive.Algebra.LinearlyOrderedCommRing.Base hiding (Trichotomy ; isPropTrichotomy ; lt ; eq ; gt)
import Constructive.Algebra.LinearlyOrderedCommRing.Base as LinearBase

private
  variable
    ℓ ℓ' : Level


private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (x y : 𝓡 .fst) → x · (- y) ≡ - (x · y)
    helper1 _ _ = solve! 𝓡


module LinearlyOrderedCommRingStr (𝓡 : LinearlyOrderedCommRing ℓ ℓ') where

  private
    𝓡ᶜ = 𝓡 .fst
    𝓡ᵣ = LinearlyOrderedCommRing→CommRing 𝓡
    R = 𝓡ᶜ .fst

  module Ord = OrderedCommRingStr (𝓡ᶜ .snd)

  open RingTheory (CommRing→Ring 𝓡ᵣ)
  open CommRingStr  (𝓡ᵣ .snd)
  open LinearOrderStrOnOrderedCommRing (𝓡 .snd) renaming (trichotomy to trichotomyᶜ)
  open OrderedProperties.OrderedCommRingTheory 𝓡ᶜ public
  open Helpers 𝓡ᵣ

  private
    variable
      x y z w : R

    Trichotomy : R → R → Type (ℓ-max ℓ ℓ')
    Trichotomy = LinearBase.Trichotomy 𝓡ᶜ

    pattern lt x<y = LinearBase.lt x<y
    pattern eq x≡y = LinearBase.eq x≡y
    pattern gt y<x = LinearBase.gt y<x

  isPropTrichotomy : (x y : R) → isProp (LinearBase.Trichotomy 𝓡ᶜ x y)
  isPropTrichotomy = LinearBase.isPropTrichotomy 𝓡ᶜ

  trichotomy : (x y : R) → LinearBase.Trichotomy 𝓡ᶜ x y
  trichotomy = trichotomyᶜ

  dec< : (x y : R) → Dec (x < y)
  dec< x y with trichotomy x y
  ... | lt x<y = yes x<y
  ... | eq x≡y = no (λ p → <-arefl p x≡y)
  ... | gt x>y = no (λ p → <-asym  p x>y)


  {-

    Cancellation from trichotomy

  -}

  ·-rPosCancel>0 : x > 0r → x · y > 0r → y > 0r
  ·-rPosCancel>0 {x = x} {y = y} x>0 x·y>0 with trichotomy y 0r
  ... | lt y<0 = Empty.rec (<-asym (·-rNegReverse>0 x>0 y<0) x·y>0)
  ... | eq y≡0 = Empty.rec (<-arefl x·y>0 (sym (0RightAnnihilates x) ∙ (λ i → x · y≡0 (~ i))))
  ... | gt y>0 = y>0

  ·-rPosCancel<0 : x > 0r → x · y < 0r → y < 0r
  ·-rPosCancel<0 {x = x} {y = y} x>0 x·y<0 =
    -Reverse->0 (·-rPosCancel>0 x>0 (subst (_> 0r) (sym (helper1 x y)) (-Reverse<0 x·y<0)))

  ·-lPosCancel>0 : x > 0r → y · x > 0r → y > 0r
  ·-lPosCancel>0 {x = x} {y = y} x>0 y·x>0 = ·-rPosCancel>0 x>0 (subst (_> 0r) (·Comm y x) y·x>0)

  ·-lPosCancel<0 : x > 0r → y · x < 0r → y < 0r
  ·-lPosCancel<0 {x = x} {y = y} x>0 y·x<0 = ·-rPosCancel<0 x>0 (subst (_< 0r) (·Comm y x) y·x<0)

  ·-rPosCancel< : x > 0r → x · y < x · z → y < z
  ·-rPosCancel< {x = x} {y = y} {z = z} x>0 x·y<x·z with trichotomy y z
  ... | lt y<z = y<z
  ... | eq y≡z = Empty.rec (<-arefl x·y<x·z (λ i → x · y≡z i))
  ... | gt y>z = Empty.rec (<-asym (·-lPosPres< x>0 y>z) x·y<x·z)


  {-

    Totality consequences

  -}

  ≤-total : (x y : R) → (x ≤ y) ⊎ (y ≤ x)
  ≤-total x y with trichotomy x y
  ... | lt x<y = inl (<-≤-weaken x<y)
  ... | eq x≡y = inl (≤-refl x≡y)
  ... | gt x>y = inr (<-≤-weaken x>y)

  <≤-total : (x y : R) → (x < y) ⊎ (y ≤ x)
  <≤-total x y with trichotomy x y
  ... | lt x<y = inl x<y
  ... | eq x≡y = inr (≤-refl (sym x≡y))
  ... | gt x>y = inr (Ord.<-≤-weaken y x x>y)

  ¬≤→> : ¬ x ≤ y → x > y
  ¬≤→> {x = x} {y = y} ¬x≤y with <≤-total y x
  ... | inl x>y = x>y
  ... | inr x≤y = Empty.rec (¬x≤y x≤y)

  ≤+¬≡→< : x ≤ y → ¬ x ≡ y → x < y
  ≤+¬≡→< {x = x} {y = y} x≤y ¬x≡y with trichotomy x y
  ... | lt x<y = x<y
  ... | eq x≡y = Empty.rec (¬x≡y x≡y)
  ... | gt y<x = Empty.rec (equivFun (Ord.≤≃¬> x y) x≤y y<x)

  ≤+¬<→≡ : x ≤ y → ¬ x < y → x ≡ y
  ≤+¬<→≡ {x = x} {y = y} x≤y ¬x<y with trichotomy x y
  ... | lt x<y = Empty.rec (¬x<y x<y)
  ... | eq x≡y = x≡y
  ... | gt y<x = Empty.rec (equivFun (Ord.≤≃¬> x y) x≤y y<x)

  ·-PosPres≥0>0 : x ≥ 0r → z ≥ 0r → y > 0r → w > 0r → x < y → z < w → x · z < y · w
  ·-PosPres≥0>0 {x = x} {z = z} {y = y} {w = w} x≥0 z≥0 y>0 w>0 x<y z<w
    with trichotomy x 0r | trichotomy z 0r
  ... | lt x<0 | _ = Empty.rec (<≤-asym x<0 x≥0)
  ... | _ | lt z<0 = Empty.rec (<≤-asym z<0 z≥0)
  ... | gt x>0 | gt z>0 = ·-PosPres> x>0 z>0 x<y z<w
  ... | eq x≡0 | _ =
    subst (y · w >_) (sym (0LeftAnnihilates _) ∙ (λ i → x≡0 (~ i) · z)) (·-Pres>0 y>0 w>0)
  ... | _ | eq z≡0 =
    subst (y · w >_) (sym (0RightAnnihilates _) ∙ (λ i → x · z≡0 (~ i))) (·-Pres>0 y>0 w>0)


  {-

    Linearly ordered commutative rings are integral

  -}

  ·-lCancel : ¬ x ≡ 0r → x · y ≡ x · z → y ≡ z
  ·-lCancel {x = x} {y = y} {z = z} x≢0 x·y≡x·z with trichotomy x 0r | trichotomy y z
  ... | _      | eq y≡z = y≡z
  ... | eq x≡0 | _      = Empty.rec (x≢0 x≡0)
  ... | lt x<0 | lt y<z = Empty.rec (<-arefl (·-lNegReverse< x<0 y<z) (sym x·y≡x·z))
  ... | lt x<0 | gt y>z = Empty.rec (<-arefl (·-lNegReverse< x<0 y>z) x·y≡x·z)
  ... | gt x>0 | lt y<z = Empty.rec (<-arefl (·-lPosPres< x>0 y<z) x·y≡x·z)
  ... | gt x>0 | gt y>z = Empty.rec (<-arefl (·-lPosPres< x>0 y>z) (sym x·y≡x·z))

  ·-rCancel : ¬ x ≡ 0r → y · x ≡ z · x → y ≡ z
  ·-rCancel x≢0 y·x≡z·x = ·-lCancel x≢0 (·Comm _ _ ∙ y·x≡z·x ∙ ·Comm _ _)


  {-

    Minimum and maximum of two elements

  -}

  min : (x y : R) → R
  min x y with ≤-total x y
  ... | inl x≤y = x
  ... | inr x≥y = y

  min≤left : min x y ≤ x
  min≤left {x = x} {y = y} with ≤-total x y
  ... | inl x≤y = ≤-refl refl
  ... | inr x≥y = x≥y

  min≤right : min x y ≤ y
  min≤right {x = x} {y = y} with ≤-total x y
  ... | inl x≤y = x≤y
  ... | inr x≥y = ≤-refl refl

  max : (x y : R) → R
  max x y with ≤-total x y
  ... | inl x≤y = y
  ... | inr x≥y = x

  max≥left : max x y ≥ x
  max≥left {x = x} {y = y} with ≤-total x y
  ... | inl x≤y = x≤y
  ... | inr x≥y = ≤-refl refl

  max≥right : max x y ≥ y
  max≥right {x = x} {y = y} with ≤-total x y
  ... | inl x≤y = ≤-refl refl
  ... | inr x≥y = x≥y
