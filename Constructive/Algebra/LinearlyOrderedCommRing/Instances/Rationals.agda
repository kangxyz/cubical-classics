{-

Ordering of rational numbers

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.LinearlyOrderedCommRing.Instances.Rationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Rationals as ℚ
  using    (ℚ ; isSetℚ ; min ; max ; [_/_])
  renaming (_+_ to _+ℚ_ ; _·_ to _·ℚ_ ; -_ to -ℚ_)
open import Cubical.Data.Nat
  using    (zero ; suc)
open import Cubical.Data.NatPlusOne
  using    (1+_)
open import Cubical.Data.Int
  using    (pos)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Int.Order as ℤOrder
  using    (zero-<sucPos)
open import Cubical.HITs.PropositionalTruncation
  using    (∣_∣₁)
open import Cubical.Relation.Nullary

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
  using    (ℚCommRing)
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.StrictOrder

open import Constructive.Algebra.LinearlyOrderedCommRing
open import Constructive.Algebra.LinearlyOrderedCommRing.Base
  using    (Trichotomy ; lt ; eq ; gt)


private
  open BinaryRelation

  0ℚ 1ℚ : ℚ
  0ℚ = [ pos zero / 1+ zero ]
  1ℚ = [ pos (suc zero) / 1+ zero ]

  ℚ≤Poset : Poset ℓ-zero ℓ-zero
  ℚ≤Poset = poset ℚ ℚOrder._≤_
    (isposet isSetℚ ℚOrder.isProp≤ ℚOrder.isRefl≤ ℚOrder.isTrans≤ ℚOrder.isAntisym≤)

  ℚ≤Pseudolattice : Pseudolattice ℓ-zero ℓ-zero
  ℚ≤Pseudolattice =
    makePseudolatticeFromPoset ℚ≤Poset min max
      (λ {a} {b} → ℚOrder.min≤ a b)
      (λ {a} {b} → subst (λ x → ℚOrder._≤_ x b) (ℚ.minComm b a) (ℚOrder.min≤ b a))
      (λ {a} {b} {x} x≤a x≤b →
        subst (λ y → ℚOrder._≤_ y (min a b)) (ℚ.minIdem x)
          (ℚOrder.≤MonotoneMin x a x b x≤a x≤b))
      (λ {a} {b} → ℚOrder.≤max a b)
      (λ {a} {b} → subst (λ x → ℚOrder._≤_ b x) (ℚ.maxComm b a) (ℚOrder.≤max b a))
      (λ {a} {b} {x} a≤x b≤x →
        subst (λ y → ℚOrder._≤_ (max a b) y) (ℚ.maxIdem x)
          (ℚOrder.≤MonotoneMax a x b x a≤x b≤x))

  ℚIsOrderedCommRing : IsOrderedCommRing 0ℚ 1ℚ _+ℚ_ _·ℚ_ -ℚ_ ℚOrder._<_ ℚOrder._≤_
  ℚIsOrderedCommRing .IsOrderedCommRing.isCommRing = ℚCommRing .snd .CommRingStr.isCommRing
  ℚIsOrderedCommRing .IsOrderedCommRing.isPseudolattice = ℚ≤Pseudolattice .snd .PseudolatticeStr.is-pseudolattice
  ℚIsOrderedCommRing .IsOrderedCommRing.isStrictOrder =
    isstrictorder isSetℚ ℚOrder.isProp< ℚOrder.isIrrefl< ℚOrder.isTrans< ℚOrder.isAsym< ℚOrder.isWeaklyLinear<
  ℚIsOrderedCommRing .IsOrderedCommRing.<-≤-weaken = ℚOrder.<Weaken≤
  ℚIsOrderedCommRing .IsOrderedCommRing.≤≃¬> = λ x y →
    propBiimpl→Equiv (ℚOrder.isProp≤ x y) (isProp¬ (y ℚOrder.< x))
      (ℚOrder.≤→≯ x y)
      (ℚOrder.≮→≥ y x)
  ℚIsOrderedCommRing .IsOrderedCommRing.+MonoR≤ = ℚOrder.≤-+o
  ℚIsOrderedCommRing .IsOrderedCommRing.+MonoR< = ℚOrder.<-+o
  ℚIsOrderedCommRing .IsOrderedCommRing.posSum→pos∨pos = λ x y p → ∣ ℚOrder.0<+ x y p ∣₁
  ℚIsOrderedCommRing .IsOrderedCommRing.<-≤-trans = ℚOrder.isTrans<≤
  ℚIsOrderedCommRing .IsOrderedCommRing.≤-<-trans = ℚOrder.isTrans≤<
  ℚIsOrderedCommRing .IsOrderedCommRing.·MonoR≤ = ℚOrder.≤-·o
  ℚIsOrderedCommRing .IsOrderedCommRing.·MonoR< = ℚOrder.<-·o
  ℚIsOrderedCommRing .IsOrderedCommRing.0<1 = zero-<sucPos


ℚOrderedCommRing : OrderedCommRing ℓ-zero ℓ-zero
ℚOrderedCommRing .fst = ℚ
ℚOrderedCommRing .snd =
  orderedcommringstr 0ℚ 1ℚ _+ℚ_ _·ℚ_ -ℚ_ ℚOrder._<_ ℚOrder._≤_ ℚIsOrderedCommRing


_>0 : ℚ → Type
q >0 = 0ℚ ℚOrder.< q

isProp>0 : (q : ℚ) → isProp (q >0)
isProp>0 q = ℚOrder.isProp< 0ℚ q


trichotomyℚ : (x y : ℚ) → Trichotomy ℚOrderedCommRing x y
trichotomyℚ x y with x ℚOrder.≟ y
... | ℚOrder.lt x<y = lt x<y
... | ℚOrder.eq x≡y = eq x≡y
... | ℚOrder.gt y<x = gt y<x


{-

  ℚ is a linearly ordered commutative ring

-}

ℚLinearlyOrderedCommRing : LinearlyOrderedCommRing _ _
ℚLinearlyOrderedCommRing = ℚOrderedCommRing , linearorderstr trichotomyℚ
