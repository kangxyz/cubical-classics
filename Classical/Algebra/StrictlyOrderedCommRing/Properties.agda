{-

  Properties of strictly ordered commutative rings

-}
{-# OPTIONS --safe --lossy-unification #-}
module Classical.Algebra.StrictlyOrderedCommRing.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc)

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
  using (OrderedCommRing ; OrderedCommRingStr)
open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Relation.Nullary

open import Classical.Algebra.StrictlyOrderedCommRing.Base hiding (Trichotomy ; isPropTrichotomy ; lt ; eq ; gt)
import Classical.Algebra.StrictlyOrderedCommRing.Base as StrictBase

private
  variable
    ℓ ℓ' : Level


private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (x : 𝓡 .fst) → x ≡ (x - 0r)
    helper1 _ = solve! 𝓡

    helper2 : (x y : 𝓡 .fst) → x - y ≡ - (y - x)
    helper2 _ _ = solve! 𝓡

    helper3 : (x y z : 𝓡 .fst) → (z - y) + (y - x) ≡ z - x
    helper3 _ _ _ = solve! 𝓡

    helper4 : (x y : 𝓡 .fst) → (y - x) + x ≡ y
    helper4 _ _ = solve! 𝓡

    helper6 : (x y : 𝓡 .fst) → y - x ≡ ((- x) - (- y))
    helper6 _ _ = solve! 𝓡

    helper7 : (x y : 𝓡 .fst) → x · (- y) ≡ - (x · y)
    helper7 _ _ = solve! 𝓡

    helper8 : (x y : 𝓡 .fst) → (- x) · (- y) ≡ x · y
    helper8 _ _ = solve! 𝓡

    helper9 : (x y z : 𝓡 .fst) → (x - 0r) · (z - y) ≡ (x · z) - (x · y)
    helper9 _ _ _ = solve! 𝓡

    helper10 : (x y z : 𝓡 .fst) → (z - y) · (x - 0r) ≡ (z · x) - (y · x)
    helper10 _ _ _ = solve! 𝓡

    helper11 : (x y : 𝓡 .fst) → - ((- x) · y) ≡ x · y
    helper11 _ _ = solve! 𝓡

    helper14 : (x y : 𝓡 .fst) → x ≡ (y + x) - y
    helper14 _ _ = solve! 𝓡

    helper15 : (x y : 𝓡 .fst) → (x - 0r) · (y - 1r) ≡ (x · y) - x
    helper15 _ _ = solve! 𝓡

    helper16 : 1r - 0r ≡ 1r
    helper16 = solve! 𝓡

    helper17 : (n q : 𝓡 .fst) → (1r + n) · q ≡ (n · q) + q
    helper17 _ _ = solve! 𝓡

    helper18 : (x : 𝓡 .fst) → - (1r + x) ≡ - 1r - x
    helper18 _ = solve! 𝓡

    helper19 : (x y : 𝓡 .fst) → (x - y) + y ≡ x
    helper19 _ _ = solve! 𝓡

    helper20 : (x y : 𝓡 .fst) → (x + y) - y ≡ x
    helper20 _ _ = solve! 𝓡


module StrictlyOrderedCommRingStr (𝓡 : StrictlyOrderedCommRing ℓ ℓ') where

  private
    𝓡ᶜ = 𝓡 .fst
    𝓡ᵣ = StrictlyOrderedCommRing→CommRing 𝓡
    R = 𝓡ᶜ .fst

  module Ord = OrderedCommRingStr (𝓡ᶜ .snd)

  open RingTheory (CommRing→Ring 𝓡ᵣ)
  open CommRingStr  (𝓡ᵣ .snd)
  open StrictOrderStrOnOrderedCommRing (𝓡 .snd) renaming (trichotomy to trichotomyᶜ)

  open Helpers 𝓡ᵣ


  private
    isSetR = is-set

    variable
      x y z w : R

  _<_ : R → R → Type ℓ'
  _<_ = Ord._<_

  _≤_ : R → R → Type ℓ'
  _≤_ = Ord._≤_

  _>_ : R → R → Type ℓ'
  x > y = y < x

  _≥_ : R → R → Type ℓ'
  x ≥ y = y ≤ x

  infix 4 _>_ _<_ _≥_ _≤_

  _>0 : R → Type ℓ'
  x >0 = 0r < x

  isProp>0 : (x : R) → isProp (x >0)
  isProp>0 x = Ord.is-prop-valued< 0r x

  >0-1r : 1r >0
  >0-1r = Ord.0<1

  -Pos→Neg : (- x) >0 → x < 0r
  -Pos→Neg {x = x} -x>0 =
    transport (λ i → +IdL x i < +InvL x i) (Ord.+MonoR< 0r (- x) x -x>0)

  >0-asym : (x : R) → x >0 → (- x) >0 → ⊥
  >0-asym x x>0 -x>0 = Ord.is-asym 0r x x>0 (-Pos→Neg -x>0)

  >0-arefl : (x : R) → x >0 → x ≡ 0r → ⊥
  >0-arefl x x>0 x≡0 = Ord.is-irrefl 0r (subst (0r <_) x≡0 x>0)

  >0-+ : (x y : R) → x >0 → y >0 → (x + y) >0
  >0-+ x y x>0 y>0 =
    Ord.is-trans< 0r y (x + y) y>0
      (subst (_< x + y) (+IdL y) (Ord.+MonoR< 0r x y x>0))

  >0-· : (x y : R) → x >0 → y >0 → (x · y) >0
  >0-· x y x>0 y>0 =
    subst (_< x · y) (0LeftAnnihilates y) (Ord.·MonoR< 0r x y y>0 x>0)

  <→Diff>0 : {x y : R} → x < y → (y - x) >0
  <→Diff>0 {x = x} {y = y} x<y =
    transport (λ i → +InvR x i < y - x) (Ord.+MonoR< x y (- x) x<y)

  Diff>0→< : {x y : R} → (y - x) >0 → x < y
  Diff>0→< {x = x} {y = y} y-x>0 =
    transport (λ i → +IdL x i < helper4 x y i) (Ord.+MonoR< 0r (y - x) x y-x>0)


  {-

    Strict Ordering

  -}

  isProp< : {x y : R} → isProp (x < y)
  isProp< {x = x} {y = y} = Ord.is-prop-valued< x y


  <-asym : x < y → x > y → ⊥
  <-asym {x = x} {y = y} = Ord.is-asym x y

  <-arefl : x < y → x ≡ y → ⊥
  <-arefl {x = x} {y = y} x<y x≡y = Ord.is-irrefl y (subst (_< y) x≡y x<y)

  >-arefl : x > y → x ≡ y → ⊥
  >-arefl x>y x≡y = <-arefl x>y (sym x≡y)

  <-trans : x < y → y < z → x < z
  <-trans {x = x} {y = y} {z = z} = Ord.is-trans< x y z


  private
    Trichotomy : R → R → Type (ℓ-max ℓ ℓ')
    Trichotomy = StrictBase.Trichotomy 𝓡ᶜ

    pattern lt x<y = StrictBase.lt x<y
    pattern eq x≡y = StrictBase.eq x≡y
    pattern gt y<x = StrictBase.gt y<x

  isPropTrichotomy : (x y : R) → isProp (StrictBase.Trichotomy 𝓡ᶜ x y)
  isPropTrichotomy = StrictBase.isPropTrichotomy 𝓡ᶜ

  trichotomy : (x y : R) → StrictBase.Trichotomy 𝓡ᶜ x y
  trichotomy = trichotomyᶜ

  dec< : (x y : R) → Dec (x < y)
  dec< x y with trichotomy x y
  ... | lt x<y = yes x<y
  ... | eq x≡y = no (λ p → <-arefl p x≡y)
  ... | gt x>y = no (λ p → <-asym  p x>y)


  +-Pres< : x < y → z < w → x + z < y + w
  +-Pres< {x = x} {y = y} {z = z} {w = w} x<y z<w =
    <-trans (Ord.+MonoR< x y z x<y)
      (transport (λ i → +Comm z y i < +Comm w y i) (Ord.+MonoR< z w y z<w))

  +-lPres< : x < y → z + x < z + y
  +-lPres< {x = x} {y = y} {z = z} x<y =
    transport (λ i → +Comm x z i < +Comm y z i) (Ord.+MonoR< x y z x<y)

  +-rPres< : x < y → x + z < y + z
  +-rPres< {x = x} {y = y} {z = z} = Ord.+MonoR< x y z


  -Reverse< : x < y → - x > - y
  -Reverse< {x = x} {y = y} x<y = Diff>0→< (subst (_>0) (helper6 x y) (<→Diff>0 x<y))

  -lReverse< : - x < y → x > - y
  -lReverse< {x = x} {y = y} -x<y = subst (_> - y) (-Idempotent x) (-Reverse< -x<y)

  -rReverse< : x < - y → - x > y
  -rReverse< {x = x} {y = y} x<-y = subst (_< - x) (-Idempotent y) (-Reverse< x<-y)


  -Reverse>0 : x > 0r → - x < 0r
  -Reverse>0 {x = x} x>0 = subst (- x <_) 0Selfinverse (-Reverse< x>0)

  -Reverse<0 : x < 0r → - x > 0r
  -Reverse<0 {x = x} x<0 = subst (- x >_) 0Selfinverse (-Reverse< x<0)

  -Reverse->0 : - x > 0r → x < 0r
  -Reverse->0 {x = x} -x>0 = subst (_< 0r) (-Idempotent x) (-Reverse>0 -x>0)

  -Reverse-<0 : - x < 0r → x > 0r
  -Reverse-<0 {x = x} -x<0 = subst (_> 0r) (-Idempotent x) (-Reverse<0 -x<0)


  +-rPos→> : x > 0r → y + x > y
  +-rPos→> {x = x} {y = y} x>0 = subst (_< y + x) (+IdR y) (+-lPres< {z = y} x>0)

  +-rNeg→< : x < 0r → y + x < y
  +-rNeg→< {x = x} {y = y} x<0 = subst (y + x <_) (+IdR y) (+-lPres< {z = y} x<0)

  -rPos→< : x > 0r → y - x < y
  -rPos→< x>0 = +-rNeg→< (-Reverse>0 x>0)

  -rNeg→> : x < 0r → y - x > y
  -rNeg→> x<0 = +-rPos→> (-Reverse<0 x<0)


  ·-lPosPres< : x > 0r → y < z → x · y < x · z
  ·-lPosPres< {x = x} {y = y} {z = z} x>0 y<z =
    transport (λ i → ·Comm y x i < ·Comm z x i) (Ord.·MonoR< y z x x>0 y<z)

  ·-rPosPres< : x > 0r → y < z → y · x < z · x
  ·-rPosPres< {x = x} {y = y} {z = z} = Ord.·MonoR< y z x

  ·-PosPres> : x > 0r → z > 0r → x < y → z < w → x · z < y · w
  ·-PosPres> x>0 z>0 x<y z<w = <-trans (·-rPosPres< z>0 x<y) (·-lPosPres< (<-trans x>0 x<y) z<w)


  +-Pres>0 : x > 0r → y > 0r → x + y > 0r
  +-Pres>0 {x = x} {y = y} x>0 y>0 = subst (x + y >_) (+IdR _) (+-Pres< x>0 y>0)

  +-Pres<0 : x < 0r → y < 0r → x + y < 0r
  +-Pres<0 {x = x} {y = y} x<0 y<0 = subst (x + y <_) (+IdR _) (+-Pres< x<0 y<0)

  ·-Pres>0 : x > 0r → y > 0r → x · y > 0r
  ·-Pres>0 {x = x} {y = y} = >0-· x y


  >→Diff>0 : x > y → x - y > 0r
  >→Diff>0 = <→Diff>0

  <→Diff<0 : x < y → x - y < 0r
  <→Diff<0 {x = x} {y = y} x<y = subst (_< 0r) (sym (helper2 x y)) (-Reverse>0 (<→Diff>0 x<y))

  Diff>0→> : x - y > 0r → x > y
  Diff>0→> = Diff>0→<

  Diff<0→< : x - y < 0r → x < y
  Diff<0→< {x = x} {y = y} x-y<0 = Diff>0→< (subst (_> 0r) (sym (helper2 y x)) (-Reverse<0 x-y<0))


  ·-lNegReverse< : x < 0r → y < z → x · y > x · z
  ·-lNegReverse< {x = x} {y = y} {z = z} x<0 y<z = transport (λ i → helper11 x y i > helper11 x z i) -x·y<-x·z
    where -x·y<-x·z : - ((- x) · y) > - ((- x) · z)
          -x·y<-x·z = -Reverse< (·-lPosPres< (-Reverse<0 x<0) y<z)

  ·-rNegReverse< : x < 0r → y < z → y · x > z · x
  ·-rNegReverse< {x = x} {y = y} {z = z} x<0 y<z = transport (λ i → ·Comm x y i > ·Comm x z i) (·-lNegReverse< x<0 y<z)


  ·-rNegReverse>0 : x > 0r → y < 0r → x · y < 0r
  ·-rNegReverse>0 {x = x} {y = y} x>0 y<0 = -Reverse->0 (subst (_> 0r) (helper7 x y) (·-Pres>0 x>0 (-Reverse<0 y<0)))

  ·-lNegReverse>0 : x < 0r → y > 0r → x · y < 0r
  ·-lNegReverse>0 {x = x} {y = y} x<0 y>0 = subst (_< 0r) (·Comm y x) (·-rNegReverse>0 y>0 x<0)

  ·-rNegReverse<0 : x < 0r → y < 0r → x · y > 0r
  ·-rNegReverse<0 {x = x} {y = y} x>0 y<0 = subst (_> 0r) (helper8 x y) (·-Pres>0 (-Reverse<0 x>0) (-Reverse<0 y<0))


  ·-rPosCancel>0 : x > 0r → x · y > 0r → y > 0r
  ·-rPosCancel>0 {x = x} {y = y} x>0 x·y>0 with trichotomy y 0r
  ... | lt y<0 = Empty.rec (<-asym (·-rNegReverse>0 x>0 y<0) x·y>0)
  ... | eq y≡0 = Empty.rec (<-arefl x·y>0 (sym (0RightAnnihilates x) ∙ (λ i → x · y≡0 (~ i))))
  ... | gt y>0 = y>0

  ·-rPosCancel<0 : x > 0r → x · y < 0r → y < 0r
  ·-rPosCancel<0 {x = x} {y = y} x>0 x·y<0 = -Reverse->0 (·-rPosCancel>0 x>0 (subst (_> 0r) (sym (helper7 x y)) (-Reverse<0 x·y<0)))

  ·-lPosCancel>0 : x > 0r → y · x > 0r → y > 0r
  ·-lPosCancel>0 {x = x} {y = y} x>0 y·x>0 = ·-rPosCancel>0 x>0 (subst (_> 0r) (·Comm y x) y·x>0)

  ·-lPosCancel<0 : x > 0r → y · x < 0r → y < 0r
  ·-lPosCancel<0 {x = x} {y = y} x>0 y·x<0 = ·-rPosCancel<0 x>0 (subst (_< 0r) (·Comm y x) y·x<0)


  ·-rPosCancel< : x > 0r → x · y < x · z → y < z
  ·-rPosCancel< {x = x} {y = y} {z = z} x>0 x·y<x·z with trichotomy y z
  ... | lt y<z = y<z
  ... | eq y≡z = Empty.rec (<-arefl x·y<x·z (λ i → x · y≡z i))
  ... | gt y>z = Empty.rec (<-asym (·-lPosPres< x>0 y>z) x·y<x·z)


  ·-Pos·>1→> : x > 0r → y > 1r → x · y > x
  ·-Pos·>1→> {x = x} {y = y} x>0 y>1 =
    transport (λ i → ·IdL x i < ·Comm y x i) (Ord.·MonoR< 1r y x x>0 y>1)


  +-MoveLToR< : x + y < z → x < z - y
  +-MoveLToR< {x = x} {y = y} {z = z} x+y<z = subst (_< z - y) (helper20 x y) (+-rPres< x+y<z)

  +-MoveRToL< : z < x + y → z - y < x
  +-MoveRToL< {z = z} {x = x} {y = y} x+y>z = subst (_> z - y) (helper20 x y) (+-rPres< x+y>z)

  +-MoveLToR<' : x + y < z → y < z - x
  +-MoveLToR<' {x = x} {y = y} {z = z} x+y<z = +-MoveLToR< (subst (_< z) (+Comm x y) x+y<z)

  +-MoveRToL<' : z < x + y → z - x < y
  +-MoveRToL<' {z = z} {x = x} {y = y} x+y>z = +-MoveRToL< (subst (_> z) (+Comm x y) x+y>z)

  -MoveLToR< : x - y < z → x < z + y
  -MoveLToR< {x = x} {y = y} {z = z} x-y<z = subst (x <_) (λ i → z + -Idempotent y i) (+-MoveLToR< x-y<z)

  -MoveRToL< : z < x - y → z + y < x
  -MoveRToL< {z = z} {x = x} {y = y} x-y>z = subst (x >_) (λ i → z + -Idempotent y i) (+-MoveRToL< x-y>z)

  -MoveLToR<' : x - y < z → x < y + z
  -MoveLToR<' {x = x} x-y<z = subst (x <_) (+Comm _ _) (-MoveLToR< x-y<z)

  -MoveRToL<' : z < x - y → y + z < x
  -MoveRToL<' {x = x} x-y>z = subst (x >_) (+Comm _ _) (-MoveRToL< x-y>z)


  isProp≤ : isProp (x ≤ y)
  isProp≤ {x = x} {y = y} = Ord.is-prop-valued≤ x y


  ≤-asym : x ≤ y → x ≥ y → x ≡ y
  ≤-asym {x = x} {y = y} = Ord.is-antisym x y

  ≤-refl : x ≡ y → x ≤ y
  ≤-refl {x = x} {y = y} x≡y = subst (x ≤_) x≡y (Ord.is-refl x)

  <-≤-weaken : x < y → x ≤ y
  <-≤-weaken {x = x} {y = y} = Ord.<-≤-weaken x y

  ≤≃¬> : (x y : R) → (x ≤ y) ≃ (¬ y < x)
  ≤≃¬> = Ord.≤≃¬>

  ≤-trans : x ≤ y → y ≤ z → x ≤ z
  ≤-trans {x = x} {y = y} {z = z} = Ord.is-trans≤ x y z

  ≤-total : (x y : R) → (x ≤ y) ⊎ (y ≤ x)
  ≤-total x y with trichotomy x y
  ... | lt x<y = inl (<-≤-weaken x<y)
  ... | eq x≡y = inl (≤-refl x≡y)
  ... | gt x>y = inr (<-≤-weaken x>y)


  +-Pres≥0 : x ≥ 0r → y ≥ 0r → (x + y) ≥ 0r
  +-Pres≥0 {x = x} {y = y} x≥0 y≥0 =
    ≤-trans y≥0 (subst (_≤ x + y) (+IdL y) (Ord.+MonoR≤ 0r x y x≥0))

  ·-Pres≥0 : x ≥ 0r → y ≥ 0r → (x · y) ≥ 0r
  ·-Pres≥0 {x = x} {y = y} x≥0 y≥0 =
    subst (_≤ x · y) (0LeftAnnihilates y) (Ord.·MonoR≤ 0r x y y≥0 x≥0)


  +-rPos→≥ : x ≥ 0r → y + x ≥ y
  +-rPos→≥ {x = x} {y = y} x≥0 =
    transport (λ i → +IdL y i ≤ +Comm x y i) (Ord.+MonoR≤ 0r x y x≥0)

  +-rNeg→≤ : x ≤ 0r → y + x ≤ y
  +-rNeg→≤ {x = x} {y = y} x≤0 =
    transport (λ i → +Comm x y i ≤ +IdL y i) (Ord.+MonoR≤ x 0r y x≤0)


  ≥→Diff≥0 : x ≥ y → x - y ≥ 0r
  ≥→Diff≥0 {x = x} {y = y} y≤x =
    transport (λ i → +InvR y i ≤ x - y) (Ord.+MonoR≤ y x (- y) y≤x)

  ≤→Diff≤0 : x ≤ y → x - y ≤ 0r
  ≤→Diff≤0 {x = x} {y = y} x≤y =
    transport (λ i → x - y ≤ +InvR y i) (Ord.+MonoR≤ x y (- y) x≤y)

  Diff≥0→≥ : x - y ≥ 0r → x ≥ y
  Diff≥0→≥ {x = x} {y = y} 0≤x-y =
    transport (λ i → +IdL y i ≤ helper19 x y i) (Ord.+MonoR≤ 0r (x - y) y 0≤x-y)

  Diff≤0→≤ : x - y ≤ 0r → x ≤ y
  Diff≤0→≤ {x = x} {y = y} x-y≤0 =
    transport (λ i → helper19 x y i ≤ +IdL y i) (Ord.+MonoR≤ (x - y) 0r y x-y≤0)


  +-Pres≤ : x ≤ y → z ≤ w → x + z ≤ y + w
  +-Pres≤ {x = x} {y = y} {z = z} {w = w} x≤y z≤w =
    ≤-trans (Ord.+MonoR≤ x y z x≤y)
      (transport (λ i → +Comm z y i ≤ +Comm w y i) (Ord.+MonoR≤ z w y z≤w))

  +-lPres≤ : x ≤ y → z + x ≤ z + y
  +-lPres≤ {x = x} {y = y} {z = z} x≤y =
    transport (λ i → +Comm x z i ≤ +Comm y z i) (Ord.+MonoR≤ x y z x≤y)

  +-rPres≤ : x ≤ y → x + z ≤ y + z
  +-rPres≤ {x = x} {y = y} {z = z} = Ord.+MonoR≤ x y z


  -Reverse≤ : x ≤ y → - x ≥ - y
  -Reverse≤ {x = x} {y = y} x≤y = Diff≥0→≥ (subst (_≥ 0r) (helper6 x y) (≥→Diff≥0 x≤y))

  -lReverse≤ : - x ≤ y → x ≥ - y
  -lReverse≤ {x = x} {y = y} -x≥y = subst (_≥ - y) (-Idempotent x) (-Reverse≤ -x≥y)

  -rReverse≤ : x ≤ - y → - x ≥ y
  -rReverse≤ {x = x} {y = y} x≤-y = subst (_≤ - x) (-Idempotent y) (-Reverse≤ x≤-y)


  ·-lPosPres≤ : x ≥ 0r → y ≤ z → x · y ≤ x · z
  ·-lPosPres≤ {x = x} {y = y} {z = z} x≥0 y≤z =
    transport (λ i → ·Comm y x i ≤ ·Comm z x i) (Ord.·MonoR≤ y z x x≥0 y≤z)

  ·-rPosPres≤ : x ≥ 0r → y ≤ z → y · x ≤ z · x
  ·-rPosPres≤ {x = x} {y = y} {z = z} = Ord.·MonoR≤ y z x

  ·-PosPres≥ : x ≥ 0r → z ≥ 0r → x ≤ y → z ≤ w → x · z ≤ y · w
  ·-PosPres≥ x≥0 z≥0 x≤y z≤w = ≤-trans (·-rPosPres≤ z≥0 x≤y) (·-lPosPres≤ (≤-trans x≥0 x≤y) z≤w)


  {-

    Strict & Non-strict Together

  -}

  <≤-asym : x < y → y ≤ x → ⊥
  <≤-asym {x = x} {y = y} x<y y≤x = equivFun (Ord.≤≃¬> y x) y≤x x<y


  <≤-trans : x < y → y ≤ z → x < z
  <≤-trans {x = x} {y = y} {z = z} = Ord.<-≤-trans x y z

  ≤<-trans : x ≤ y → y < z → x < z
  ≤<-trans {x = x} {y = y} {z = z} = Ord.≤-<-trans x y z


  <≤-total : (x y : R) → (x < y) ⊎ (y ≤ x)
  <≤-total x y with trichotomy x y
  ... | lt x<y = inl x<y
  ... | eq x≡y = inr (≤-refl (sym x≡y))
  ... | gt x>y = inr (Ord.<-≤-weaken y x x>y)


  ¬<→≥ : ¬ x < y → x ≥ y
  ¬<→≥ {x = x} {y = y} ¬x<y = invEq (Ord.≤≃¬> y x) ¬x<y

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


  ·-PosPres>≥ : x > 0r → z > 0r → x < y → z ≤ w → x · z < y · w
  ·-PosPres>≥ x>0 z>0 x<y z≤w =
    <≤-trans (·-rPosPres< z>0 x<y) (·-lPosPres≤ (Ord.<-≤-weaken _ _ (<-trans x>0 x<y)) z≤w)

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

    Strictly ordered commutative rings are integral

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

    Inclusion from Natural Numbers

  -}

  1>0 : 1r > 0r
  1>0 = >0-1r


  ℕ→R-Pos : ℕ → R
  ℕ→R-Pos 0 = 0r
  ℕ→R-Pos 1 = 1r
  ℕ→R-Pos (suc (suc n)) = 1r + ℕ→R-Pos (suc n)

  ℕ→R-Neg : ℕ → R
  ℕ→R-Neg n = - ℕ→R-Pos n

  ℕ→R-PosSuc : (n : ℕ) → ℕ→R-Pos (suc n) ≡ 1r + ℕ→R-Pos n
  ℕ→R-PosSuc zero = sym (+IdR 1r)
  ℕ→R-PosSuc (suc n) = refl

  ℕ→R-NegSuc : (n : ℕ) → ℕ→R-Neg (suc n) ≡ - 1r + ℕ→R-Neg n
  ℕ→R-NegSuc n = (λ i → - ℕ→R-PosSuc n i) ∙ helper18 _


  ℕ→R-PosSuc>0 : (n : ℕ) → ℕ→R-Pos (suc n) > 0r
  ℕ→R-PosSuc>0 zero = 1>0
  ℕ→R-PosSuc>0 (suc n) = +-Pres>0 1>0 (ℕ→R-PosSuc>0 n)

  ℕ→R-Pos≥0 : (n : ℕ) → ℕ→R-Pos n ≥ 0r
  ℕ→R-Pos≥0 zero = ≤-refl refl
  ℕ→R-Pos≥0 (suc n) = Ord.<-≤-weaken 0r (ℕ→R-Pos (suc n)) (ℕ→R-PosSuc>0 n)

  ℕ→R-NegSuc<0 : (n : ℕ) → ℕ→R-Neg (suc n) < 0r
  ℕ→R-NegSuc<0 n = -Reverse>0 (ℕ→R-PosSuc>0 n)

  ℕ→R-Neg≤0 : (n : ℕ) → ℕ→R-Neg n ≤ 0r
  ℕ→R-Neg≤0 zero = ≤-refl 0Selfinverse
  ℕ→R-Neg≤0 (suc n) = Ord.<-≤-weaken (ℕ→R-Neg (suc n)) 0r (ℕ→R-NegSuc<0 n)


  -1r : R
  -1r = - 1r

  2r : R
  2r = 1r + 1r

  -1<0 : -1r < 0r
  -1<0 = ℕ→R-NegSuc<0 0

  2>0 : 2r > 0r
  2>0 = ℕ→R-PosSuc>0 1


  q+1>q : {q : R} → q + 1r > q
  q+1>q {q = q} = +-rPos→> {x = 1r} {y = q} 1>0

  q-1<q : {q : R} → q - 1r < q
  q-1<q {q = q} = +-rNeg→< {x = -1r} {y = q} -1<0



  {-

    Scalar multiplication by natural numbers

  -}

  _⋆_ : ℕ → R → R
  n ⋆ q = ℕ→R-Pos n · q


  0⋆q≡0 : (q : R) → 0 ⋆ q ≡ 0r
  0⋆q≡0 q = 0LeftAnnihilates q

  1⋆q≡q : (q : R) → 1 ⋆ q ≡ q
  1⋆q≡q q = ·IdL q

  sucn⋆q≡n⋆q+q : (n : ℕ)(q : R) → (suc n) ⋆ q ≡ (n ⋆ q) + q
  sucn⋆q≡n⋆q+q n q = (λ i → ℕ→R-PosSuc n i · q) ∙ helper17 (ℕ→R-Pos n) q

  sucn⋆q>0 : (n : ℕ)(q : R) → q > 0r → (suc n) ⋆ q > 0r
  sucn⋆q>0 zero q q>0 = subst (_> 0r) (sym (1⋆q≡q q)) q>0
  sucn⋆q>0 (suc n) q q>0 = subst (_> 0r) (sym (sucn⋆q≡n⋆q+q (suc n) q))
    (+-Pres>0 {x = suc n ⋆ q} (sucn⋆q>0 n q q>0) q>0)

  n⋆q≥0 : (n : ℕ)(q : R) → q > 0r → n ⋆ q ≥ 0r
  n⋆q≥0 zero q _ = ≤-refl (sym (0⋆q≡0 q))
  n⋆q≥0 (suc n) q q>0 = Ord.<-≤-weaken 0r (suc n ⋆ q) (sucn⋆q>0 n q q>0)


  {-

    Difference and Equality

  -}

  diff≡0→x≡y : x - y ≡ 0r → x ≡ y
  diff≡0→x≡y {y = y} x-y≡0 = sym (helper19 _ _) ∙ (λ i → x-y≡0 i + y) ∙ +IdL _

  x≡y→diff≡0 : x ≡ y → x - y ≡ 0r
  x≡y→diff≡0 {y = y} x≡y = (λ i → x≡y i - y) ∙ +InvR _

  x-y≡-[y-x] : x - y ≡ - (y - x)
  x-y≡-[y-x] = helper2 _ _


  {-

    No Infinitesimal

  -}

  infinitesimal : x ≥ 0r → ((ε : R) → (ε > 0r) → x < ε) → x ≡ 0r
  infinitesimal {x = x} x≥0 ∀ε>x = ≤-asym (¬<→≥ ¬x>0) x≥0
    where
    ¬x>0 : ¬ x > 0r
    ¬x>0 x>0 = <-asym (∀ε>x x x>0) (∀ε>x x x>0)


  {-

    Minimum and Maximum of Two Elements

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
