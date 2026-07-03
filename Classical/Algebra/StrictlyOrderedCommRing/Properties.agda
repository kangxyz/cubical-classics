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
open import Cubical.Algebra.OrderedCommRing as CubicalOrderedCommRing
  using (OrderedCommRing ; OrderedCommRingStr)
open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Relation.Nullary

open import Classical.Algebra.StrictlyOrderedCommRing.Base hiding (Trichotomy ; lt ; eq ; gt)
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

    helper5 : (x y z w : 𝓡 .fst) → (y - x) + (w - z) ≡ (y + w) - (x + z)
    helper5 _ _ _ _ = solve! 𝓡

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

    helper12 : (x y z : 𝓡 .fst) → y - x ≡ (y + z) - (x + z)
    helper12 _ _ _ = solve! 𝓡

    helper13 : (x y z : 𝓡 .fst) → y - x ≡ (z + y) - (z + x)
    helper13 _ _ _ = solve! 𝓡

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

  _<ᶜ_ : R → R → Type ℓ'
  _<ᶜ_ = Ord._<_

  _≤ᶜ_ : R → R → Type ℓ'
  _≤ᶜ_ = Ord._≤_

  infix 4 _<ᶜ_ _≤ᶜ_

  _>0 : R → Type ℓ'
  x >0 = 0r <ᶜ x

  isProp>0 : (x : R) → isProp (x >0)
  isProp>0 x = Ord.is-prop-valued< 0r x

  >0-1r : 1r >0
  >0-1r = Ord.0<1

  -Pos→Neg : (- x) >0 → x <ᶜ 0r
  -Pos→Neg {x = x} -x>0 =
    transport (λ i → +IdL x i <ᶜ +InvL x i) (Ord.+MonoR< 0r (- x) x -x>0)

  >0-asym : (x : R) → x >0 → (- x) >0 → ⊥
  >0-asym x x>0 -x>0 = Ord.is-asym 0r x x>0 (-Pos→Neg -x>0)

  >0-arefl : (x : R) → x >0 → x ≡ 0r → ⊥
  >0-arefl x x>0 x≡0 = Ord.is-irrefl 0r (subst (0r <ᶜ_) x≡0 x>0)

  >0-+ : (x y : R) → x >0 → y >0 → (x + y) >0
  >0-+ x y x>0 y>0 =
    Ord.is-trans< 0r y (x + y) y>0
      (subst (_<ᶜ x + y) (+IdL y) (Ord.+MonoR< 0r x y x>0))

  >0-· : (x y : R) → x >0 → y >0 → (x · y) >0
  >0-· x y x>0 y>0 =
    subst (_<ᶜ x · y) (0LeftAnnihilates y) (Ord.·MonoR< 0r x y y>0 x>0)

  <ᶜ→Diff>0 : {x y : R} → x <ᶜ y → (y - x) >0
  <ᶜ→Diff>0 {x = x} {y = y} x<ᶜy =
    transport (λ i → +InvR x i <ᶜ y - x) (Ord.+MonoR< x y (- x) x<ᶜy)

  Diff>0→<ᶜ : {x y : R} → (y - x) >0 → x <ᶜ y
  Diff>0→<ᶜ {x = x} {y = y} y-x>0 =
    transport (λ i → +IdL x i <ᶜ helper4 x y i) (Ord.+MonoR< 0r (y - x) x y-x>0)


  {-

    Strict Ordering

  -}

  _>_ : R → R → Type ℓ'
  x > y = (x - y) >0

  _<_ : R → R → Type ℓ'
  x < y = y > x

  infix 4 _>_ _<_

  isProp< : {x y : R} → isProp (x < y)
  isProp< {x = x} {y = y} = isProp>0 (y - x)

  >0≡>0r : (x : R) → (x >0) ≡ (x > 0r)
  >0≡>0r x i = (helper1 x i) >0


  <-asym : x < y → x > y → ⊥
  <-asym {x = x} {y = y} x<y x>y = >0-asym (y - x) x<y (subst (_>0) (helper2 x y) x>y)

  <-arefl : x < y → x ≡ y → ⊥
  <-arefl {x = x} {y = y} x<y x≡y = <-asym {x = x} {y = y} x<y (transport (λ i → x≡y i < x≡y (~ i)) x<y)

  >-arefl : x > y → x ≡ y → ⊥
  >-arefl x>y x≡y = <-arefl x>y (sym x≡y)

  <-trans : x < y → y < z → x < z
  <-trans {x = x} {y = y} {z = z} x<y y<z = subst (_>0) (helper3 x y z) (>0-+ (z - y) (y - x) y<z x<y)


  data Trichotomy (x y : R) : Type (ℓ-max ℓ ℓ') where
    lt : x < y → Trichotomy x y
    eq : x ≡ y → Trichotomy x y
    gt : x > y → Trichotomy x y

  isPropTrichotomy : (x y : R) → isProp (Trichotomy x y)
  isPropTrichotomy x y (lt x<y) (lt x<y') i = lt (isProp< x<y x<y' i)
  isPropTrichotomy x y (eq x≡y) (eq x≡y') i = eq (isSetR _ _ x≡y x≡y' i)
  isPropTrichotomy x y (gt x>y) (gt x>y') i = gt (isProp< x>y x>y' i)
  isPropTrichotomy x y (lt x<y) (eq x≡y) = Empty.rec (<-arefl x<y x≡y)
  isPropTrichotomy x y (lt x<y) (gt x>y) = Empty.rec (<-asym x<y x>y)
  isPropTrichotomy x y (gt x>y) (eq x≡y) = Empty.rec (<-arefl x>y (sym x≡y))
  isPropTrichotomy x y (gt x>y) (lt x<y) = Empty.rec (<-asym x<y x>y)
  isPropTrichotomy x y (eq x≡y) (lt x<y) = Empty.rec (<-arefl x<y x≡y)
  isPropTrichotomy x y (eq x≡y) (gt x>y) = Empty.rec (<-arefl x>y (sym x≡y))

  trichotomy : (x y : R) → Trichotomy x y
  trichotomy x y with trichotomyᶜ x y
  ... | StrictBase.lt x<ᶜy = lt (<ᶜ→Diff>0 x<ᶜy)
  ... | StrictBase.eq x≡y = eq x≡y
  ... | StrictBase.gt y<ᶜx = gt (<ᶜ→Diff>0 y<ᶜx)

  dec< : (x y : R) → Dec (x < y)
  dec< x y with trichotomy x y
  ... | lt x<y = yes x<y
  ... | eq x≡y = no (λ p → <-arefl p x≡y)
  ... | gt x>y = no (λ p → <-asym  p x>y)


  +-Pres< : x < y → z < w → x + z < y + w
  +-Pres< x<y z<w = subst (_>0) (helper5 _ _ _ _) (>0-+ _ _ x<y z<w)

  +-lPres< : x < y → z + x < z + y
  +-lPres< {z = z} x<y = subst (_>0) (helper13 _ _ z) x<y

  +-rPres< : x < y → x + z < y + z
  +-rPres< {z = z} x<y = subst (_>0) (helper12 _ _ z) x<y


  -Reverse< : x < y → - x > - y
  -Reverse< x<y = subst (_>0) (helper6 _ _) x<y

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
  +-rPos→> {x = x} {y = y} x>0 = subst (y + x >_) (+IdR y) (+-lPres< {z = y} x>0)

  +-rNeg→< : x < 0r → y + x < y
  +-rNeg→< {x = x} {y = y} x<0 = subst (_> y + x) (+IdR y) (+-lPres< {z = y} x<0)

  -rPos→< : x > 0r → y - x < y
  -rPos→< x>0 = +-rNeg→< (-Reverse>0 x>0)

  -rNeg→> : x < 0r → y - x > y
  -rNeg→> x<0 = +-rPos→> (-Reverse<0 x<0)


  ·-lPosPres< : x > 0r → y < z → x · y < x · z
  ·-lPosPres< x>0 y<z = subst (_>0) (helper9  _ _ _) (>0-· _ _ x>0 y<z)

  ·-rPosPres< : x > 0r → y < z → y · x < z · x
  ·-rPosPres< x>0 y<z = subst (_>0) (helper10 _ _ _) (>0-· _ _ y<z x>0)

  ·-PosPres> : x > 0r → z > 0r → x < y → z < w → x · z < y · w
  ·-PosPres> x>0 z>0 x<y z<w = <-trans (·-rPosPres< z>0 x<y) (·-lPosPres< (<-trans x>0 x<y) z<w)


  +-Pres>0 : x > 0r → y > 0r → x + y > 0r
  +-Pres>0 {x = x} {y = y} x>0 y>0 = subst (x + y >_) (+IdR _) (+-Pres< x>0 y>0)

  +-Pres<0 : x < 0r → y < 0r → x + y < 0r
  +-Pres<0 {x = x} {y = y} x<0 y<0 = subst (x + y <_) (+IdR _) (+-Pres< x<0 y<0)

  ·-Pres>0 : x > 0r → y > 0r → x · y > 0r
  ·-Pres>0 {x = x} {y = y} = transport (λ i → >0≡>0r x i → >0≡>0r y i → >0≡>0r (x · y) i) (>0-· x y)


  >→Diff>0 : x > y → x - y > 0r
  >→Diff>0 x>y = transport (>0≡>0r _) x>y

  <→Diff<0 : x < y → x - y < 0r
  <→Diff<0 x<y = subst (_< 0r) (sym (helper2 _ _)) (-Reverse>0 (transport (>0≡>0r _) x<y))

  Diff>0→> : x - y > 0r → x > y
  Diff>0→> x-y>0 = transport (sym (>0≡>0r _)) x-y>0

  Diff<0→< : x - y < 0r → x < y
  Diff<0→< x-y<0 = transport (sym (>0≡>0r _)) (subst (_> 0r) (sym (helper2 _ _)) (-Reverse<0 x-y<0))


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
  ·-Pos·>1→> x>0 y>1 = subst (_>0) (helper15 _ _) (>0-· _ _ x>0 y>1)


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


  {-

    Non-strict Ordering

  -}

  _≤_ : R → R → Type (ℓ-max ℓ ℓ')
  x ≤ y = (x < y) ⊎ (x ≡ y)

  _≥_ : R → R → Type (ℓ-max ℓ ℓ')
  x ≥ y = y ≤ x

  infix 4 _≥_ _≤_

  isProp≤ : isProp (x ≤ y)
  isProp≤ {x = x} {y = y} (inl x<y) (inl x<y') i = inl (isProp< {x} {y} x<y x<y' i)
  isProp≤ (inr x≡y) (inr x≡y') i = inr (isSetR _ _ x≡y x≡y' i)
  isProp≤ (inl x<y) (inr x≡y) = Empty.rec (<-arefl x<y x≡y)
  isProp≤ (inr x≡y) (inl x<y) = Empty.rec (<-arefl x<y x≡y)


  ≤-asym : x ≤ y → x ≥ y → x ≡ y
  ≤-asym (inr x≡y) _ = x≡y
  ≤-asym _ (inr y≡x) = sym y≡x
  ≤-asym {x = x} {y = y} (inl x<y) (inl x>y) = Empty.rec (<-asym {x = x} {y = y} x<y x>y)

  ≤-refl : x ≡ y → x ≤ y
  ≤-refl x≡y = inr x≡y

  ≤-trans : x ≤ y → y ≤ z → x ≤ z
  ≤-trans {z = z} (inr x≡y) y≤z = subst (_≤ z) (sym x≡y) y≤z
  ≤-trans {x = x} x≤y (inr y≡z) = subst (x ≤_) y≡z x≤y
  ≤-trans {x = x} {y = y} {z = z} (inl x<y) (inl y<z) = inl (<-trans {x = x} {y = y} {z = z} x<y y<z)

  ≤-total : (x y : R) → (x ≤ y) ⊎ (y ≤ x)
  ≤-total x y with trichotomy x y
  ... | lt x<y = inl (inl x<y)
  ... | eq x≡y = inl (inr x≡y)
  ... | gt x>y = inr (inl x>y)


  +-Pres≥0 : x ≥ 0r → y ≥ 0r → (x + y) ≥ 0r
  +-Pres≥0 {x = x} {y = y} (inl x>0) (inl y>0) = inl (+-Pres>0 {x = x} {y = y} x>0 y>0)
  +-Pres≥0 {x = x} {y = y} (inr 0≡x) y≥0 = subst (_≥ 0r) y≡x+y y≥0
    where y≡x+y : y ≡ x + y
          y≡x+y = sym (+IdL _) ∙ (λ i → 0≡x i + y)
  +-Pres≥0 {x = x} {y = y} x≥0 (inr 0≡y) = subst (_≥ 0r) x≡x+y x≥0
    where x≡x+y : x ≡ x + y
          x≡x+y = sym (+IdR _) ∙ (λ i → x + 0≡y i)

  ·-Pres≥0 : x ≥ 0r → y ≥ 0r → (x · y) ≥ 0r
  ·-Pres≥0 {x = x} {y = y} (inl x>0) (inl y>0) = inl (·-Pres>0 {x = x} {y = y} x>0 y>0)
  ·-Pres≥0 {x = x} {y = y} (inr 0≡x) y≥0 = inr 0≡x·y
    where 0≡x·y : 0r ≡ x · y
          0≡x·y = sym (0LeftAnnihilates  y) ∙ (λ i → 0≡x i · y)
  ·-Pres≥0 {x = x} {y = y} x≥0 (inr 0≡y) = inr 0≡x·y
    where 0≡x·y : 0r ≡ x · y
          0≡x·y = sym (0RightAnnihilates x) ∙ (λ i → x · 0≡y i)


  +-rPos→≥ : x ≥ 0r → y + x ≥ y
  +-rPos→≥ (inl x>0) = inl (+-rPos→> x>0)
  +-rPos→≥ {y = y} (inr 0≡x) = inr (sym (+IdR y) ∙ (λ i → y + 0≡x i))

  +-rNeg→≤ : x ≤ 0r → y + x ≤ y
  +-rNeg→≤ (inl x<0) = inl (+-rNeg→< x<0)
  +-rNeg→≤ {y = y} (inr x≡0) = inr ((λ i → y + x≡0 i) ∙ +IdR y)


  ≥→Diff≥0 : x ≥ y → x - y ≥ 0r
  ≥→Diff≥0 (inl x>y) = inl (>→Diff>0 x>y)
  ≥→Diff≥0 {y = y} (inr x≡y) = inr (sym (+InvR y) ∙ (λ i → x≡y i - y))

  ≤→Diff≤0 : x ≤ y → x - y ≤ 0r
  ≤→Diff≤0 (inl x<y) = inl (<→Diff<0 x<y)
  ≤→Diff≤0 {y = y} (inr y≡x) = inr ((λ i → y≡x i - y) ∙ +InvR y)

  Diff≥0→≥ : x - y ≥ 0r → x ≥ y
  Diff≥0→≥ (inl x-y>0) = inl (Diff>0→> x-y>0)
  Diff≥0→≥ {x = x} {y = y} (inr x-y≡0) = inr (sym (+IdL y) ∙ (λ i → x-y≡0 i + y) ∙ helper19 x y)


  +-Pres≤ : x ≤ y → z ≤ w → x + z ≤ y + w
  +-Pres≤ x≤y z≤w = Diff≥0→≥ (subst (_≥ 0r) (helper5 _ _ _ _) (+-Pres≥0 (≥→Diff≥0 x≤y) (≥→Diff≥0 z≤w)))

  +-lPres≤ : x ≤ y → z + x ≤ z + y
  +-lPres≤ {z = z} x≤y = Diff≥0→≥ (subst (_≥ 0r) (helper13 _ _ z) (≥→Diff≥0 x≤y))

  +-rPres≤ : x ≤ y → x + z ≤ y + z
  +-rPres≤ {z = z} x≤y = Diff≥0→≥ (subst (_≥ 0r) (helper12 _ _ z) (≥→Diff≥0 x≤y))


  -Reverse≤ : x ≤ y → - x ≥ - y
  -Reverse≤ (inl x<y) = inl (-Reverse< x<y)
  -Reverse≤ (inr x≡y) = inr (λ i → - x≡y (~ i))

  -lReverse≤ : - x ≤ y → x ≥ - y
  -lReverse≤ {x = x} {y = y} -x≥y = subst (_≥ - y) (-Idempotent x) (-Reverse≤ -x≥y)

  -rReverse≤ : x ≤ - y → - x ≥ y
  -rReverse≤ {x = x} {y = y} x≤-y = subst (_≤ - x) (-Idempotent y) (-Reverse≤ x≤-y)


  ·-lPosPres≤ : x ≥ 0r → y ≤ z → x · y ≤ x · z
  ·-lPosPres≤ (inl 0<x) (inl y<z) = inl (·-lPosPres< 0<x y<z)
  ·-lPosPres≤ {y = y} {z = z} (inr 0≡x) _ =
    inr ((λ i → 0≡x (~ i) · y) ∙ 0LeftAnnihilates _ ∙ sym (0LeftAnnihilates _) ∙ (λ i → 0≡x i · z))
  ·-lPosPres≤ {x = x} _ (inr y≡z) = inr (λ i → x · y≡z i)

  ·-rPosPres≤ : x ≥ 0r → y ≤ z → y · x ≤ z · x
  ·-rPosPres≤ {x = x} {y = y} {z = z} x≥0 y≤z = transport (λ i → ·Comm x y i ≤ ·Comm x z i) (·-lPosPres≤ x≥0 y≤z)

  ·-PosPres≥ : x ≥ 0r → z ≥ 0r → x ≤ y → z ≤ w → x · z ≤ y · w
  ·-PosPres≥ x≥0 z≥0 x≤y z≤w = ≤-trans (·-rPosPres≤ z≥0 x≤y) (·-lPosPres≤ (≤-trans x≥0 x≤y) z≤w)


  {-

    Strict & Non-strict Together

  -}

  <≤-asym : x < y → y ≤ x → ⊥
  <≤-asym x<y (inl x>y) = <-asym  x<y x>y
  <≤-asym x<y (inr x≡y) = <-arefl x<y (sym x≡y)


  <≤-trans : x < y → y ≤ z → x < z
  <≤-trans x<y (inl y<z) = <-trans x<y y<z
  <≤-trans {x = x} x<y (inr y≡z) = subst (x <_) y≡z x<y

  ≤<-trans : x ≤ y → y < z → x < z
  ≤<-trans (inl x<y) y<z = <-trans x<y y<z
  ≤<-trans {z = z} (inr x≡y) y<z = subst (_< z) (sym x≡y) y<z


  <≤-total : (x y : R) → (x < y) ⊎ (y ≤ x)
  <≤-total x y with trichotomy x y
  ... | lt x<y = inl x<y
  ... | eq x≡y = inr (inr (sym x≡y))
  ... | gt x>y = inr (inl x>y)


  ¬<→≥ : ¬ x < y → x ≥ y
  ¬<→≥ {x = x} {y = y} ¬x<y with <≤-total x y
  ... | inl x<y = Empty.rec (¬x<y x<y)
  ... | inr x≥y = x≥y

  ¬≤→> : ¬ x ≤ y → x > y
  ¬≤→> {x = x} {y = y} ¬x≤y with <≤-total y x
  ... | inl x>y = x>y
  ... | inr x≤y = Empty.rec (¬x≤y x≤y)

  ≤+¬≡→< : x ≤ y → ¬ x ≡ y → x < y
  ≤+¬≡→< (inl x<y) _ = x<y
  ≤+¬≡→< (inr x≡y) ¬x≡y = Empty.rec (¬x≡y x≡y)

  ≤+¬<→≡ : x ≤ y → ¬ x < y → x ≡ y
  ≤+¬<→≡ (inl x<y) ¬x<y = Empty.rec (¬x<y x<y)
  ≤+¬<→≡ (inr x≡y) _ = x≡y


  ·-PosPres>≥ : x > 0r → z > 0r → x < y → z ≤ w → x · z < y · w
  ·-PosPres>≥ x>0 z>0 x<y (inl z<w) = ·-PosPres> x>0 z>0 x<y z<w
  ·-PosPres>≥ {x = x} {z = z} {y = y} x>0 z>0 x<y (inr z≡w) =
    subst (λ w → x · z < y · w) z≡w (·-rPosPres< z>0 x<y)

  ·-PosPres≥0>0 : x ≥ 0r → z ≥ 0r → y > 0r → w > 0r → x < y → z < w → x · z < y · w
  ·-PosPres≥0>0 (inl x>0) (inl z>0) _ _ x<y z<w = ·-PosPres> x>0 z>0 x<y z<w
  ·-PosPres≥0>0 {z = z} {y = y} {w = w} (inr 0≡x) _ y>0 w>0 _ _ =
    subst (y · w >_) (sym (0LeftAnnihilates _) ∙ (λ i → 0≡x i · z)) (·-Pres>0 y>0 w>0)
  ·-PosPres≥0>0 {x = x} {y = y} {w = w} _ (inr 0≡z) y>0 w>0 _ _ =
    subst (y · w >_) (sym (0RightAnnihilates _) ∙ (λ i → x · 0≡z i)) (·-Pres>0 y>0 w>0)


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
  1>0 = subst (_>0) (sym helper16) (>0-1r)


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
  ℕ→R-Pos≥0 zero = inr refl
  ℕ→R-Pos≥0 (suc n) = inl (ℕ→R-PosSuc>0 n)

  ℕ→R-NegSuc<0 : (n : ℕ) → ℕ→R-Neg (suc n) < 0r
  ℕ→R-NegSuc<0 n = -Reverse>0 (ℕ→R-PosSuc>0 n)

  ℕ→R-Neg≤0 : (n : ℕ) → ℕ→R-Neg n ≤ 0r
  ℕ→R-Neg≤0 zero = inr 0Selfinverse
  ℕ→R-Neg≤0 (suc n) = inl (ℕ→R-NegSuc<0 n)


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
  n⋆q≥0 zero q _ = inr (sym (0⋆q≡0 q))
  n⋆q≥0 (suc n) q q>0 = inl (sucn⋆q>0 n q q>0)


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
