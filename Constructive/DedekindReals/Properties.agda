{-

Order and approximation lemmas for constructive Dedekind reals

The rational cut presentation remains level-polymorphic.  No Oracle, LEM, or
propositional resizing is used here.

-}
{-# OPTIONS --safe #-}
module Constructive.DedekindReals.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals using (ℚ)
import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Nullary using (¬_)
import Cubical.Relation.Binary.Order.StrictOrder as StrictOrder

open import Constructive.DedekindReals.Base public
import Constructive.Rationals as ℚExtra

private
  variable
    ℓ : Level

-- The same rational cut, lifted to an arbitrary predicate universe
ℚ→𝔻 : (ℓ : Level) → ℚ → DedekindReal ℓ
ℚ→𝔻 ℓ q .lower p =
  Lift ℓ (p ℚOrder.< q) ,
  isOfHLevelLift 1 (ℚOrder.isProp< p q)
ℚ→𝔻 ℓ q .upper p =
  Lift ℓ (q ℚOrder.< p) ,
  isOfHLevelLift 1 (ℚOrder.isProp< q p)
ℚ→𝔻 ℓ q .isDedekindReal .IsDedekindReal.lower-inhabited =
  ∣ q ℚ.- ℚExtra.1ℚ , lift (ℚExtra.q-1<q q) ∣₁
ℚ→𝔻 ℓ q .isDedekindReal .IsDedekindReal.upper-inhabited =
  ∣ q ℚ.+ ℚExtra.1ℚ , lift (ℚExtra.q<q+1 q) ∣₁
ℚ→𝔻 ℓ q .isDedekindReal .IsDedekindReal.lower-closed =
  λ p r p<r r<q → lift (ℚOrder.isTrans< p r q p<r (Lift.lower r<q))
ℚ→𝔻 ℓ q .isDedekindReal .IsDedekindReal.upper-closed =
  λ p r p<r q<p → lift (ℚOrder.isTrans< q p r (Lift.lower q<p) p<r)
ℚ→𝔻 ℓ q .isDedekindReal .IsDedekindReal.lower-rounded =
  λ p p<q →
    Prop.rec squash₁
      (λ (r , p<r , r<q) → ∣ r , p<r , lift r<q ∣₁)
      (ℚExtra.dense {p = p} {q = q} (Lift.lower p<q))
ℚ→𝔻 ℓ q .isDedekindReal .IsDedekindReal.upper-rounded =
  λ p q<p →
    Prop.rec squash₁
      (λ (r , q<r , r<p) → ∣ r , r<p , lift q<r ∣₁)
      (ℚExtra.dense {p = q} {q = p} (Lift.lower q<p))
ℚ→𝔻 ℓ q .isDedekindReal .IsDedekindReal.disjoint =
  λ p p<q q<p → ℚOrder.isAsym< p q (Lift.lower p<q) (Lift.lower q<p)
ℚ→𝔻 ℓ q .isDedekindReal .IsDedekindReal.located =
  λ p r p<r →
    Prop.rec squash₁
      (λ where
        (Sum.inl p<q) → ∣ Sum.inl (lift p<q) ∣₁
        (Sum.inr q<r) → ∣ Sum.inr (lift q<r) ∣₁)
      (ℚOrder.isWeaklyLinear< p r q p<r)


-- The order and strict order used constructively for Dedekind reals
module Order {ℓ : Level} where
  open DedekindReal

  _≤_ : DedekindReal ℓ → DedekindReal ℓ → Type ℓ
  x ≤ y = (q : ℚ) → q ∈ lower x → q ∈ lower y

  _<_ : DedekindReal ℓ → DedekindReal ℓ → Type ℓ
  x < y = ∥ Σ[ q ∈ ℚ ] (q ∈ upper x) × (q ∈ lower y) ∥₁

  _#_ : DedekindReal ℓ → DedekindReal ℓ → Type ℓ
  x # y = (x < y) ⊎ (y < x)

  infix 4 _≤_ _<_ _#_

  isProp≤ : (x y : DedekindReal ℓ) → isProp (x ≤ y)
  isProp≤ x y = isPropΠ2 λ q _ → isProp∈ (lower y) q

  isProp< : (x y : DedekindReal ℓ) → isProp (x < y)
  isProp< x y = squash₁

  ≡→≤ : {x y : DedekindReal ℓ} → x ≡ y → x ≤ y
  ≡→≤ x≡y q q∈Lx = subst (λ z → q ∈ lower z) x≡y q∈Lx

  ≤-refl : (x : DedekindReal ℓ) → x ≤ x
  ≤-refl x q q∈Lx = q∈Lx

  ≤-trans : (x y z : DedekindReal ℓ) → x ≤ y → y ≤ z → x ≤ z
  ≤-trans x y z x≤y y≤z q q∈Lx = y≤z q (x≤y q q∈Lx)

  lower<upper :
    (x : DedekindReal ℓ) (p q : ℚ) →
    p ∈ lower x →
    q ∈ upper x →
    p ℚOrder.< q
  lower<upper x p q p∈L q∈U with p ℚOrder.≟ q
  ... | ℚOrder.lt p<q = p<q
  ... | ℚOrder.eq p≡q =
    Empty.rec (disjoint x q (subst (λ r → r ∈ lower x) p≡q p∈L) q∈U)
  ... | ℚOrder.gt q<p =
    Empty.rec (disjoint x p p∈L (upper-closed x q p q<p q∈U))

  lower-closed-≤ :
    (x : DedekindReal ℓ) (p q : ℚ) →
    p ℚOrder.≤ q → q ∈ lower x → p ∈ lower x
  lower-closed-≤ x p q p≤q q∈L with p ℚOrder.≟ q
  ... | ℚOrder.lt p<q = lower-closed x p q p<q q∈L
  ... | ℚOrder.eq p≡q = subst (λ r → r ∈ lower x) (sym p≡q) q∈L
  ... | ℚOrder.gt q<p = Empty.rec (ℚOrder.≤→≯ p q p≤q q<p)

  upper-closed-≤ :
    (x : DedekindReal ℓ) (p q : ℚ) →
    p ℚOrder.≤ q → p ∈ upper x → q ∈ upper x
  upper-closed-≤ x p q p≤q p∈U with p ℚOrder.≟ q
  ... | ℚOrder.lt p<q = upper-closed x p q p<q p∈U
  ... | ℚOrder.eq p≡q = subst (λ r → r ∈ upper x) p≡q p∈U
  ... | ℚOrder.gt q<p = Empty.rec (ℚOrder.≤→≯ p q p≤q q<p)

  lower→ℚ< :
    (x : DedekindReal ℓ) (q : ℚ) →
    q ∈ lower x →
    ℚ→𝔻 ℓ q < x
  lower→ℚ< x q q∈Lx =
    Prop.rec squash₁
      (λ (r , q<r , r∈Lx) → ∣ r , lift q<r , r∈Lx ∣₁)
      (lower-rounded x q q∈Lx)

  ℚ<→lower :
    (x : DedekindReal ℓ) (q : ℚ) →
    ℚ→𝔻 ℓ q < x →
    q ∈ lower x
  ℚ<→lower x q =
    Prop.rec (isProp∈ (lower x) q)
      (λ (r , q<r , r∈Lx) →
        lower-closed x q r (Lift.lower q<r) r∈Lx)

  upper→<ℚ :
    (x : DedekindReal ℓ) (q : ℚ) →
    q ∈ upper x →
    x < ℚ→𝔻 ℓ q
  upper→<ℚ x q q∈Ux =
    Prop.rec squash₁
      (λ (r , r<q , r∈Ux) → ∣ r , r∈Ux , lift r<q ∣₁)
      (upper-rounded x q q∈Ux)

  <ℚ→upper :
    (x : DedekindReal ℓ) (q : ℚ) →
    x < ℚ→𝔻 ℓ q →
    q ∈ upper x
  <ℚ→upper x q =
    Prop.rec (isProp∈ (upper x) q)
      (λ (r , r∈Ux , r<q) →
        upper-closed x r q (Lift.lower r<q) r∈Ux)

  lower⇔ℚ< :
    (x : DedekindReal ℓ) (q : ℚ) →
    (q ∈ lower x → ℚ→𝔻 ℓ q < x)
    ×
    (ℚ→𝔻 ℓ q < x → q ∈ lower x)
  lower⇔ℚ< x q = lower→ℚ< x q , ℚ<→lower x q

  upper⇔<ℚ :
    (x : DedekindReal ℓ) (q : ℚ) →
    (q ∈ upper x → x < ℚ→𝔻 ℓ q)
    ×
    (x < ℚ→𝔻 ℓ q → q ∈ upper x)
  upper⇔<ℚ x q = upper→<ℚ x q , <ℚ→upper x q

  rational-between :
    (x y : DedekindReal ℓ) →
    x < y →
    ∥ Σ[ q ∈ ℚ ] (x < ℚ→𝔻 ℓ q) × (ℚ→𝔻 ℓ q < y) ∥₁
  rational-between x y =
    Prop.rec squash₁
      (λ (q , q∈Ux , q∈Ly) →
        ∣ q , upper→<ℚ x q q∈Ux , lower→ℚ< y q q∈Ly ∣₁)

  rational-located :
    (x : DedekindReal ℓ) (p q : ℚ) →
    p ℚOrder.< q →
    ∥ (ℚ→𝔻 ℓ p < x) ⊎ (x < ℚ→𝔻 ℓ q) ∥₁
  rational-located x p q p<q =
    Prop.rec squash₁
      (λ where
        (Sum.inl p∈Lx) → ∣ Sum.inl (lower→ℚ< x p p∈Lx) ∣₁
        (Sum.inr q∈Ux) → ∣ Sum.inr (upper→<ℚ x q q∈Ux) ∣₁)
      (located x p q p<q)

  upper-inclusion-from-lower :
    (x y : DedekindReal ℓ) →
    y ≤ x →
    upper x ⊆ upper y
  upper-inclusion-from-lower x y y≤x q q∈Ux =
    Prop.rec (isProp∈ (upper y) q)
      (λ (r , r<q , r∈Ux) →
        Prop.rec (isProp∈ (upper y) q)
          (λ where
            (Sum.inl r∈Ly) →
              Empty.rec (disjoint x r (y≤x r r∈Ly) r∈Ux)
            (Sum.inr q∈Uy) → q∈Uy)
          (located y r q r<q))
      (upper-rounded x q q∈Ux)

  ≤-antisym : (x y : DedekindReal ℓ) → x ≤ y → y ≤ x → x ≡ y
  ≤-antisym x y x≤y y≤x =
    realExt x y x≤y y≤x
      (upper-inclusion-from-lower x y y≤x)
      (upper-inclusion-from-lower y x x≤y)

  <→≤ : (x y : DedekindReal ℓ) → x < y → x ≤ y
  <→≤ x y x<y q q∈Lx =
    Prop.rec (isProp∈ (lower y) q)
      (λ (r , r∈Ux , r∈Ly) →
        lower-closed y q r (lower<upper x q r q∈Lx r∈Ux) r∈Ly)
      x<y

  <-trans : (x y z : DedekindReal ℓ) → x < y → y < z → x < z
  <-trans x y z x<y y<z =
    Prop.rec squash₁
      (λ (q , q∈Ux , q∈Ly) →
        Prop.rec squash₁
          (λ (r , r∈Uy , r∈Lz) →
            Prop.rec squash₁
              (λ (s , q<s , s<r) →
                ∣ s
                , upper-closed x q s q<s q∈Ux
                , lower-closed z s r s<r r∈Lz
                ∣₁)
              (ℚExtra.dense
                {p = q} {q = r}
                (lower<upper y q r q∈Ly r∈Uy)))
          y<z)
      x<y

  ≤-<-trans : (x y z : DedekindReal ℓ) → x ≤ y → y < z → x < z
  ≤-<-trans x y z x≤y y<z =
    Prop.rec squash₁
      (λ (q , q∈Uy , q∈Lz) →
        ∣ q , upper-inclusion-from-lower y x x≤y q q∈Uy , q∈Lz ∣₁)
      y<z

  <-≤-trans : (x y z : DedekindReal ℓ) → x < y → y ≤ z → x < z
  <-≤-trans x y z x<y y≤z =
    Prop.rec squash₁
      (λ (q , q∈Ux , q∈Ly) → ∣ q , q∈Ux , y≤z q q∈Ly ∣₁)
      x<y

  <≤-asym : (x y : DedekindReal ℓ) → x < y → y ≤ x → ⊥
  <≤-asym x y x<y y≤x =
    Prop.rec Empty.isProp⊥
      (λ (q , q∈Ux , q∈Ly) → disjoint x q (y≤x q q∈Ly) q∈Ux)
      x<y

  <-irrefl : (x : DedekindReal ℓ) → ¬ x < x
  <-irrefl x x<x = <≤-asym x x x<x (≤-refl x)

  <-asym : (x y : DedekindReal ℓ) → x < y → ¬ y < x
  <-asym x y x<y y<x = <≤-asym x y x<y (<→≤ y x y<x)

  isWeaklyLinear< :
    (x y z : DedekindReal ℓ) → x < y → ∥ (x < z) ⊎ (z < y) ∥₁
  isWeaklyLinear< x y z x<y =
    Prop.rec squash₁
      (λ (q , q∈Ux , q∈Ly) →
        Prop.rec squash₁
          (λ (r , q<r , r∈Ly) →
            Prop.rec squash₁
              (λ where
                (Sum.inl q∈Lz) → ∣ Sum.inl ∣ q , q∈Ux , q∈Lz ∣₁ ∣₁
                (Sum.inr r∈Uz) → ∣ Sum.inr ∣ r , r∈Uz , r∈Ly ∣₁ ∣₁)
              (located z q r q<r))
          (lower-rounded y q q∈Ly))
      x<y

  ≤→¬> : (x y : DedekindReal ℓ) → x ≤ y → ¬ y < x
  ≤→¬> x y x≤y y<x = <≤-asym y x y<x x≤y

  ¬>→≤ : (x y : DedekindReal ℓ) → ¬ y < x → x ≤ y
  ¬>→≤ x y ¬y<x q q∈Lx =
    Prop.rec (isProp∈ (lower y) q)
      (λ (r , q<r , r∈Lx) →
        Prop.rec (isProp∈ (lower y) q)
          (λ where
            (Sum.inl q∈Ly) → q∈Ly
            (Sum.inr r∈Uy) → Empty.rec (¬y<x ∣ r , r∈Uy , r∈Lx ∣₁))
          (located y q r q<r))
      (lower-rounded x q q∈Lx)

  ≤⇔¬> : (x y : DedekindReal ℓ) → (x ≤ y → ¬ y < x) × (¬ y < x → x ≤ y)
  ≤⇔¬> x y = ≤→¬> x y , ¬>→≤ x y

  isStrictOrder< : StrictOrder.IsStrictOrder _<_
  isStrictOrder< =
    StrictOrder.isstrictorder
      isSetDedekindReal
      isProp<
      <-irrefl
      <-trans
      <-asym
      isWeaklyLinear<

  isProp# : (x y : DedekindReal ℓ) → isProp (x # y)
  isProp# x y = Sum.isProp⊎ (isProp< x y) (isProp< y x) (<-asym x y)

  #-irrefl : (x : DedekindReal ℓ) → ¬ x # x
  #-irrefl x (Sum.inl x<x) = <-irrefl x x<x
  #-irrefl x (Sum.inr x<x) = <-irrefl x x<x

  #-sym : (x y : DedekindReal ℓ) → x # y → y # x
  #-sym x y (Sum.inl x<y) = Sum.inr x<y
  #-sym x y (Sum.inr y<x) = Sum.inl y<x

  #-cotrans :
    (x y z : DedekindReal ℓ) →
    x # y → ∥ (x # z) ⊎ (z # y) ∥₁
  #-cotrans x y z (Sum.inl x<y) =
    Prop.rec squash₁
      (λ where
        (Sum.inl x<z) → ∣ Sum.inl (Sum.inl x<z) ∣₁
        (Sum.inr z<y) → ∣ Sum.inr (Sum.inl z<y) ∣₁)
      (isWeaklyLinear< x y z x<y)
  #-cotrans x y z (Sum.inr y<x) =
    Prop.rec squash₁
      (λ where
        (Sum.inl y<z) → ∣ Sum.inr (Sum.inr y<z) ∣₁
        (Sum.inr z<x) → ∣ Sum.inl (Sum.inr z<x) ∣₁)
      (isWeaklyLinear< y x z y<x)

  #-tight : (x y : DedekindReal ℓ) → ¬ x # y → x ≡ y
  #-tight x y ¬x#y =
    ≤-antisym x y
      (¬>→≤ x y (λ y<x → ¬x#y (Sum.inr y<x)))
      (¬>→≤ y x (λ x<y → ¬x#y (Sum.inl x<y)))

  <→≠ : (x y : DedekindReal ℓ) → x < y → ¬ x ≡ y
  <→≠ x y x<y x≡y = <≤-asym x y x<y (≡→≤ (sym x≡y))

  #→≠ : (x y : DedekindReal ℓ) → x # y → ¬ x ≡ y
  #→≠ x y (Sum.inl x<y) x≡y =
    Prop.rec Empty.isProp⊥
      (λ (q , q∈Ux , q∈Ly) →
        disjoint x q
          (subst (λ z → q ∈ lower z) (sym x≡y) q∈Ly)
          q∈Ux)
      x<y
  #→≠ x y (Sum.inr y<x) x≡y =
    Prop.rec Empty.isProp⊥
      (λ (q , q∈Uy , q∈Lx) →
        disjoint x q
          q∈Lx
          (subst (λ z → q ∈ upper z) (sym x≡y) q∈Uy))
      y<x


module Lattice {ℓ : Level} where
  open Order {ℓ}

  infixl 7 _⊓_
  infixl 6 _⊔_

  meetLower : DedekindReal ℓ → DedekindReal ℓ → ℚPred ℓ
  meetLower x y q =
    ((q ∈ lower x) × (q ∈ lower y)) ,
    isProp× (isProp∈ (lower x) q) (isProp∈ (lower y) q)

  meetUpper : DedekindReal ℓ → DedekindReal ℓ → ℚPred ℓ
  meetUpper x y q =
    ∥ (q ∈ upper x) ⊎ (q ∈ upper y) ∥₁ , squash₁

  joinLower : DedekindReal ℓ → DedekindReal ℓ → ℚPred ℓ
  joinLower x y q =
    ∥ (q ∈ lower x) ⊎ (q ∈ lower y) ∥₁ , squash₁

  joinUpper : DedekindReal ℓ → DedekindReal ℓ → ℚPred ℓ
  joinUpper x y q =
    ((q ∈ upper x) × (q ∈ upper y)) ,
    isProp× (isProp∈ (upper x) q) (isProp∈ (upper y) q)

  isDedekindReal⊓ :
    (x y : DedekindReal ℓ) →
    IsDedekindReal (meetLower x y) (meetUpper x y)
  isDedekindReal⊓ x y .IsDedekindReal.lower-inhabited =
    Prop.rec2 squash₁
      (λ (px , px∈Lx) (py , py∈Ly) →
        let
          m = ℚ.min px py
          q = m ℚ.- ℚExtra.1ℚ
          q<m = ℚExtra.q-1<q m
        in
        ∣ q
        , lower-closed x q px
            (ℚOrder.isTrans<≤ q m px q<m (ℚOrder.min≤ px py))
            px∈Lx
        , lower-closed y q py
            (ℚOrder.isTrans<≤ q m py q<m (ℚExtra.min≤r px py))
            py∈Ly
        ∣₁)
      (lower-inhabited x)
      (lower-inhabited y)
  isDedekindReal⊓ x y .IsDedekindReal.upper-inhabited =
    Prop.rec squash₁
      (λ (q , q∈Ux) → ∣ q , ∣ Sum.inl q∈Ux ∣₁ ∣₁)
      (upper-inhabited x)
  isDedekindReal⊓ x y .IsDedekindReal.lower-closed =
    λ p q p<q (q∈Lx , q∈Ly) →
      lower-closed x p q p<q q∈Lx ,
      lower-closed y p q p<q q∈Ly
  isDedekindReal⊓ x y .IsDedekindReal.upper-closed =
    λ p q p<q p∈Uxy →
      Prop.rec squash₁
        (λ where
          (Sum.inl p∈Ux) → ∣ Sum.inl (upper-closed x p q p<q p∈Ux) ∣₁
          (Sum.inr p∈Uy) → ∣ Sum.inr (upper-closed y p q p<q p∈Uy) ∣₁)
        p∈Uxy
  isDedekindReal⊓ x y .IsDedekindReal.lower-rounded =
    λ q (q∈Lx , q∈Ly) →
      Prop.rec2 squash₁
        (λ (rx , q<rx , rx∈Lx) (ry , q<ry , ry∈Ly) →
          let m = ℚ.min rx ry in
          ∣ m
          , ℚExtra.<min {q = q} {r = rx} {s = ry} q<rx q<ry
          , lower-closed-≤ x m rx (ℚOrder.min≤ rx ry) rx∈Lx
          , lower-closed-≤ y m ry (ℚExtra.min≤r rx ry) ry∈Ly
          ∣₁)
        (lower-rounded x q q∈Lx)
        (lower-rounded y q q∈Ly)
  isDedekindReal⊓ x y .IsDedekindReal.upper-rounded =
    λ q q∈Uxy →
      Prop.rec squash₁
        (λ where
          (Sum.inl q∈Ux) →
            Prop.rec squash₁
              (λ (r , r<q , r∈Ux) →
                ∣ r , r<q , ∣ Sum.inl r∈Ux ∣₁ ∣₁)
              (upper-rounded x q q∈Ux)
          (Sum.inr q∈Uy) →
            Prop.rec squash₁
              (λ (r , r<q , r∈Uy) →
                ∣ r , r<q , ∣ Sum.inr r∈Uy ∣₁ ∣₁)
              (upper-rounded y q q∈Uy))
        q∈Uxy
  isDedekindReal⊓ x y .IsDedekindReal.disjoint =
    λ q (q∈Lx , q∈Ly) q∈Uxy →
      Prop.rec Empty.isProp⊥
        (λ where
          (Sum.inl q∈Ux) → disjoint x q q∈Lx q∈Ux
          (Sum.inr q∈Uy) → disjoint y q q∈Ly q∈Uy)
        q∈Uxy
  isDedekindReal⊓ x y .IsDedekindReal.located =
    λ p q p<q →
      Prop.rec2 squash₁
        (λ where
          (Sum.inl p∈Lx) (Sum.inl p∈Ly) →
            ∣ Sum.inl (p∈Lx , p∈Ly) ∣₁
          (Sum.inl p∈Lx) (Sum.inr q∈Uy) →
            ∣ Sum.inr ∣ Sum.inr q∈Uy ∣₁ ∣₁
          (Sum.inr q∈Ux) (Sum.inl p∈Ly) →
            ∣ Sum.inr ∣ Sum.inl q∈Ux ∣₁ ∣₁
          (Sum.inr q∈Ux) (Sum.inr q∈Uy) →
            ∣ Sum.inr ∣ Sum.inl q∈Ux ∣₁ ∣₁)
        (located x p q p<q)
        (located y p q p<q)

  _⊓_ : DedekindReal ℓ → DedekindReal ℓ → DedekindReal ℓ
  x ⊓ y = record
    { lower = meetLower x y
    ; upper = meetUpper x y
    ; isDedekindReal = isDedekindReal⊓ x y
    }

  isDedekindReal⊔ :
    (x y : DedekindReal ℓ) →
    IsDedekindReal (joinLower x y) (joinUpper x y)
  isDedekindReal⊔ x y .IsDedekindReal.lower-inhabited =
    Prop.rec squash₁
      (λ (q , q∈Lx) → ∣ q , ∣ Sum.inl q∈Lx ∣₁ ∣₁)
      (lower-inhabited x)
  isDedekindReal⊔ x y .IsDedekindReal.upper-inhabited =
    Prop.rec2 squash₁
      (λ (ux , ux∈Ux) (uy , uy∈Uy) →
        let
          m = ℚ.max ux uy
          q = m ℚ.+ ℚExtra.1ℚ
          m<q = ℚExtra.q<q+1 m
        in
        ∣ q
        , upper-closed x ux q
            (ℚOrder.isTrans≤< ux m q (ℚOrder.≤max ux uy) m<q)
            ux∈Ux
        , upper-closed y uy q
            (ℚOrder.isTrans≤< uy m q (ℚExtra.≤max-r ux uy) m<q)
            uy∈Uy
        ∣₁)
      (upper-inhabited x)
      (upper-inhabited y)
  isDedekindReal⊔ x y .IsDedekindReal.lower-closed =
    λ p q p<q q∈Lxy →
      Prop.rec squash₁
        (λ where
          (Sum.inl q∈Lx) → ∣ Sum.inl (lower-closed x p q p<q q∈Lx) ∣₁
          (Sum.inr q∈Ly) → ∣ Sum.inr (lower-closed y p q p<q q∈Ly) ∣₁)
        q∈Lxy
  isDedekindReal⊔ x y .IsDedekindReal.upper-closed =
    λ p q p<q (p∈Ux , p∈Uy) →
      upper-closed x p q p<q p∈Ux ,
      upper-closed y p q p<q p∈Uy
  isDedekindReal⊔ x y .IsDedekindReal.lower-rounded =
    λ q q∈Lxy →
      Prop.rec squash₁
        (λ where
          (Sum.inl q∈Lx) →
            Prop.rec squash₁
              (λ (r , q<r , r∈Lx) →
                ∣ r , q<r , ∣ Sum.inl r∈Lx ∣₁ ∣₁)
              (lower-rounded x q q∈Lx)
          (Sum.inr q∈Ly) →
            Prop.rec squash₁
              (λ (r , q<r , r∈Ly) →
                ∣ r , q<r , ∣ Sum.inr r∈Ly ∣₁ ∣₁)
              (lower-rounded y q q∈Ly))
        q∈Lxy
  isDedekindReal⊔ x y .IsDedekindReal.upper-rounded =
    λ q (q∈Ux , q∈Uy) →
      Prop.rec2 squash₁
        (λ (rx , rx<q , rx∈Ux) (ry , ry<q , ry∈Uy) →
          let m = ℚ.max rx ry in
          ∣ m
          , ℚExtra.max< {r = rx} {s = ry} {q = q} rx<q ry<q
          , upper-closed-≤ x rx m (ℚOrder.≤max rx ry) rx∈Ux
          , upper-closed-≤ y ry m (ℚExtra.≤max-r rx ry) ry∈Uy
          ∣₁)
        (upper-rounded x q q∈Ux)
        (upper-rounded y q q∈Uy)
  isDedekindReal⊔ x y .IsDedekindReal.disjoint =
    λ q q∈Lxy (q∈Ux , q∈Uy) →
      Prop.rec Empty.isProp⊥
        (λ where
          (Sum.inl q∈Lx) → disjoint x q q∈Lx q∈Ux
          (Sum.inr q∈Ly) → disjoint y q q∈Ly q∈Uy)
        q∈Lxy
  isDedekindReal⊔ x y .IsDedekindReal.located =
    λ p q p<q →
      Prop.rec2 squash₁
        (λ where
          (Sum.inl p∈Lx) (Sum.inl p∈Ly) →
            ∣ Sum.inl ∣ Sum.inl p∈Lx ∣₁ ∣₁
          (Sum.inl p∈Lx) (Sum.inr q∈Uy) →
            ∣ Sum.inl ∣ Sum.inl p∈Lx ∣₁ ∣₁
          (Sum.inr q∈Ux) (Sum.inl p∈Ly) →
            ∣ Sum.inl ∣ Sum.inr p∈Ly ∣₁ ∣₁
          (Sum.inr q∈Ux) (Sum.inr q∈Uy) →
            ∣ Sum.inr (q∈Ux , q∈Uy) ∣₁)
        (located x p q p<q)
        (located y p q p<q)

  _⊔_ : DedekindReal ℓ → DedekindReal ℓ → DedekindReal ℓ
  x ⊔ y = record
    { lower = joinLower x y
    ; upper = joinUpper x y
    ; isDedekindReal = isDedekindReal⊔ x y
    }

  ⊓≤left : (x y : DedekindReal ℓ) → (x ⊓ y) ≤ x
  ⊓≤left x y q (q∈Lx , _) = q∈Lx

  ⊓≤right : (x y : DedekindReal ℓ) → (x ⊓ y) ≤ y
  ⊓≤right x y q (_ , q∈Ly) = q∈Ly

  ≤⊓ :
    (z x y : DedekindReal ℓ) →
    z ≤ x → z ≤ y → z ≤ (x ⊓ y)
  ≤⊓ z x y z≤x z≤y q q∈Lz = z≤x q q∈Lz , z≤y q q∈Lz

  left≤⊔ : (x y : DedekindReal ℓ) → x ≤ (x ⊔ y)
  left≤⊔ x y q q∈Lx = ∣ Sum.inl q∈Lx ∣₁

  right≤⊔ : (x y : DedekindReal ℓ) → y ≤ (x ⊔ y)
  right≤⊔ x y q q∈Ly = ∣ Sum.inr q∈Ly ∣₁

  ⊔≤ :
    (x y z : DedekindReal ℓ) →
    x ≤ z → y ≤ z → (x ⊔ y) ≤ z
  ⊔≤ x y z x≤z y≤z q q∈Lxy =
    Prop.rec (isProp∈ (lower z) q)
      (λ where
        (Sum.inl q∈Lx) → x≤z q q∈Lx
        (Sum.inr q∈Ly) → y≤z q q∈Ly)
      q∈Lxy

  Dedekind≤Poset : Poset (ℓ-suc ℓ) ℓ
  Dedekind≤Poset =
    poset (DedekindReal ℓ) _≤_
      (isposet isSetDedekindReal isProp≤ ≤-refl ≤-trans ≤-antisym)

  Dedekind≤Pseudolattice : Pseudolattice (ℓ-suc ℓ) ℓ
  Dedekind≤Pseudolattice =
    makePseudolatticeFromPoset Dedekind≤Poset _⊓_ _⊔_
      (λ {a} {b} → ⊓≤left a b)
      (λ {a} {b} → ⊓≤right a b)
      (λ {a} {b} {x} → ≤⊓ x a b)
      (λ {a} {b} → left≤⊔ a b)
      (λ {a} {b} → right≤⊔ a b)
      (λ {a} {b} {x} → ⊔≤ a b x)

  module DedekindPseudolatticeTheory =
    PseudolatticeTheory Dedekind≤Pseudolattice

  ⊓-comm : (x y : DedekindReal ℓ) → x ⊓ y ≡ y ⊓ x
  ⊓-comm x y = DedekindPseudolatticeTheory.∧Comm {a = x} {b = y}

  ⊓-idem : (x : DedekindReal ℓ) → x ⊓ x ≡ x
  ⊓-idem x = DedekindPseudolatticeTheory.∧Idem {a = x}

  ⊓-assoc :
    (x y z : DedekindReal ℓ) →
    x ⊓ (y ⊓ z) ≡ (x ⊓ y) ⊓ z
  ⊓-assoc x y z =
    DedekindPseudolatticeTheory.∧Assoc {a = x} {b = y} {c = z}

  ⊔-comm : (x y : DedekindReal ℓ) → x ⊔ y ≡ y ⊔ x
  ⊔-comm x y = DedekindPseudolatticeTheory.∨Comm {a = x} {b = y}

  ⊔-idem : (x : DedekindReal ℓ) → x ⊔ x ≡ x
  ⊔-idem x = DedekindPseudolatticeTheory.∨Idem {a = x}

  ⊔-assoc :
    (x y z : DedekindReal ℓ) →
    x ⊔ (y ⊔ z) ≡ (x ⊔ y) ⊔ z
  ⊔-assoc x y z =
    DedekindPseudolatticeTheory.∨Assoc {a = x} {b = y} {c = z}

  ⊓-absorb-⊔ : (x y : DedekindReal ℓ) → x ⊓ (x ⊔ y) ≡ x
  ⊓-absorb-⊔ x y =
    DedekindPseudolatticeTheory.≤→∧≡Left
      {a = x} {b = x ⊔ y} (left≤⊔ x y)

  ⊔-absorb-⊓ : (x y : DedekindReal ℓ) → x ⊔ (x ⊓ y) ≡ x
  ⊔-absorb-⊓ x y =
    DedekindPseudolatticeTheory.≥→∨≡Left
      {a = x} {b = x ⊓ y} (⊓≤left x y)

module RationalEmbedding {ℓ : Level} where
  open Order {ℓ}

  ℚ→<-pres :
    (p q : ℚ) → p ℚOrder.< q →
    ℚ→𝔻 ℓ p < ℚ→𝔻 ℓ q
  ℚ→<-pres p q p<q =
    Prop.rec squash₁
      (λ (r , p<r , r<q) → ∣ r , lift p<r , lift r<q ∣₁)
      (ℚExtra.dense {p = p} {q = q} p<q)

  ℚ→<-reflect :
    (p q : ℚ) →
    ℚ→𝔻 ℓ p < ℚ→𝔻 ℓ q →
    p ℚOrder.< q
  ℚ→<-reflect p q =
    Prop.rec (ℚOrder.isProp< p q)
      (λ (r , p<r , r<q) →
        ℚOrder.isTrans< p r q (Lift.lower p<r) (Lift.lower r<q))

  ℚ→<-iff :
    (p q : ℚ) →
    (p ℚOrder.< q → ℚ→𝔻 ℓ p < ℚ→𝔻 ℓ q)
    ×
    (ℚ→𝔻 ℓ p < ℚ→𝔻 ℓ q → p ℚOrder.< q)
  ℚ→<-iff p q = ℚ→<-pres p q , ℚ→<-reflect p q

  ℚ→≤-pres :
    (p q : ℚ) → p ℚOrder.≤ q →
    ℚ→𝔻 ℓ p ≤ ℚ→𝔻 ℓ q
  ℚ→≤-pres p q p≤q r r<p =
    lift (ℚOrder.isTrans<≤ r p q (Lift.lower r<p) p≤q)

  ℚ→≤-reflect :
    (p q : ℚ) →
    ℚ→𝔻 ℓ p ≤ ℚ→𝔻 ℓ q →
    p ℚOrder.≤ q
  ℚ→≤-reflect p q p≤q =
    ℚOrder.≮→≥ q p λ q<p →
      Prop.rec Empty.isProp⊥
        (λ (r , q<r , r<p) →
          ℚOrder.isAsym< q r q<r (Lift.lower (p≤q r (lift r<p))))
        (ℚExtra.dense {p = q} {q = p} q<p)

  ℚ→≤-iff :
    (p q : ℚ) →
    (p ℚOrder.≤ q → ℚ→𝔻 ℓ p ≤ ℚ→𝔻 ℓ q)
    ×
    (ℚ→𝔻 ℓ p ≤ ℚ→𝔻 ℓ q → p ℚOrder.≤ q)
  ℚ→≤-iff p q = ℚ→≤-pres p q , ℚ→≤-reflect p q

  ℚ→-injective :
    (p q : ℚ) →
    ℚ→𝔻 ℓ p ≡ ℚ→𝔻 ℓ q →
    p ≡ q
  ℚ→-injective p q p*≡q* =
    ℚOrder.isAntisym≤ p q
      (ℚ→≤-reflect p q (≡→≤ p*≡q*))
      (ℚ→≤-reflect q p (≡→≤ (sym p*≡q*)))

  0𝔻<1𝔻 : ℚ→𝔻 ℓ ℚExtra.0ℚ < ℚ→𝔻 ℓ ℚExtra.1ℚ
  0𝔻<1𝔻 = ℚ→<-pres ℚExtra.0ℚ ℚExtra.1ℚ ℚExtra.0<1


module Archimedean {ℓ : Level} where
  open Order {ℓ}

  upper-rational-bound :
    (x : DedekindReal ℓ) →
    ∥ Σ[ n ∈ ℕ ] x < ℚ→𝔻 ℓ (ℚExtra.natMul n ℚExtra.1ℚ) ∥₁
  upper-rational-bound x =
    Prop.rec squash₁
      (λ (q , q∈Ux) →
        let (n , q<n) = ℚExtra.archimedes q ℚExtra.1ℚ ℚExtra.0<1 in
        ∣ n , ∣ q , q∈Ux , lift q<n ∣₁ ∣₁)
      (upper-inhabited x)

  lower-rational-bound :
    (x : DedekindReal ℓ) →
    ∥ Σ[ n ∈ ℕ ] ℚ→𝔻 ℓ (ℚ.- ℚExtra.natMul n ℚExtra.1ℚ) < x ∥₁
  lower-rational-bound x =
    Prop.rec squash₁
      (λ (q , q∈Lx) →
        let
          n , -q<n = ℚExtra.archimedes (ℚ.- q) ℚExtra.1ℚ ℚExtra.0<1
          -n<q =
            subst (λ r → (ℚ.- ℚExtra.natMul n ℚExtra.1ℚ) ℚOrder.< r)
              (ℚ.-Invol q)
              (ℚExtra.negReverse<
                {p = ℚ.- q}
                {q = ℚExtra.natMul n ℚExtra.1ℚ}
                -q<n)
        in
        ∣ n , ∣ q , lift -n<q , q∈Lx ∣₁ ∣₁)
      (lower-inhabited x)


module Approximation {ℓ : Level} where
  open Order {ℓ}

  CloseBounds : DedekindReal ℓ → ℚ → Type ℓ
  CloseBounds x ε =
    Σ[ p ∈ ℚ ] Σ[ q ∈ ℚ ]
      (p ∈ lower x) ×
      (q ∈ upper x) ×
      (p ℚOrder.< q) ×
      (q ℚOrder.< p ℚ.+ ε)

  BoundedCloseBounds : DedekindReal ℓ → ℚ → ℚ → Type ℓ
  BoundedCloseBounds x ε u =
    Σ[ p ∈ ℚ ] Σ[ q ∈ ℚ ]
      (p ∈ lower x) ×
      (q ∈ upper x) ×
      (p ℚOrder.< q) ×
      (q ℚOrder.< p ℚ.+ ε) ×
      (q ℚOrder.≤ u)

  private
    bounded→close :
      (x : DedekindReal ℓ) (ε u : ℚ) →
      BoundedCloseBounds x ε u → CloseBounds x ε
    bounded→close x ε u (p , q , p∈Lx , q∈Ux , p<q , q<p+ε , _) =
      p , q , p∈Lx , q∈Ux , p<q , q<p+ε

  bounded-rounded-upper-close :
    (x : DedekindReal ℓ) (ε p q u : ℚ) →
    p ∈ lower x →
    q ∈ upper x →
    q ℚOrder.≤ p ℚ.+ ε →
    q ℚOrder.≤ u →
    ∥ BoundedCloseBounds x ε u ∥₁
  bounded-rounded-upper-close x ε p q u p∈Lx q∈Ux q≤p+ε q≤u =
    Prop.rec squash₁
      (λ (r , r<q , r∈Ux) →
        ∣ p , r
        , p∈Lx
        , r∈Ux
        , lower<upper x p r p∈Lx r∈Ux
        , ℚOrder.isTrans<≤ r q (p ℚ.+ ε) r<q q≤p+ε
        , ℚOrder.<Weaken≤ r u (ℚOrder.isTrans<≤ r q u r<q q≤u)
        ∣₁)
      (upper-rounded x q q∈Ux)

  bounded-close-from-< :
    (x : DedekindReal ℓ) (ε p q u : ℚ) →
    p ∈ lower x →
    q ∈ upper x →
    q ℚOrder.< p ℚ.+ ε →
    q ℚOrder.≤ u →
    ∥ BoundedCloseBounds x ε u ∥₁
  bounded-close-from-< x ε p q u p∈Lx q∈Ux q<p+ε q≤u =
    bounded-rounded-upper-close x ε p q u p∈Lx q∈Ux
      (ℚOrder.<Weaken≤ q (p ℚ.+ ε) q<p+ε)
      q≤u

  bounded-scan-close :
    (x : DedekindReal ℓ) (ε δ : ℚ) →
    ℚExtra.0ℚ ℚOrder.< δ →
    δ ℚ.+ δ ≡ ε →
    (n : ℕ) (p q u : ℚ) →
    p ∈ lower x →
    q ∈ upper x →
    q ℚOrder.≤ p ℚ.+ ℚExtra.natMul (suc n) δ →
    q ℚOrder.≤ u →
    ∥ BoundedCloseBounds x ε u ∥₁
  bounded-scan-close x ε δ 0<δ δ+δ≡ε zero p q u p∈Lx q∈Ux q≤p+δ q≤u =
    bounded-close-from-< x ε p q u p∈Lx q∈Ux q<p+ε q≤u
    where
    q≤p+δ' : q ℚOrder.≤ p ℚ.+ δ
    q≤p+δ' =
      subst (λ r → q ℚOrder.≤ p ℚ.+ r)
        (ℚExtra.natMul-one δ)
        q≤p+δ

    δ<δ+δ : δ ℚOrder.< δ ℚ.+ δ
    δ<δ+δ = ℚExtra.q<q+positive δ δ 0<δ

    δ<ε : δ ℚOrder.< ε
    δ<ε =
      ℚOrder.isTrans<≤ δ (δ ℚ.+ δ) ε
        δ<δ+δ
        (ℚOrder.≡Weaken≤ (δ ℚ.+ δ) ε δ+δ≡ε)

    p+δ<p+ε : p ℚ.+ δ ℚOrder.< p ℚ.+ ε
    p+δ<p+ε = ℚOrder.<-o+ δ ε p δ<ε

    q<p+ε : q ℚOrder.< p ℚ.+ ε
    q<p+ε =
      ℚOrder.isTrans≤< q (p ℚ.+ δ) (p ℚ.+ ε)
        q≤p+δ'
        p+δ<p+ε

  bounded-scan-close x ε δ 0<δ δ+δ≡ε (suc n) p q u p∈Lx q∈Ux q≤bound q≤u =
    Prop.rec squash₁ step
      (located x p₁ p₂ p₁<p₂)
    where
    p₁ : ℚ
    p₁ = p ℚ.+ δ

    p₂ : ℚ
    p₂ = p₁ ℚ.+ δ

    p₁<p₂ : p₁ ℚOrder.< p₂
    p₁<p₂ = ℚExtra.q<q+positive p₁ δ 0<δ

    p₂≡p+ε : p₂ ≡ p ℚ.+ ε
    p₂≡p+ε =
      sym (ℚ.+Assoc p δ δ) ∙
      cong (p ℚ.+_) δ+δ≡ε

    p₂≤p+ε : p₂ ℚOrder.≤ p ℚ.+ ε
    p₂≤p+ε = ℚOrder.≡Weaken≤ p₂ (p ℚ.+ ε) p₂≡p+ε

    q≤shifted : q ℚOrder.≤ p₁ ℚ.+ ℚExtra.natMul (suc n) δ
    q≤shifted =
      subst (λ r → q ℚOrder.≤ r)
        (ℚExtra.shift-bound-suc p δ n)
        q≤bound

    close-with-p₂ :
      p₂ ∈ upper x →
      ∥ BoundedCloseBounds x ε u ∥₁
    close-with-p₂ p₂∈Ux with p₂ ℚOrder.≟ q
    ... | ℚOrder.lt p₂<q =
      bounded-rounded-upper-close x ε p p₂ u p∈Lx p₂∈Ux
        p₂≤p+ε
        (ℚOrder.<Weaken≤ p₂ u
          (ℚOrder.isTrans<≤ p₂ q u p₂<q q≤u))
    ... | ℚOrder.eq p₂≡q =
      bounded-rounded-upper-close x ε p p₂ u p∈Lx p₂∈Ux
        p₂≤p+ε
        (ℚOrder.isTrans≤ p₂ q u
          (ℚOrder.≡Weaken≤ p₂ q p₂≡q)
          q≤u)
    ... | ℚOrder.gt q<p₂ =
      bounded-rounded-upper-close x ε p q u p∈Lx q∈Ux
        (ℚOrder.<Weaken≤ q (p ℚ.+ ε)
          (subst (λ r → q ℚOrder.< r) p₂≡p+ε q<p₂))
        q≤u

    step :
      (p₁ ∈ lower x) ⊎ (p₂ ∈ upper x) →
      ∥ BoundedCloseBounds x ε u ∥₁
    step (Sum.inl p₁∈Lx) =
      bounded-scan-close x ε δ 0<δ δ+δ≡ε n p₁ q u
        p₁∈Lx q∈Ux q≤shifted q≤u
    step (Sum.inr p₂∈Ux) =
      close-with-p₂ p₂∈Ux

  bounded-close-bounds :
    (x : DedekindReal ℓ) (ε u : ℚ) →
    ℚExtra.0ℚ ℚOrder.< ε →
    u ∈ upper x →
    ∥ BoundedCloseBounds x ε u ∥₁
  bounded-close-bounds x ε u 0<ε u∈Ux =
    Prop.rec squash₁ initial
      (lower-inhabited x)
    where
    δ : ℚ
    δ = ε ℚ.· ℚExtra.1/2

    0<δ : ℚExtra.0ℚ ℚOrder.< δ
    0<δ = ℚExtra.positive-half {ε = ε} 0<ε

    δ+δ≡ε : δ ℚ.+ δ ≡ ε
    δ+δ≡ε = ℚExtra.half+half ε

    initial :
      Σ[ p ∈ ℚ ] p ∈ lower x →
      ∥ BoundedCloseBounds x ε u ∥₁
    initial (p , p∈Lx) =
      bounded-scan-close x ε δ 0<δ δ+δ≡ε n p u u
        p∈Lx u∈Ux u≤p+sucnδ (ℚOrder.isRefl≤ u)
      where
      n : ℕ
      n = fst (ℚExtra.archimedes (u ℚ.- p) δ 0<δ)

      u-p<nδ : u ℚ.- p ℚOrder.< ℚExtra.natMul n δ
      u-p<nδ = snd (ℚExtra.archimedes (u ℚ.- p) δ 0<δ)

      u<p+nδ : u ℚOrder.< p ℚ.+ ℚExtra.natMul n δ
      u<p+nδ =
        ℚExtra.diff<→shift< p u (ℚExtra.natMul n δ) u-p<nδ

      p+nδ<p+sucnδ :
        p ℚ.+ ℚExtra.natMul n δ
        ℚOrder.<
        p ℚ.+ ℚExtra.natMul (suc n) δ
      p+nδ<p+sucnδ =
        ℚOrder.<-o+
          (ℚExtra.natMul n δ)
          (ℚExtra.natMul (suc n) δ)
          p
          (ℚExtra.natMul-step< n {ε = δ} 0<δ)

      u<p+sucnδ : u ℚOrder.< p ℚ.+ ℚExtra.natMul (suc n) δ
      u<p+sucnδ =
        ℚOrder.isTrans< u
          (p ℚ.+ ℚExtra.natMul n δ)
          (p ℚ.+ ℚExtra.natMul (suc n) δ)
          u<p+nδ
          p+nδ<p+sucnδ

      u≤p+sucnδ : u ℚOrder.≤ p ℚ.+ ℚExtra.natMul (suc n) δ
      u≤p+sucnδ =
        ℚOrder.<Weaken≤ u
          (p ℚ.+ ℚExtra.natMul (suc n) δ)
          u<p+sucnδ

  close-bounds :
    (x : DedekindReal ℓ) (ε : ℚ) →
    ℚExtra.0ℚ ℚOrder.< ε →
    ∥ CloseBounds x ε ∥₁
  close-bounds x ε 0<ε =
    Prop.rec squash₁
      (λ (u , u∈Ux) →
        Prop.rec squash₁
          (λ close → ∣ bounded→close x ε u close ∣₁)
          (bounded-close-bounds x ε u 0<ε u∈Ux))
      (upper-inhabited x)


module Algebra {ℓ : Level} where
  -_ : DedekindReal ℓ → DedekindReal ℓ
  (- x) .lower q = (ℚ.- q ∈ upper x) , isProp∈ (upper x) (ℚ.- q)
  (- x) .upper q = (ℚ.- q ∈ lower x) , isProp∈ (lower x) (ℚ.- q)
  (- x) .isDedekindReal .IsDedekindReal.lower-inhabited =
    Prop.rec squash₁
      (λ (q , q∈Ux) →
        ∣ ℚ.- q
        , subst (λ r → r ∈ upper x) (sym (ℚ.-Invol q)) q∈Ux
        ∣₁)
      (upper-inhabited x)
  (- x) .isDedekindReal .IsDedekindReal.upper-inhabited =
    Prop.rec squash₁
      (λ (q , q∈Lx) →
        ∣ ℚ.- q
        , subst (λ r → r ∈ lower x) (sym (ℚ.-Invol q)) q∈Lx
        ∣₁)
      (lower-inhabited x)
  (- x) .isDedekindReal .IsDedekindReal.lower-closed =
    λ p q p<q -q∈Ux →
      upper-closed x (ℚ.- q) (ℚ.- p)
        (ℚExtra.negReverse< {p = p} {q = q} p<q)
        -q∈Ux
  (- x) .isDedekindReal .IsDedekindReal.upper-closed =
    λ p q p<q -p∈Lx →
      lower-closed x (ℚ.- q) (ℚ.- p)
        (ℚExtra.negReverse< {p = p} {q = q} p<q)
        -p∈Lx
  (- x) .isDedekindReal .IsDedekindReal.lower-rounded =
    λ q -q∈Ux →
      Prop.rec squash₁
        (λ (r , r<-q , r∈Ux) →
          ∣ ℚ.- r
          , subst (λ s → s ℚOrder.< ℚ.- r)
              (ℚ.-Invol q)
              (ℚExtra.negReverse< {p = r} {q = ℚ.- q} r<-q)
          , subst (λ s → s ∈ upper x) (sym (ℚ.-Invol r)) r∈Ux
          ∣₁)
        (upper-rounded x (ℚ.- q) -q∈Ux)
  (- x) .isDedekindReal .IsDedekindReal.upper-rounded =
    λ q -q∈Lx →
      Prop.rec squash₁
        (λ (r , -q<r , r∈Lx) →
          ∣ ℚ.- r
          , subst (λ s → ℚ.- r ℚOrder.< s)
              (ℚ.-Invol q)
              (ℚExtra.negReverse< {p = ℚ.- q} {q = r} -q<r)
          , subst (λ s → s ∈ lower x) (sym (ℚ.-Invol r)) r∈Lx
          ∣₁)
        (lower-rounded x (ℚ.- q) -q∈Lx)
  (- x) .isDedekindReal .IsDedekindReal.disjoint =
    λ q -q∈Ux -q∈Lx → disjoint x (ℚ.- q) -q∈Lx -q∈Ux
  (- x) .isDedekindReal .IsDedekindReal.located =
    λ p q p<q →
      Prop.rec squash₁
        (λ where
          (Sum.inl -q∈Lx) → ∣ Sum.inr -q∈Lx ∣₁
          (Sum.inr -p∈Ux) → ∣ Sum.inl -p∈Ux ∣₁)
        (located x (ℚ.- q) (ℚ.- p)
          (ℚExtra.negReverse< {p = p} {q = q} p<q))

  infix 8 -_

  neg-involutive : (x : DedekindReal ℓ) → - (- x) ≡ x
  neg-involutive x =
    realExt (- (- x)) x
      (λ q -- -(-q) is in the lower cut of x.
        → subst (λ r → r ∈ lower x) (ℚ.-Invol q))
      (λ q → subst (λ r → r ∈ lower x) (sym (ℚ.-Invol q)))
      (λ q → subst (λ r → r ∈ upper x) (ℚ.-Invol q))
      (λ q → subst (λ r → r ∈ upper x) (sym (ℚ.-Invol q)))

  neg-≤-reverse :
    (x y : DedekindReal ℓ) →
    Order._≤_ {ℓ = ℓ} x y →
    Order._≤_ {ℓ = ℓ} (- y) (- x)
  neg-≤-reverse x y x≤y q -q∈Uy =
    Order.upper-inclusion-from-lower y x x≤y (ℚ.- q) -q∈Uy

  neg-≤-reflect :
    (x y : DedekindReal ℓ) →
    Order._≤_ {ℓ = ℓ} (- y) (- x) →
    Order._≤_ {ℓ = ℓ} x y
  neg-≤-reflect x y -y≤-x q q∈Lx =
    subst (λ r → r ∈ lower y) (ℚ.-Invol q)
      (Order.upper-inclusion-from-lower (- x) (- y) -y≤-x
        (ℚ.- q)
        (subst (λ r → r ∈ lower x) (sym (ℚ.-Invol q)) q∈Lx))

  neg-≤-iff :
    (x y : DedekindReal ℓ) →
    (Order._≤_ {ℓ = ℓ} x y → Order._≤_ {ℓ = ℓ} (- y) (- x))
    ×
    (Order._≤_ {ℓ = ℓ} (- y) (- x) → Order._≤_ {ℓ = ℓ} x y)
  neg-≤-iff x y = neg-≤-reverse x y , neg-≤-reflect x y

  neg-<-reverse :
    (x y : DedekindReal ℓ) →
    Order._<_ {ℓ = ℓ} x y →
    Order._<_ {ℓ = ℓ} (- y) (- x)
  neg-<-reverse x y x<y =
    Prop.rec squash₁
      (λ (q , q∈Ux , q∈Ly) →
        ∣ ℚ.- q
        , subst (λ r → r ∈ lower y) (sym (ℚ.-Invol q)) q∈Ly
        , subst (λ r → r ∈ upper x) (sym (ℚ.-Invol q)) q∈Ux
        ∣₁)
      x<y

  neg-<-reflect :
    (x y : DedekindReal ℓ) →
    Order._<_ {ℓ = ℓ} (- y) (- x) →
    Order._<_ {ℓ = ℓ} x y
  neg-<-reflect x y -y<-x =
    subst2 (Order._<_ {ℓ = ℓ})
      (neg-involutive x)
      (neg-involutive y)
      (neg-<-reverse (- y) (- x) -y<-x)

  neg-<-iff :
    (x y : DedekindReal ℓ) →
    (Order._<_ {ℓ = ℓ} x y → Order._<_ {ℓ = ℓ} (- y) (- x))
    ×
    (Order._<_ {ℓ = ℓ} (- y) (- x) → Order._<_ {ℓ = ℓ} x y)
  neg-<-iff x y = neg-<-reverse x y , neg-<-reflect x y

  neg-rational :
    (q : ℚ) →
    - ℚ→𝔻 ℓ q ≡ ℚ→𝔻 ℓ (ℚ.- q)
  neg-rational q =
    realExt (- ℚ→𝔻 ℓ q) (ℚ→𝔻 ℓ (ℚ.- q))
      (λ p q<-p →
        lift
          (subst (λ r → r ℚOrder.< ℚ.- q)
            (ℚ.-Invol p)
            (ℚExtra.negReverse<
              {p = q}
              {q = ℚ.- p}
              (Lift.lower q<-p))))
      (λ p p<-q →
        lift
          (subst (λ r → r ℚOrder.< ℚ.- p)
            (ℚ.-Invol q)
            (ℚExtra.negReverse<
              {p = p}
              {q = ℚ.- q}
              (Lift.lower p<-q))))
      (λ p -p<q →
        lift
          (subst (λ r → ℚ.- q ℚOrder.< r)
            (ℚ.-Invol p)
            (ℚExtra.negReverse<
              {p = ℚ.- p}
              {q = q}
              (Lift.lower -p<q))))
      (λ p -q<p →
        lift
          (subst (λ r → ℚ.- p ℚOrder.< r)
            (ℚ.-Invol q)
            (ℚExtra.negReverse<
              {p = ℚ.- q}
              {q = p}
              (Lift.lower -q<p))))
