{-

Order on Dedekind completions over linearly ordered fields

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.DedekindCompletion.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Nullary using (¬_)
import Cubical.Relation.Binary.Order.StrictOrder as StrictOrder

import Constructive.Algebra.LinearlyOrderedCommRing.Base as LinearBase
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.DedekindCompletion.Base
open import Constructive.Foundations.Powerset hiding (Pred)

private
  variable
    ℓ ℓ' ℓᴾ : Level


module CompletionOrder (𝒦 : LinearlyOrderedField ℓ ℓ') where

  open CompletionBase 𝒦
  open LinearlyOrderedFieldStr 𝒦
    using
      ( middle ; middle>l ; middle<r
      ; trichotomy ; ≤-total
      ; min ; max ; min≤left ; min≤right ; max≥left ; max≥right
      ; 1r ; _+_ ; _-_
      ; q-1<q ; q+1>q
      )
    renaming
      ( _<_ to _<K_
      ; _≤_ to _≤K_
      ; isProp< to isProp<K
      ; <-trans to <K-trans
      ; <-asym to <K-asym
      ; <-arefl to <K-arefl
      ; <≤-asym to <K≤K-asym
      ; <≤-trans to <K≤K-trans
      ; ≤<-trans to ≤K<K-trans
      )

  private
    K : Type ℓ
    K = 𝒦 .fst .fst .fst


  _≤_ : DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
  x ≤ y = (q : K) → q ∈ lower x → q ∈ lower y

  _<_ : DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
  x < y = ∥ Σ[ q ∈ K ] (q ∈ upper x) × (q ∈ lower y) ∥₁

  _#_ : DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
  x # y = (x < y) ⊎ (y < x)

  infix 4 _≤_ _<_ _#_

  isProp≤ : (x y : DedekindCompletion ℓᴾ) → isProp (x ≤ y)
  isProp≤ x y = isPropΠ2 λ q _ → isProp∈ (lower y) q

  isProp< : (x y : DedekindCompletion ℓᴾ) → isProp (x < y)
  isProp< x y = squash₁

  ≡→≤ : {x y : DedekindCompletion ℓᴾ} → x ≡ y → x ≤ y
  ≡→≤ x≡y q q∈Lx = subst (λ z → q ∈ lower z) x≡y q∈Lx

  ≤-refl : (x : DedekindCompletion ℓᴾ) → x ≤ x
  ≤-refl x q q∈Lx = q∈Lx

  ≤-trans :
    (x y z : DedekindCompletion ℓᴾ) →
    x ≤ y → y ≤ z → x ≤ z
  ≤-trans x y z x≤y y≤z q q∈Lx = y≤z q (x≤y q q∈Lx)

  lower<upper :
    (x : DedekindCompletion ℓᴾ) (p q : K) →
    p ∈ lower x →
    q ∈ upper x →
    p <K q
  lower<upper x p q p∈L q∈U with trichotomy p q
  ... | LinearBase.lt p<q = p<q
  ... | LinearBase.eq p≡q =
    Empty.rec (disjoint x q (subst (λ r → r ∈ lower x) p≡q p∈L) q∈U)
  ... | LinearBase.gt q<p =
    Empty.rec (disjoint x p p∈L (upper-closed x q p q<p q∈U))

  lower-closed-≤ :
    (x : DedekindCompletion ℓᴾ) (p q : K) →
    p ≤K q →
    q ∈ lower x →
    p ∈ lower x
  lower-closed-≤ x p q p≤q q∈L with trichotomy p q
  ... | LinearBase.lt p<q = lower-closed x p q p<q q∈L
  ... | LinearBase.eq p≡q = subst (λ r → r ∈ lower x) (sym p≡q) q∈L
  ... | LinearBase.gt q<p = Empty.rec (<K≤K-asym q<p p≤q)

  upper-closed-≤ :
    (x : DedekindCompletion ℓᴾ) (p q : K) →
    p ≤K q →
    p ∈ upper x →
    q ∈ upper x
  upper-closed-≤ x p q p≤q p∈U with trichotomy p q
  ... | LinearBase.lt p<q = upper-closed x p q p<q p∈U
  ... | LinearBase.eq p≡q = subst (λ r → r ∈ upper x) p≡q p∈U
  ... | LinearBase.gt q<p = Empty.rec (<K≤K-asym q<p p≤q)

  K<→principalLower :
    (p q : K) →
    p <K q →
    p ∈ lower (K→𝔻 ℓᴾ q)
  K<→principalLower p q p<q = lift p<q

  principalLower→K< :
    (p q : K) →
    p ∈ lower (K→𝔻 ℓᴾ q) →
    p <K q
  principalLower→K< p q p∈L = Lift.lower p∈L

  K<→principalUpper :
    (p q : K) →
    q <K p →
    p ∈ upper (K→𝔻 ℓᴾ q)
  K<→principalUpper p q q<p = lift q<p

  principalUpper→K< :
    (p q : K) →
    p ∈ upper (K→𝔻 ℓᴾ q) →
    q <K p
  principalUpper→K< p q p∈U = Lift.lower p∈U

  K→<-pres :
    (p q : K) →
    p <K q →
    K→𝔻 ℓᴾ p < K→𝔻 ℓᴾ q
  K→<-pres p q p<q =
    ∣ middle p q
    , lift (middle>l p<q)
    , lift (middle<r p<q)
    ∣₁

  K→<-reflect :
    (p q : K) →
    K→𝔻 ℓᴾ p < K→𝔻 ℓᴾ q →
    p <K q
  K→<-reflect p q =
    Prop.rec isProp<K
      (λ (r , p<r , r<q) →
        <K-trans (Lift.lower p<r) (Lift.lower r<q))

  lower→K< :
    (x : DedekindCompletion ℓᴾ) (q : K) →
    q ∈ lower x →
    K→𝔻 ℓᴾ q < x
  lower→K< x q q∈Lx =
    Prop.rec squash₁
      (λ (r , q<r , r∈Lx) → ∣ r , lift q<r , r∈Lx ∣₁)
      (lower-rounded x q q∈Lx)

  K<→lower :
    (x : DedekindCompletion ℓᴾ) (q : K) →
    K→𝔻 ℓᴾ q < x →
    q ∈ lower x
  K<→lower x q =
    Prop.rec (isProp∈ (lower x) q)
      (λ (r , q<r , r∈Lx) →
        lower-closed x q r (Lift.lower q<r) r∈Lx)

  upper→<K :
    (x : DedekindCompletion ℓᴾ) (q : K) →
    q ∈ upper x →
    x < K→𝔻 ℓᴾ q
  upper→<K x q q∈Ux =
    Prop.rec squash₁
      (λ (r , r<q , r∈Ux) → ∣ r , r∈Ux , lift r<q ∣₁)
      (upper-rounded x q q∈Ux)

  <K→upper :
    (x : DedekindCompletion ℓᴾ) (q : K) →
    x < K→𝔻 ℓᴾ q →
    q ∈ upper x
  <K→upper x q =
    Prop.rec (isProp∈ (upper x) q)
      (λ (r , r∈Ux , r<q) →
        upper-closed x r q (Lift.lower r<q) r∈Ux)

  lower⇔K< :
    (x : DedekindCompletion ℓᴾ) (q : K) →
    (q ∈ lower x → K→𝔻 ℓᴾ q < x)
    ×
    (K→𝔻 ℓᴾ q < x → q ∈ lower x)
  lower⇔K< x q = lower→K< x q , K<→lower x q

  upper⇔<K :
    (x : DedekindCompletion ℓᴾ) (q : K) →
    (q ∈ upper x → x < K→𝔻 ℓᴾ q)
    ×
    (x < K→𝔻 ℓᴾ q → q ∈ upper x)
  upper⇔<K x q = upper→<K x q , <K→upper x q

  basis-between :
    (x y : DedekindCompletion ℓᴾ) →
    x < y →
    ∥ Σ[ q ∈ K ] (x < K→𝔻 ℓᴾ q) × (K→𝔻 ℓᴾ q < y) ∥₁
  basis-between x y =
    Prop.rec squash₁
      (λ (q , q∈Ux , q∈Ly) →
        ∣ q , upper→<K x q q∈Ux , lower→K< y q q∈Ly ∣₁)

  basis-located :
    (x : DedekindCompletion ℓᴾ) (p q : K) →
    p <K q →
    ∥ (K→𝔻 ℓᴾ p < x) ⊎ (x < K→𝔻 ℓᴾ q) ∥₁
  basis-located x p q p<q =
    Prop.rec squash₁
      (λ where
        (Sum.inl p∈Lx) → ∣ Sum.inl (lower→K< x p p∈Lx) ∣₁
        (Sum.inr q∈Ux) → ∣ Sum.inr (upper→<K x q q∈Ux) ∣₁)
      (located x p q p<q)

  upper-inclusion-from-lower :
    (x y : DedekindCompletion ℓᴾ) →
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

  ≤-antisym :
    (x y : DedekindCompletion ℓᴾ) →
    x ≤ y → y ≤ x → x ≡ y
  ≤-antisym x y x≤y y≤x =
    completionExt x y x≤y y≤x
      (upper-inclusion-from-lower x y y≤x)
      (upper-inclusion-from-lower y x x≤y)

  <→≤ : (x y : DedekindCompletion ℓᴾ) → x < y → x ≤ y
  <→≤ x y x<y q q∈Lx =
    Prop.rec (isProp∈ (lower y) q)
      (λ (r , r∈Ux , r∈Ly) →
        lower-closed y q r (lower<upper x q r q∈Lx r∈Ux) r∈Ly)
      x<y

  <-trans :
    (x y z : DedekindCompletion ℓᴾ) →
    x < y → y < z → x < z
  <-trans x y z x<y y<z =
    Prop.rec squash₁
      (λ (q , q∈Ux , q∈Ly) →
        Prop.rec squash₁
          (λ (r , r∈Uy , r∈Lz) →
            let
              q<r : q <K r
              q<r = lower<upper y q r q∈Ly r∈Uy

              s : K
              s = middle q r
            in
            ∣ s
            , upper-closed x q s (middle>l q<r) q∈Ux
            , lower-closed z s r (middle<r q<r) r∈Lz
            ∣₁)
          y<z)
      x<y

  ≤-<-trans :
    (x y z : DedekindCompletion ℓᴾ) →
    x ≤ y → y < z → x < z
  ≤-<-trans x y z x≤y y<z =
    Prop.rec squash₁
      (λ (q , q∈Uy , q∈Lz) →
        ∣ q , upper-inclusion-from-lower y x x≤y q q∈Uy , q∈Lz ∣₁)
      y<z

  <-≤-trans :
    (x y z : DedekindCompletion ℓᴾ) →
    x < y → y ≤ z → x < z
  <-≤-trans x y z x<y y≤z =
    Prop.rec squash₁
      (λ (q , q∈Ux , q∈Ly) → ∣ q , q∈Ux , y≤z q q∈Ly ∣₁)
      x<y

  <≤-asym :
    (x y : DedekindCompletion ℓᴾ) →
    x < y → y ≤ x → ⊥
  <≤-asym x y x<y y≤x =
    Prop.rec Empty.isProp⊥
      (λ (q , q∈Ux , q∈Ly) → disjoint x q (y≤x q q∈Ly) q∈Ux)
      x<y

  <-irrefl : (x : DedekindCompletion ℓᴾ) → ¬ x < x
  <-irrefl x x<x = <≤-asym x x x<x (≤-refl x)

  <-asym :
    (x y : DedekindCompletion ℓᴾ) →
    x < y → ¬ y < x
  <-asym x y x<y y<x = <≤-asym x y x<y (<→≤ y x y<x)

  isWeaklyLinear< :
    (x y z : DedekindCompletion ℓᴾ) →
    x < y → ∥ (x < z) ⊎ (z < y) ∥₁
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

  ≤→¬> : (x y : DedekindCompletion ℓᴾ) → x ≤ y → ¬ y < x
  ≤→¬> x y x≤y y<x = <≤-asym y x y<x x≤y

  ¬>→≤ : (x y : DedekindCompletion ℓᴾ) → ¬ y < x → x ≤ y
  ¬>→≤ x y ¬y<x q q∈Lx =
    Prop.rec (isProp∈ (lower y) q)
      (λ (r , q<r , r∈Lx) →
        Prop.rec (isProp∈ (lower y) q)
          (λ where
            (Sum.inl q∈Ly) → q∈Ly
            (Sum.inr r∈Uy) → Empty.rec (¬y<x ∣ r , r∈Uy , r∈Lx ∣₁))
          (located y q r q<r))
      (lower-rounded x q q∈Lx)

  ≤⇔¬> :
    (x y : DedekindCompletion ℓᴾ) →
    (x ≤ y → ¬ y < x) × (¬ y < x → x ≤ y)
  ≤⇔¬> x y = ≤→¬> x y , ¬>→≤ x y

  isStrictOrder< :
    StrictOrder.IsStrictOrder
      {A = DedekindCompletion ℓᴾ}
      (λ x y → x < y)
  isStrictOrder< =
    StrictOrder.isstrictorder
      isSetDedekindCompletion
      isProp<
      <-irrefl
      <-trans
      <-asym
      isWeaklyLinear<

  isProp# : (x y : DedekindCompletion ℓᴾ) → isProp (x # y)
  isProp# x y = Sum.isProp⊎ (isProp< x y) (isProp< y x) (<-asym x y)

  #-irrefl : (x : DedekindCompletion ℓᴾ) → ¬ x # x
  #-irrefl x (Sum.inl x<x) = <-irrefl x x<x
  #-irrefl x (Sum.inr x<x) = <-irrefl x x<x

  #-sym : (x y : DedekindCompletion ℓᴾ) → x # y → y # x
  #-sym x y (Sum.inl x<y) = Sum.inr x<y
  #-sym x y (Sum.inr y<x) = Sum.inl y<x

  #-cotrans :
    (x y z : DedekindCompletion ℓᴾ) →
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

  #-tight : (x y : DedekindCompletion ℓᴾ) → ¬ x # y → x ≡ y
  #-tight x y ¬x#y =
    ≤-antisym x y
      (¬>→≤ x y (λ y<x → ¬x#y (Sum.inr y<x)))
      (¬>→≤ y x (λ x<y → ¬x#y (Sum.inl x<y)))

  <→≠ :
    (x y : DedekindCompletion ℓᴾ) →
    x < y → ¬ x ≡ y
  <→≠ x y x<y x≡y = <≤-asym x y x<y (≡→≤ (sym x≡y))

  #→≠ :
    (x y : DedekindCompletion ℓᴾ) →
    x # y → ¬ x ≡ y
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


  infixl 7 _⊓_
  infixl 6 _⊔_

  private
    <min :
      {q x y : K} →
      q <K x →
      q <K y →
      q <K min x y
    <min {x = x} {y = y} q<x q<y with ≤-total x y
    ... | Sum.inl _ = q<x
    ... | Sum.inr _ = q<y

    max< :
      {x y q : K} →
      x <K q →
      y <K q →
      max x y <K q
    max< {x = x} {y = y} x<q y<q with ≤-total x y
    ... | Sum.inl _ = y<q
    ... | Sum.inr _ = x<q

  meetLower :
    DedekindCompletion ℓᴾ →
    DedekindCompletion ℓᴾ →
    Pred ℓᴾ
  meetLower x y q =
    ((q ∈ lower x) × (q ∈ lower y)) ,
    isProp× (isProp∈ (lower x) q) (isProp∈ (lower y) q)

  meetUpper :
    DedekindCompletion ℓᴾ →
    DedekindCompletion ℓᴾ →
    Pred ℓᴾ
  meetUpper x y q =
    ∥ (q ∈ upper x) ⊎ (q ∈ upper y) ∥₁ , squash₁

  joinLower :
    DedekindCompletion ℓᴾ →
    DedekindCompletion ℓᴾ →
    Pred ℓᴾ
  joinLower x y q =
    ∥ (q ∈ lower x) ⊎ (q ∈ lower y) ∥₁ , squash₁

  joinUpper :
    DedekindCompletion ℓᴾ →
    DedekindCompletion ℓᴾ →
    Pred ℓᴾ
  joinUpper x y q =
    ((q ∈ upper x) × (q ∈ upper y)) ,
    isProp× (isProp∈ (upper x) q) (isProp∈ (upper y) q)

  isDedekindCut⊓ :
    (x y : DedekindCompletion ℓᴾ) →
    IsDedekindCut (meetLower x y) (meetUpper x y)
  isDedekindCut⊓ x y .IsDedekindCut.lower-inhabited =
    Prop.rec2 squash₁
      (λ (px , px∈Lx) (py , py∈Ly) →
        let
          m = min px py
          q = m - 1r
          q<m = q-1<q {q = m}
        in
        ∣ q
        , lower-closed x q px
            (<K≤K-trans q<m min≤left)
            px∈Lx
        , lower-closed y q py
            (<K≤K-trans q<m min≤right)
            py∈Ly
        ∣₁)
      (lower-inhabited x)
      (lower-inhabited y)
  isDedekindCut⊓ x y .IsDedekindCut.upper-inhabited =
    Prop.rec squash₁
      (λ (q , q∈Ux) → ∣ q , ∣ Sum.inl q∈Ux ∣₁ ∣₁)
      (upper-inhabited x)
  isDedekindCut⊓ x y .IsDedekindCut.lower-closed =
    λ p q p<q (q∈Lx , q∈Ly) →
      lower-closed x p q p<q q∈Lx ,
      lower-closed y p q p<q q∈Ly
  isDedekindCut⊓ x y .IsDedekindCut.upper-closed =
    λ p q p<q p∈Uxy →
      Prop.rec squash₁
        (λ where
          (Sum.inl p∈Ux) → ∣ Sum.inl (upper-closed x p q p<q p∈Ux) ∣₁
          (Sum.inr p∈Uy) → ∣ Sum.inr (upper-closed y p q p<q p∈Uy) ∣₁)
        p∈Uxy
  isDedekindCut⊓ x y .IsDedekindCut.lower-rounded =
    λ q (q∈Lx , q∈Ly) →
      Prop.rec2 squash₁
        (λ (rx , q<rx , rx∈Lx) (ry , q<ry , ry∈Ly) →
          let m = min rx ry in
          ∣ m
          , <min q<rx q<ry
          , lower-closed-≤ x m rx min≤left rx∈Lx
          , lower-closed-≤ y m ry min≤right ry∈Ly
          ∣₁)
        (lower-rounded x q q∈Lx)
        (lower-rounded y q q∈Ly)
  isDedekindCut⊓ x y .IsDedekindCut.upper-rounded =
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
  isDedekindCut⊓ x y .IsDedekindCut.disjoint =
    λ q (q∈Lx , q∈Ly) q∈Uxy →
      Prop.rec Empty.isProp⊥
        (λ where
          (Sum.inl q∈Ux) → disjoint x q q∈Lx q∈Ux
          (Sum.inr q∈Uy) → disjoint y q q∈Ly q∈Uy)
        q∈Uxy
  isDedekindCut⊓ x y .IsDedekindCut.located =
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

  _⊓_ :
    DedekindCompletion ℓᴾ →
    DedekindCompletion ℓᴾ →
    DedekindCompletion ℓᴾ
  x ⊓ y = record
    { lower = meetLower x y
    ; upper = meetUpper x y
    ; isDedekindCut = isDedekindCut⊓ x y
    }

  isDedekindCut⊔ :
    (x y : DedekindCompletion ℓᴾ) →
    IsDedekindCut (joinLower x y) (joinUpper x y)
  isDedekindCut⊔ x y .IsDedekindCut.lower-inhabited =
    Prop.rec squash₁
      (λ (q , q∈Lx) → ∣ q , ∣ Sum.inl q∈Lx ∣₁ ∣₁)
      (lower-inhabited x)
  isDedekindCut⊔ x y .IsDedekindCut.upper-inhabited =
    Prop.rec2 squash₁
      (λ (ux , ux∈Ux) (uy , uy∈Uy) →
        let
          m = max ux uy
          q = m + 1r
          m<q = q+1>q {q = m}
        in
        ∣ q
        , upper-closed x ux q
            (≤K<K-trans max≥left m<q)
            ux∈Ux
        , upper-closed y uy q
            (≤K<K-trans max≥right m<q)
            uy∈Uy
        ∣₁)
      (upper-inhabited x)
      (upper-inhabited y)
  isDedekindCut⊔ x y .IsDedekindCut.lower-closed =
    λ p q p<q q∈Lxy →
      Prop.rec squash₁
        (λ where
          (Sum.inl q∈Lx) → ∣ Sum.inl (lower-closed x p q p<q q∈Lx) ∣₁
          (Sum.inr q∈Ly) → ∣ Sum.inr (lower-closed y p q p<q q∈Ly) ∣₁)
        q∈Lxy
  isDedekindCut⊔ x y .IsDedekindCut.upper-closed =
    λ p q p<q (p∈Ux , p∈Uy) →
      upper-closed x p q p<q p∈Ux ,
      upper-closed y p q p<q p∈Uy
  isDedekindCut⊔ x y .IsDedekindCut.lower-rounded =
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
  isDedekindCut⊔ x y .IsDedekindCut.upper-rounded =
    λ q (q∈Ux , q∈Uy) →
      Prop.rec2 squash₁
        (λ (rx , rx<q , rx∈Ux) (ry , ry<q , ry∈Uy) →
          let m = max rx ry in
          ∣ m
          , max< rx<q ry<q
          , upper-closed-≤ x rx m max≥left rx∈Ux
          , upper-closed-≤ y ry m max≥right ry∈Uy
          ∣₁)
        (upper-rounded x q q∈Ux)
        (upper-rounded y q q∈Uy)
  isDedekindCut⊔ x y .IsDedekindCut.disjoint =
    λ q q∈Lxy (q∈Ux , q∈Uy) →
      Prop.rec Empty.isProp⊥
        (λ where
          (Sum.inl q∈Lx) → disjoint x q q∈Lx q∈Ux
          (Sum.inr q∈Ly) → disjoint y q q∈Ly q∈Uy)
        q∈Lxy
  isDedekindCut⊔ x y .IsDedekindCut.located =
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

  _⊔_ :
    DedekindCompletion ℓᴾ →
    DedekindCompletion ℓᴾ →
    DedekindCompletion ℓᴾ
  x ⊔ y = record
    { lower = joinLower x y
    ; upper = joinUpper x y
    ; isDedekindCut = isDedekindCut⊔ x y
    }

  ⊓≤left :
    (x y : DedekindCompletion ℓᴾ) →
    (x ⊓ y) ≤ x
  ⊓≤left x y q (q∈Lx , _) = q∈Lx

  ⊓≤right :
    (x y : DedekindCompletion ℓᴾ) →
    (x ⊓ y) ≤ y
  ⊓≤right x y q (_ , q∈Ly) = q∈Ly

  ≤⊓ :
    (z x y : DedekindCompletion ℓᴾ) →
    z ≤ x →
    z ≤ y →
    z ≤ (x ⊓ y)
  ≤⊓ z x y z≤x z≤y q q∈Lz =
    z≤x q q∈Lz , z≤y q q∈Lz

  left≤⊔ :
    (x y : DedekindCompletion ℓᴾ) →
    x ≤ (x ⊔ y)
  left≤⊔ x y q q∈Lx = ∣ Sum.inl q∈Lx ∣₁

  right≤⊔ :
    (x y : DedekindCompletion ℓᴾ) →
    y ≤ (x ⊔ y)
  right≤⊔ x y q q∈Ly = ∣ Sum.inr q∈Ly ∣₁

  ⊔≤ :
    (x y z : DedekindCompletion ℓᴾ) →
    x ≤ z →
    y ≤ z →
    (x ⊔ y) ≤ z
  ⊔≤ x y z x≤z y≤z q q∈Lxy =
    Prop.rec (isProp∈ (lower z) q)
      (λ where
        (Sum.inl q∈Lx) → x≤z q q∈Lx
        (Sum.inr q∈Ly) → y≤z q q∈Ly)
      q∈Lxy

  DedekindCompletion≤Poset :
    {ℓᴾ : Level} →
    Poset (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))) (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
  DedekindCompletion≤Poset {ℓᴾ = ℓᴾ} =
    poset (DedekindCompletion ℓᴾ) _≤_
      (isposet isSetDedekindCompletion isProp≤ ≤-refl ≤-trans ≤-antisym)

  DedekindCompletion≤Pseudolattice :
    {ℓᴾ : Level} →
    Pseudolattice
      (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ)))
      (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
  DedekindCompletion≤Pseudolattice {ℓᴾ = ℓᴾ} =
    makePseudolatticeFromPoset (DedekindCompletion≤Poset {ℓᴾ = ℓᴾ}) _⊓_ _⊔_
      (λ {a} {b} → ⊓≤left a b)
      (λ {a} {b} → ⊓≤right a b)
      (λ {a} {b} {x} → ≤⊓ x a b)
      (λ {a} {b} → left≤⊔ a b)
      (λ {a} {b} → right≤⊔ a b)
      (λ {a} {b} {x} → ⊔≤ a b x)

  module DedekindCompletionPseudolatticeTheory {ℓᴾ : Level} =
    PseudolatticeTheory (DedekindCompletion≤Pseudolattice {ℓᴾ = ℓᴾ})

  ⊓-comm :
    (x y : DedekindCompletion ℓᴾ) →
    x ⊓ y ≡ y ⊓ x
  ⊓-comm x y =
    DedekindCompletionPseudolatticeTheory.∧Comm {a = x} {b = y}

  ⊓-idem :
    (x : DedekindCompletion ℓᴾ) →
    x ⊓ x ≡ x
  ⊓-idem x =
    DedekindCompletionPseudolatticeTheory.∧Idem {a = x}

  ⊓-assoc :
    (x y z : DedekindCompletion ℓᴾ) →
    x ⊓ (y ⊓ z) ≡ (x ⊓ y) ⊓ z
  ⊓-assoc x y z =
    DedekindCompletionPseudolatticeTheory.∧Assoc {a = x} {b = y} {c = z}

  ⊔-comm :
    (x y : DedekindCompletion ℓᴾ) →
    x ⊔ y ≡ y ⊔ x
  ⊔-comm x y =
    DedekindCompletionPseudolatticeTheory.∨Comm {a = x} {b = y}

  ⊔-idem :
    (x : DedekindCompletion ℓᴾ) →
    x ⊔ x ≡ x
  ⊔-idem x =
    DedekindCompletionPseudolatticeTheory.∨Idem {a = x}

  ⊔-assoc :
    (x y z : DedekindCompletion ℓᴾ) →
    x ⊔ (y ⊔ z) ≡ (x ⊔ y) ⊔ z
  ⊔-assoc x y z =
    DedekindCompletionPseudolatticeTheory.∨Assoc {a = x} {b = y} {c = z}

  ⊓-absorb-⊔ :
    (x y : DedekindCompletion ℓᴾ) →
    x ⊓ (x ⊔ y) ≡ x
  ⊓-absorb-⊔ x y =
    DedekindCompletionPseudolatticeTheory.≤→∧≡Left
      {a = x} {b = x ⊔ y} (left≤⊔ x y)

  ⊔-absorb-⊓ :
    (x y : DedekindCompletion ℓᴾ) →
    x ⊔ (x ⊓ y) ≡ x
  ⊔-absorb-⊓ x y =
    DedekindCompletionPseudolatticeTheory.≥→∨≡Left
      {a = x} {b = x ⊓ y} (⊓≤left x y)
