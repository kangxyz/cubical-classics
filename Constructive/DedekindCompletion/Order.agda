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
open import Cubical.Relation.Nullary using (¬_)
import Cubical.Relation.Binary.Order.StrictOrder as StrictOrder

import Constructive.Algebra.LinearlyOrderedCommRing.Base as LinearBase
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.DedekindCompletion.Base

private
  variable
    ℓ ℓ' ℓᴾ : Level


module CompletionOrder (𝒦 : LinearlyOrderedField ℓ ℓ') where

  open CompletionBase 𝒦
  open LinearlyOrderedFieldStr 𝒦
    using (middle ; middle>l ; middle<r ; trichotomy)
    renaming
      ( _<_ to _<K_
      ; isProp< to isProp<K
      ; <-trans to <K-trans
      ; <-asym to <K-asym
      ; <-arefl to <K-arefl
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
