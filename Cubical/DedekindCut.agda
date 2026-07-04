{-

Constructive Dedekind cuts over the rationals.

This module deliberately avoids the classical powerset/Oracle setup used in
the Classical namespace.  The lower and upper cuts are level-polymorphic
predicate-valued maps into hProp, so using the definition does not require
LEM or propositional resizing.  Users who want a single small universe of
propositions can instantiate this with their own resizing principle elsewhere.

-}
{-# OPTIONS --safe #-}
module Cubical.DedekindCut where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (hPropExt)

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals using (ℚ ; fromNatℚ ; fromNegℚ)
import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Relation.Nullary using (¬_)
import Cubical.Relation.Binary.Order.StrictOrder as StrictOrder

import Cubical.Rationals as ℚExtra

private
  variable
    ℓ : Level


-- A small predicate on rationals.  Keeping the level explicit is what avoids
-- assuming propositional resizing.
ℚPred : (ℓ : Level) → Type (ℓ-suc ℓ)
ℚPred ℓ = ℚ → hProp ℓ

_∈_ : ℚ → ℚPred ℓ → Type ℓ
q ∈ P = P q .fst

infix 4 _∈_

isProp∈ : (P : ℚPred ℓ) → (q : ℚ) → isProp (q ∈ P)
isProp∈ P q = P q .snd


isSetℚPred : isSet (ℚPred ℓ)
isSetℚPred = isSetΠ λ _ → isSetHProp

_⊆_ : ℚPred ℓ → ℚPred ℓ → Type ℓ
P ⊆ Q = (q : ℚ) → q ∈ P → q ∈ Q

infix 4 _⊆_

isProp⊆ : (P Q : ℚPred ℓ) → isProp (P ⊆ Q)
isProp⊆ P Q = isPropΠ2 λ q _ → isProp∈ Q q

⊆-refl : (P : ℚPred ℓ) → P ⊆ P
⊆-refl P q q∈P = q∈P

⊆-trans : (P Q R : ℚPred ℓ) → P ⊆ Q → Q ⊆ R → P ⊆ R
⊆-trans P Q R P⊆Q Q⊆R q q∈P = Q⊆R q (P⊆Q q q∈P)

predExt : (P Q : ℚPred ℓ) → P ⊆ Q → Q ⊆ P → P ≡ Q
predExt P Q P⊆Q Q⊆P =
  funExt λ q →
    TypeOfHLevel≡ 1
      (hPropExt (isProp∈ P q) (isProp∈ Q q) (P⊆Q q) (Q⊆P q))


record isDedekindCut (L U : ℚPred ℓ) : Type ℓ where
  no-eta-equality

  field
    -- Both sides are inhabited.
    lower-inhabited : ∥ Σ[ q ∈ ℚ ] q ∈ L ∥₁
    upper-inhabited : ∥ Σ[ q ∈ ℚ ] q ∈ U ∥₁

    -- Lower and upper closure.
    lower-closed :
      (p q : ℚ) → p ℚOrder.< q → q ∈ L → p ∈ L

    upper-closed :
      (p q : ℚ) → p ℚOrder.< q → p ∈ U → q ∈ U

    -- Roundedness: membership can be improved inward.
    lower-rounded :
      (q : ℚ) → q ∈ L →
      ∥ Σ[ r ∈ ℚ ] (q ℚOrder.< r) × (r ∈ L) ∥₁

    upper-rounded :
      (q : ℚ) → q ∈ U →
      ∥ Σ[ r ∈ ℚ ] (r ℚOrder.< q) × (r ∈ U) ∥₁

    -- The two sides do not overlap.
    disjoint :
      (q : ℚ) → q ∈ L → q ∈ U → ⊥

    -- Constructive locatedness.  This is the replacement for deciding
    -- membership in one side of the cut.
    located :
      (p q : ℚ) → p ℚOrder.< q →
      ∥ (p ∈ L) ⊎ (q ∈ U) ∥₁


record DedekindCut (ℓ : Level) : Type (ℓ-suc ℓ) where
  no-eta-equality

  field
    lower : ℚPred ℓ
    upper : ℚPred ℓ
    is-cut : isDedekindCut lower upper

  open isDedekindCut is-cut public


open DedekindCut public


isPropIsDedekindCut : (L U : ℚPred ℓ) → isProp (isDedekindCut L U)
isPropIsDedekindCut L U c d i .isDedekindCut.lower-inhabited =
  squash₁ (c .isDedekindCut.lower-inhabited) (d .isDedekindCut.lower-inhabited) i
isPropIsDedekindCut L U c d i .isDedekindCut.upper-inhabited =
  squash₁ (c .isDedekindCut.upper-inhabited) (d .isDedekindCut.upper-inhabited) i
isPropIsDedekindCut L U c d i .isDedekindCut.lower-closed =
  isPropΠ4 (λ p _ _ _ → isProp∈ L p)
    (c .isDedekindCut.lower-closed) (d .isDedekindCut.lower-closed) i
isPropIsDedekindCut L U c d i .isDedekindCut.upper-closed =
  isPropΠ4 (λ _ q _ _ → isProp∈ U q)
    (c .isDedekindCut.upper-closed) (d .isDedekindCut.upper-closed) i
isPropIsDedekindCut L U c d i .isDedekindCut.lower-rounded =
  isPropΠ2 (λ _ _ → squash₁)
    (c .isDedekindCut.lower-rounded) (d .isDedekindCut.lower-rounded) i
isPropIsDedekindCut L U c d i .isDedekindCut.upper-rounded =
  isPropΠ2 (λ _ _ → squash₁)
    (c .isDedekindCut.upper-rounded) (d .isDedekindCut.upper-rounded) i
isPropIsDedekindCut L U c d i .isDedekindCut.disjoint =
  isPropΠ3 (λ _ _ _ → Empty.isProp⊥)
    (c .isDedekindCut.disjoint) (d .isDedekindCut.disjoint) i
isPropIsDedekindCut L U c d i .isDedekindCut.located =
  isPropΠ3 (λ _ _ _ → squash₁)
    (c .isDedekindCut.located) (d .isDedekindCut.located) i


path-DedekindCut :
  (x y : DedekindCut ℓ) →
  lower x ≡ lower y →
  upper x ≡ upper y →
  x ≡ y
path-DedekindCut x y lower-path upper-path i .lower = lower-path i
path-DedekindCut x y lower-path upper-path i .upper = upper-path i
path-DedekindCut x y lower-path upper-path i .is-cut =
  isProp→PathP
    (λ i → isPropIsDedekindCut (lower-path i) (upper-path i))
    (is-cut x) (is-cut y) i


cutExt :
  (x y : DedekindCut ℓ) →
  lower x ⊆ lower y →
  lower y ⊆ lower x →
  upper x ⊆ upper y →
  upper y ⊆ upper x →
  x ≡ y
cutExt x y Lx⊆Ly Ly⊆Lx Ux⊆Uy Uy⊆Ux =
  path-DedekindCut x y
    (predExt (lower x) (lower y) Lx⊆Ly Ly⊆Lx)
    (predExt (upper x) (upper y) Ux⊆Uy Uy⊆Ux)


private
  CutΣ : (ℓ : Level) → Type (ℓ-suc ℓ)
  CutΣ ℓ = Σ[ L ∈ ℚPred ℓ ] Σ[ U ∈ ℚPred ℓ ] isDedekindCut L U

  cut→Σ : DedekindCut ℓ → CutΣ ℓ
  cut→Σ x = lower x , upper x , is-cut x

  Σ→cut : CutΣ ℓ → DedekindCut ℓ
  Σ→cut (L , U , cut) = record
    { lower = L
    ; upper = U
    ; is-cut = cut
    }

  isSetCutΣ : isSet (CutΣ ℓ)
  isSetCutΣ =
    isOfHLevelΣ 2 isSetℚPred λ L →
    isOfHLevelΣ 2 isSetℚPred λ U →
    isProp→isSet (isPropIsDedekindCut L U)


isSetDedekindCut : isSet (DedekindCut ℓ)
isSetDedekindCut =
  isSetRetract cut→Σ Σ→cut
    (λ x → path-DedekindCut (Σ→cut (cut→Σ x)) x refl refl)
    isSetCutΣ


-- The rational cut associated to q.
ℚ→DedekindCut : ℚ → DedekindCut ℓ-zero
ℚ→DedekindCut q .lower p = (p ℚOrder.< q) , ℚOrder.isProp< p q
ℚ→DedekindCut q .upper p = (q ℚOrder.< p) , ℚOrder.isProp< q p
ℚ→DedekindCut q .is-cut .isDedekindCut.lower-inhabited =
  ∣ q ℚ.- ℚExtra.1ℚ , ℚExtra.q-1<q q ∣₁
ℚ→DedekindCut q .is-cut .isDedekindCut.upper-inhabited =
  ∣ q ℚ.+ ℚExtra.1ℚ , ℚExtra.q<q+1 q ∣₁
ℚ→DedekindCut q .is-cut .isDedekindCut.lower-closed =
  λ p r p<r r<q → ℚOrder.isTrans< p r q p<r r<q
ℚ→DedekindCut q .is-cut .isDedekindCut.upper-closed =
  λ p r p<r q<p → ℚOrder.isTrans< q p r q<p p<r
ℚ→DedekindCut q .is-cut .isDedekindCut.lower-rounded =
  λ p p<q → ℚExtra.dense {p = p} {q = q} p<q
ℚ→DedekindCut q .is-cut .isDedekindCut.upper-rounded =
  λ p q<p →
    Prop.rec squash₁
      (λ (r , q<r , r<p) → ∣ r , r<p , q<r ∣₁)
      (ℚExtra.dense {p = q} {q = p} q<p)
ℚ→DedekindCut q .is-cut .isDedekindCut.disjoint =
  λ p p<q q<p → ℚOrder.isAsym< p q p<q q<p
ℚ→DedekindCut q .is-cut .isDedekindCut.located =
  λ p r p<r → ℚOrder.isWeaklyLinear< p r q p<r


-- The same rational cut, lifted to an arbitrary predicate universe.
ℚ→DedekindCutAt : (ℓ : Level) → ℚ → DedekindCut ℓ
ℚ→DedekindCutAt ℓ q .lower p =
  Lift ℓ (p ℚOrder.< q) ,
  isOfHLevelLift 1 (ℚOrder.isProp< p q)
ℚ→DedekindCutAt ℓ q .upper p =
  Lift ℓ (q ℚOrder.< p) ,
  isOfHLevelLift 1 (ℚOrder.isProp< q p)
ℚ→DedekindCutAt ℓ q .is-cut .isDedekindCut.lower-inhabited =
  ∣ q ℚ.- ℚExtra.1ℚ , lift (ℚExtra.q-1<q q) ∣₁
ℚ→DedekindCutAt ℓ q .is-cut .isDedekindCut.upper-inhabited =
  ∣ q ℚ.+ ℚExtra.1ℚ , lift (ℚExtra.q<q+1 q) ∣₁
ℚ→DedekindCutAt ℓ q .is-cut .isDedekindCut.lower-closed =
  λ p r p<r r<q → lift (ℚOrder.isTrans< p r q p<r (Lift.lower r<q))
ℚ→DedekindCutAt ℓ q .is-cut .isDedekindCut.upper-closed =
  λ p r p<r q<p → lift (ℚOrder.isTrans< q p r (Lift.lower q<p) p<r)
ℚ→DedekindCutAt ℓ q .is-cut .isDedekindCut.lower-rounded =
  λ p p<q →
    Prop.rec squash₁
      (λ (r , p<r , r<q) → ∣ r , p<r , lift r<q ∣₁)
      (ℚExtra.dense {p = p} {q = q} (Lift.lower p<q))
ℚ→DedekindCutAt ℓ q .is-cut .isDedekindCut.upper-rounded =
  λ p q<p →
    Prop.rec squash₁
      (λ (r , q<r , r<p) → ∣ r , r<p , lift q<r ∣₁)
      (ℚExtra.dense {p = q} {q = p} (Lift.lower q<p))
ℚ→DedekindCutAt ℓ q .is-cut .isDedekindCut.disjoint =
  λ p p<q q<p → ℚOrder.isAsym< p q (Lift.lower p<q) (Lift.lower q<p)
ℚ→DedekindCutAt ℓ q .is-cut .isDedekindCut.located =
  λ p r p<r →
    Prop.rec squash₁
      (λ where
        (Sum.inl p<q) → ∣ Sum.inl (lift p<q) ∣₁
        (Sum.inr q<r) → ∣ Sum.inr (lift q<r) ∣₁)
      (ℚOrder.isWeaklyLinear< p r q p<r)


-- The order and strict order used constructively for Dedekind cuts.
module Order {ℓ : Level} where
  open DedekindCut

  _≤_ : DedekindCut ℓ → DedekindCut ℓ → Type ℓ
  x ≤ y = (q : ℚ) → q ∈ lower x → q ∈ lower y

  _<_ : DedekindCut ℓ → DedekindCut ℓ → Type ℓ
  x < y = ∥ Σ[ q ∈ ℚ ] (q ∈ upper x) × (q ∈ lower y) ∥₁

  _#_ : DedekindCut ℓ → DedekindCut ℓ → Type ℓ
  x # y = (x < y) ⊎ (y < x)

  infix 4 _≤_ _<_ _#_

  isProp≤ : (x y : DedekindCut ℓ) → isProp (x ≤ y)
  isProp≤ x y = isPropΠ2 λ q _ → isProp∈ (lower y) q

  isProp< : (x y : DedekindCut ℓ) → isProp (x < y)
  isProp< x y = squash₁

  ≡→≤ : {x y : DedekindCut ℓ} → x ≡ y → x ≤ y
  ≡→≤ x≡y q q∈Lx = subst (λ z → q ∈ lower z) x≡y q∈Lx

  ≤-refl : (x : DedekindCut ℓ) → x ≤ x
  ≤-refl x q q∈Lx = q∈Lx

  ≤-trans : (x y z : DedekindCut ℓ) → x ≤ y → y ≤ z → x ≤ z
  ≤-trans x y z x≤y y≤z q q∈Lx = y≤z q (x≤y q q∈Lx)

  lower<upper :
    (x : DedekindCut ℓ) (p q : ℚ) →
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
    (x : DedekindCut ℓ) (p q : ℚ) →
    p ℚOrder.≤ q → q ∈ lower x → p ∈ lower x
  lower-closed-≤ x p q p≤q q∈L with p ℚOrder.≟ q
  ... | ℚOrder.lt p<q = lower-closed x p q p<q q∈L
  ... | ℚOrder.eq p≡q = subst (λ r → r ∈ lower x) (sym p≡q) q∈L
  ... | ℚOrder.gt q<p = Empty.rec (ℚOrder.≤→≯ p q p≤q q<p)

  upper-closed-≤ :
    (x : DedekindCut ℓ) (p q : ℚ) →
    p ℚOrder.≤ q → p ∈ upper x → q ∈ upper x
  upper-closed-≤ x p q p≤q p∈U with p ℚOrder.≟ q
  ... | ℚOrder.lt p<q = upper-closed x p q p<q p∈U
  ... | ℚOrder.eq p≡q = subst (λ r → r ∈ upper x) p≡q p∈U
  ... | ℚOrder.gt q<p = Empty.rec (ℚOrder.≤→≯ p q p≤q q<p)

  lower→ℚ< :
    (x : DedekindCut ℓ) (q : ℚ) →
    q ∈ lower x →
    ℚ→DedekindCutAt ℓ q < x
  lower→ℚ< x q q∈Lx =
    Prop.rec squash₁
      (λ (r , q<r , r∈Lx) → ∣ r , lift q<r , r∈Lx ∣₁)
      (lower-rounded x q q∈Lx)

  ℚ<→lower :
    (x : DedekindCut ℓ) (q : ℚ) →
    ℚ→DedekindCutAt ℓ q < x →
    q ∈ lower x
  ℚ<→lower x q =
    Prop.rec (isProp∈ (lower x) q)
      (λ (r , q<r , r∈Lx) →
        lower-closed x q r (Lift.lower q<r) r∈Lx)

  upper→<ℚ :
    (x : DedekindCut ℓ) (q : ℚ) →
    q ∈ upper x →
    x < ℚ→DedekindCutAt ℓ q
  upper→<ℚ x q q∈Ux =
    Prop.rec squash₁
      (λ (r , r<q , r∈Ux) → ∣ r , r∈Ux , lift r<q ∣₁)
      (upper-rounded x q q∈Ux)

  <ℚ→upper :
    (x : DedekindCut ℓ) (q : ℚ) →
    x < ℚ→DedekindCutAt ℓ q →
    q ∈ upper x
  <ℚ→upper x q =
    Prop.rec (isProp∈ (upper x) q)
      (λ (r , r∈Ux , r<q) →
        upper-closed x r q (Lift.lower r<q) r∈Ux)

  lower⇔ℚ< :
    (x : DedekindCut ℓ) (q : ℚ) →
    (q ∈ lower x → ℚ→DedekindCutAt ℓ q < x)
    ×
    (ℚ→DedekindCutAt ℓ q < x → q ∈ lower x)
  lower⇔ℚ< x q = lower→ℚ< x q , ℚ<→lower x q

  upper⇔<ℚ :
    (x : DedekindCut ℓ) (q : ℚ) →
    (q ∈ upper x → x < ℚ→DedekindCutAt ℓ q)
    ×
    (x < ℚ→DedekindCutAt ℓ q → q ∈ upper x)
  upper⇔<ℚ x q = upper→<ℚ x q , <ℚ→upper x q

  rational-between :
    (x y : DedekindCut ℓ) →
    x < y →
    ∥ Σ[ q ∈ ℚ ] (x < ℚ→DedekindCutAt ℓ q) × (ℚ→DedekindCutAt ℓ q < y) ∥₁
  rational-between x y =
    Prop.rec squash₁
      (λ (q , q∈Ux , q∈Ly) →
        ∣ q , upper→<ℚ x q q∈Ux , lower→ℚ< y q q∈Ly ∣₁)

  rational-located :
    (x : DedekindCut ℓ) (p q : ℚ) →
    p ℚOrder.< q →
    ∥ (ℚ→DedekindCutAt ℓ p < x) ⊎ (x < ℚ→DedekindCutAt ℓ q) ∥₁
  rational-located x p q p<q =
    Prop.rec squash₁
      (λ where
        (Sum.inl p∈Lx) → ∣ Sum.inl (lower→ℚ< x p p∈Lx) ∣₁
        (Sum.inr q∈Ux) → ∣ Sum.inr (upper→<ℚ x q q∈Ux) ∣₁)
      (located x p q p<q)

  upper-inclusion-from-lower :
    (x y : DedekindCut ℓ) →
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

  ≤-antisym : (x y : DedekindCut ℓ) → x ≤ y → y ≤ x → x ≡ y
  ≤-antisym x y x≤y y≤x =
    cutExt x y x≤y y≤x
      (upper-inclusion-from-lower x y y≤x)
      (upper-inclusion-from-lower y x x≤y)

  <→≤ : (x y : DedekindCut ℓ) → x < y → x ≤ y
  <→≤ x y x<y q q∈Lx =
    Prop.rec (isProp∈ (lower y) q)
      (λ (r , r∈Ux , r∈Ly) →
        lower-closed y q r (lower<upper x q r q∈Lx r∈Ux) r∈Ly)
      x<y

  <-trans : (x y z : DedekindCut ℓ) → x < y → y < z → x < z
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

  ≤-<-trans : (x y z : DedekindCut ℓ) → x ≤ y → y < z → x < z
  ≤-<-trans x y z x≤y y<z =
    Prop.rec squash₁
      (λ (q , q∈Uy , q∈Lz) →
        ∣ q , upper-inclusion-from-lower y x x≤y q q∈Uy , q∈Lz ∣₁)
      y<z

  <-≤-trans : (x y z : DedekindCut ℓ) → x < y → y ≤ z → x < z
  <-≤-trans x y z x<y y≤z =
    Prop.rec squash₁
      (λ (q , q∈Ux , q∈Ly) → ∣ q , q∈Ux , y≤z q q∈Ly ∣₁)
      x<y

  <≤-asym : (x y : DedekindCut ℓ) → x < y → y ≤ x → ⊥
  <≤-asym x y x<y y≤x =
    Prop.rec Empty.isProp⊥
      (λ (q , q∈Ux , q∈Ly) → disjoint x q (y≤x q q∈Ly) q∈Ux)
      x<y

  <-irrefl : (x : DedekindCut ℓ) → ¬ x < x
  <-irrefl x x<x = <≤-asym x x x<x (≤-refl x)

  <-asym : (x y : DedekindCut ℓ) → x < y → ¬ y < x
  <-asym x y x<y y<x = <≤-asym x y x<y (<→≤ y x y<x)

  isWeaklyLinear< :
    (x y z : DedekindCut ℓ) → x < y → ∥ (x < z) ⊎ (z < y) ∥₁
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

  ≤→¬> : (x y : DedekindCut ℓ) → x ≤ y → ¬ y < x
  ≤→¬> x y x≤y y<x = <≤-asym y x y<x x≤y

  ¬>→≤ : (x y : DedekindCut ℓ) → ¬ y < x → x ≤ y
  ¬>→≤ x y ¬y<x q q∈Lx =
    Prop.rec (isProp∈ (lower y) q)
      (λ (r , q<r , r∈Lx) →
        Prop.rec (isProp∈ (lower y) q)
          (λ where
            (Sum.inl q∈Ly) → q∈Ly
            (Sum.inr r∈Uy) → Empty.rec (¬y<x ∣ r , r∈Uy , r∈Lx ∣₁))
          (located y q r q<r))
      (lower-rounded x q q∈Lx)

  ≤⇔¬> : (x y : DedekindCut ℓ) → (x ≤ y → ¬ y < x) × (¬ y < x → x ≤ y)
  ≤⇔¬> x y = ≤→¬> x y , ¬>→≤ x y

  isStrictOrder< : StrictOrder.IsStrictOrder _<_
  isStrictOrder< =
    StrictOrder.isstrictorder
      isSetDedekindCut
      isProp<
      <-irrefl
      <-trans
      <-asym
      isWeaklyLinear<

  isProp# : (x y : DedekindCut ℓ) → isProp (x # y)
  isProp# x y = Sum.isProp⊎ (isProp< x y) (isProp< y x) (<-asym x y)

  #-irrefl : (x : DedekindCut ℓ) → ¬ x # x
  #-irrefl x (Sum.inl x<x) = <-irrefl x x<x
  #-irrefl x (Sum.inr x<x) = <-irrefl x x<x

  #-sym : (x y : DedekindCut ℓ) → x # y → y # x
  #-sym x y (Sum.inl x<y) = Sum.inr x<y
  #-sym x y (Sum.inr y<x) = Sum.inl y<x

  #-cotrans :
    (x y z : DedekindCut ℓ) →
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

  #-tight : (x y : DedekindCut ℓ) → ¬ x # y → x ≡ y
  #-tight x y ¬x#y =
    ≤-antisym x y
      (¬>→≤ x y (λ y<x → ¬x#y (Sum.inr y<x)))
      (¬>→≤ y x (λ x<y → ¬x#y (Sum.inl x<y)))

  <→≠ : (x y : DedekindCut ℓ) → x < y → ¬ x ≡ y
  <→≠ x y x<y x≡y = <≤-asym x y x<y (≡→≤ (sym x≡y))

  #→≠ : (x y : DedekindCut ℓ) → x # y → ¬ x ≡ y
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

  meetLower : DedekindCut ℓ → DedekindCut ℓ → ℚPred ℓ
  meetLower x y q =
    ((q ∈ lower x) × (q ∈ lower y)) ,
    isProp× (isProp∈ (lower x) q) (isProp∈ (lower y) q)

  meetUpper : DedekindCut ℓ → DedekindCut ℓ → ℚPred ℓ
  meetUpper x y q =
    ∥ (q ∈ upper x) ⊎ (q ∈ upper y) ∥₁ , squash₁

  joinLower : DedekindCut ℓ → DedekindCut ℓ → ℚPred ℓ
  joinLower x y q =
    ∥ (q ∈ lower x) ⊎ (q ∈ lower y) ∥₁ , squash₁

  joinUpper : DedekindCut ℓ → DedekindCut ℓ → ℚPred ℓ
  joinUpper x y q =
    ((q ∈ upper x) × (q ∈ upper y)) ,
    isProp× (isProp∈ (upper x) q) (isProp∈ (upper y) q)

  meet-is-cut :
    (x y : DedekindCut ℓ) →
    isDedekindCut (meetLower x y) (meetUpper x y)
  meet-is-cut x y .isDedekindCut.lower-inhabited =
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
  meet-is-cut x y .isDedekindCut.upper-inhabited =
    Prop.rec squash₁
      (λ (q , q∈Ux) → ∣ q , ∣ Sum.inl q∈Ux ∣₁ ∣₁)
      (upper-inhabited x)
  meet-is-cut x y .isDedekindCut.lower-closed =
    λ p q p<q (q∈Lx , q∈Ly) →
      lower-closed x p q p<q q∈Lx ,
      lower-closed y p q p<q q∈Ly
  meet-is-cut x y .isDedekindCut.upper-closed =
    λ p q p<q p∈Uxy →
      Prop.rec squash₁
        (λ where
          (Sum.inl p∈Ux) → ∣ Sum.inl (upper-closed x p q p<q p∈Ux) ∣₁
          (Sum.inr p∈Uy) → ∣ Sum.inr (upper-closed y p q p<q p∈Uy) ∣₁)
        p∈Uxy
  meet-is-cut x y .isDedekindCut.lower-rounded =
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
  meet-is-cut x y .isDedekindCut.upper-rounded =
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
  meet-is-cut x y .isDedekindCut.disjoint =
    λ q (q∈Lx , q∈Ly) q∈Uxy →
      Prop.rec Empty.isProp⊥
        (λ where
          (Sum.inl q∈Ux) → disjoint x q q∈Lx q∈Ux
          (Sum.inr q∈Uy) → disjoint y q q∈Ly q∈Uy)
        q∈Uxy
  meet-is-cut x y .isDedekindCut.located =
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

  _⊓_ : DedekindCut ℓ → DedekindCut ℓ → DedekindCut ℓ
  x ⊓ y = record
    { lower = meetLower x y
    ; upper = meetUpper x y
    ; is-cut = meet-is-cut x y
    }

  join-is-cut :
    (x y : DedekindCut ℓ) →
    isDedekindCut (joinLower x y) (joinUpper x y)
  join-is-cut x y .isDedekindCut.lower-inhabited =
    Prop.rec squash₁
      (λ (q , q∈Lx) → ∣ q , ∣ Sum.inl q∈Lx ∣₁ ∣₁)
      (lower-inhabited x)
  join-is-cut x y .isDedekindCut.upper-inhabited =
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
  join-is-cut x y .isDedekindCut.lower-closed =
    λ p q p<q q∈Lxy →
      Prop.rec squash₁
        (λ where
          (Sum.inl q∈Lx) → ∣ Sum.inl (lower-closed x p q p<q q∈Lx) ∣₁
          (Sum.inr q∈Ly) → ∣ Sum.inr (lower-closed y p q p<q q∈Ly) ∣₁)
        q∈Lxy
  join-is-cut x y .isDedekindCut.upper-closed =
    λ p q p<q (p∈Ux , p∈Uy) →
      upper-closed x p q p<q p∈Ux ,
      upper-closed y p q p<q p∈Uy
  join-is-cut x y .isDedekindCut.lower-rounded =
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
  join-is-cut x y .isDedekindCut.upper-rounded =
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
  join-is-cut x y .isDedekindCut.disjoint =
    λ q q∈Lxy (q∈Ux , q∈Uy) →
      Prop.rec Empty.isProp⊥
        (λ where
          (Sum.inl q∈Lx) → disjoint x q q∈Lx q∈Ux
          (Sum.inr q∈Ly) → disjoint y q q∈Ly q∈Uy)
        q∈Lxy
  join-is-cut x y .isDedekindCut.located =
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

  _⊔_ : DedekindCut ℓ → DedekindCut ℓ → DedekindCut ℓ
  x ⊔ y = record
    { lower = joinLower x y
    ; upper = joinUpper x y
    ; is-cut = join-is-cut x y
    }

  ⊓≤left : (x y : DedekindCut ℓ) → (x ⊓ y) ≤ x
  ⊓≤left x y q (q∈Lx , _) = q∈Lx

  ⊓≤right : (x y : DedekindCut ℓ) → (x ⊓ y) ≤ y
  ⊓≤right x y q (_ , q∈Ly) = q∈Ly

  ≤⊓ :
    (z x y : DedekindCut ℓ) →
    z ≤ x → z ≤ y → z ≤ (x ⊓ y)
  ≤⊓ z x y z≤x z≤y q q∈Lz = z≤x q q∈Lz , z≤y q q∈Lz

  left≤⊔ : (x y : DedekindCut ℓ) → x ≤ (x ⊔ y)
  left≤⊔ x y q q∈Lx = ∣ Sum.inl q∈Lx ∣₁

  right≤⊔ : (x y : DedekindCut ℓ) → y ≤ (x ⊔ y)
  right≤⊔ x y q q∈Ly = ∣ Sum.inr q∈Ly ∣₁

  ⊔≤ :
    (x y z : DedekindCut ℓ) →
    x ≤ z → y ≤ z → (x ⊔ y) ≤ z
  ⊔≤ x y z x≤z y≤z q q∈Lxy =
    Prop.rec (isProp∈ (lower z) q)
      (λ where
        (Sum.inl q∈Lx) → x≤z q q∈Lx
        (Sum.inr q∈Ly) → y≤z q q∈Ly)
      q∈Lxy

  ⊓-comm : (x y : DedekindCut ℓ) → x ⊓ y ≡ y ⊓ x
  ⊓-comm x y =
    ≤-antisym (x ⊓ y) (y ⊓ x)
      (λ q (q∈Lx , q∈Ly) → q∈Ly , q∈Lx)
      (λ q (q∈Ly , q∈Lx) → q∈Lx , q∈Ly)

  ⊓-idem : (x : DedekindCut ℓ) → x ⊓ x ≡ x
  ⊓-idem x =
    ≤-antisym (x ⊓ x) x
      (λ q (q∈Lx , _) → q∈Lx)
      (λ q q∈Lx → q∈Lx , q∈Lx)

  ⊓-assoc :
    (x y z : DedekindCut ℓ) →
    x ⊓ (y ⊓ z) ≡ (x ⊓ y) ⊓ z
  ⊓-assoc x y z =
    ≤-antisym (x ⊓ (y ⊓ z)) ((x ⊓ y) ⊓ z)
      (λ q (q∈Lx , q∈Ly , q∈Lz) → (q∈Lx , q∈Ly) , q∈Lz)
      (λ q ((q∈Lx , q∈Ly) , q∈Lz) → q∈Lx , q∈Ly , q∈Lz)

  ⊔-comm : (x y : DedekindCut ℓ) → x ⊔ y ≡ y ⊔ x
  ⊔-comm x y =
    ≤-antisym (x ⊔ y) (y ⊔ x)
      (λ q q∈Lxy →
        Prop.rec squash₁
          (λ where
            (Sum.inl q∈Lx) → ∣ Sum.inr q∈Lx ∣₁
            (Sum.inr q∈Ly) → ∣ Sum.inl q∈Ly ∣₁)
          q∈Lxy)
      (λ q q∈Lyx →
        Prop.rec squash₁
          (λ where
            (Sum.inl q∈Ly) → ∣ Sum.inr q∈Ly ∣₁
            (Sum.inr q∈Lx) → ∣ Sum.inl q∈Lx ∣₁)
          q∈Lyx)

  ⊔-idem : (x : DedekindCut ℓ) → x ⊔ x ≡ x
  ⊔-idem x =
    ≤-antisym (x ⊔ x) x
      (λ q q∈Lxx →
        Prop.rec (isProp∈ (lower x) q)
          (λ where
            (Sum.inl q∈Lx) → q∈Lx
            (Sum.inr q∈Lx) → q∈Lx)
          q∈Lxx)
      (λ q q∈Lx → ∣ Sum.inl q∈Lx ∣₁)

  ⊔-assoc :
    (x y z : DedekindCut ℓ) →
    x ⊔ (y ⊔ z) ≡ (x ⊔ y) ⊔ z
  ⊔-assoc x y z =
    ≤-antisym (x ⊔ (y ⊔ z)) ((x ⊔ y) ⊔ z)
      (λ q q∈Lxyz →
        Prop.rec squash₁
          (λ where
            (Sum.inl q∈Lx) → ∣ Sum.inl ∣ Sum.inl q∈Lx ∣₁ ∣₁
            (Sum.inr q∈Lyz) →
              Prop.rec squash₁
                (λ where
                  (Sum.inl q∈Ly) → ∣ Sum.inl ∣ Sum.inr q∈Ly ∣₁ ∣₁
                  (Sum.inr q∈Lz) → ∣ Sum.inr q∈Lz ∣₁)
                q∈Lyz)
          q∈Lxyz)
      (λ q q∈Lxyz →
        Prop.rec squash₁
          (λ where
            (Sum.inl q∈Lxy) →
              Prop.rec squash₁
                (λ where
                  (Sum.inl q∈Lx) → ∣ Sum.inl q∈Lx ∣₁
                  (Sum.inr q∈Ly) → ∣ Sum.inr ∣ Sum.inl q∈Ly ∣₁ ∣₁)
                q∈Lxy
            (Sum.inr q∈Lz) → ∣ Sum.inr ∣ Sum.inr q∈Lz ∣₁ ∣₁)
          q∈Lxyz)

  ⊓-absorb-⊔ : (x y : DedekindCut ℓ) → x ⊓ (x ⊔ y) ≡ x
  ⊓-absorb-⊔ x y =
    ≤-antisym (x ⊓ (x ⊔ y)) x
      (λ q (q∈Lx , _) → q∈Lx)
      (λ q q∈Lx → q∈Lx , ∣ Sum.inl q∈Lx ∣₁)

  ⊔-absorb-⊓ : (x y : DedekindCut ℓ) → x ⊔ (x ⊓ y) ≡ x
  ⊔-absorb-⊓ x y =
    ≤-antisym (x ⊔ (x ⊓ y)) x
      (λ q q∈Lxxy →
        Prop.rec (isProp∈ (lower x) q)
          (λ where
            (Sum.inl q∈Lx) → q∈Lx
            (Sum.inr (q∈Lx , _)) → q∈Lx)
          q∈Lxxy)
      (λ q q∈Lx → ∣ Sum.inl q∈Lx ∣₁)


module RationalEmbedding where
  open Order {ℓ-zero}

  ℚ→<-pres :
    (p q : ℚ) → p ℚOrder.< q →
    ℚ→DedekindCut p < ℚ→DedekindCut q
  ℚ→<-pres p q p<q =
    Prop.rec squash₁
      (λ (r , p<r , r<q) → ∣ r , p<r , r<q ∣₁)
      (ℚExtra.dense {p = p} {q = q} p<q)

  ℚ→<-reflect :
    (p q : ℚ) →
    ℚ→DedekindCut p < ℚ→DedekindCut q →
    p ℚOrder.< q
  ℚ→<-reflect p q =
    Prop.rec (ℚOrder.isProp< p q)
      (λ (r , p<r , r<q) → ℚOrder.isTrans< p r q p<r r<q)

  ℚ→<-iff :
    (p q : ℚ) →
    (p ℚOrder.< q → ℚ→DedekindCut p < ℚ→DedekindCut q)
    ×
    (ℚ→DedekindCut p < ℚ→DedekindCut q → p ℚOrder.< q)
  ℚ→<-iff p q = ℚ→<-pres p q , ℚ→<-reflect p q

  ℚ→≤-pres :
    (p q : ℚ) → p ℚOrder.≤ q →
    ℚ→DedekindCut p ≤ ℚ→DedekindCut q
  ℚ→≤-pres p q p≤q r r<p = ℚOrder.isTrans<≤ r p q r<p p≤q

  ℚ→≤-reflect :
    (p q : ℚ) →
    ℚ→DedekindCut p ≤ ℚ→DedekindCut q →
    p ℚOrder.≤ q
  ℚ→≤-reflect p q p≤q =
    ℚOrder.≮→≥ q p λ q<p →
      Prop.rec Empty.isProp⊥
        (λ (r , q<r , r<p) → ℚOrder.isAsym< q r q<r (p≤q r r<p))
        (ℚExtra.dense {p = q} {q = p} q<p)

  ℚ→≤-iff :
    (p q : ℚ) →
    (p ℚOrder.≤ q → ℚ→DedekindCut p ≤ ℚ→DedekindCut q)
    ×
    (ℚ→DedekindCut p ≤ ℚ→DedekindCut q → p ℚOrder.≤ q)
  ℚ→≤-iff p q = ℚ→≤-pres p q , ℚ→≤-reflect p q

  ℚ→-injective :
    (p q : ℚ) →
    ℚ→DedekindCut p ≡ ℚ→DedekindCut q →
    p ≡ q
  ℚ→-injective p q p*≡q* =
    ℚOrder.isAntisym≤ p q
      (ℚ→≤-reflect p q (≡→≤ p*≡q*))
      (ℚ→≤-reflect q p (≡→≤ (sym p*≡q*)))

  0<1-cut : ℚ→DedekindCut ℚExtra.0ℚ < ℚ→DedekindCut ℚExtra.1ℚ
  0<1-cut = ℚ→<-pres ℚExtra.0ℚ ℚExtra.1ℚ ℚExtra.0<1


module RationalEmbeddingAt {ℓ : Level} where
  open Order {ℓ}

  ℚ→<-pres :
    (p q : ℚ) → p ℚOrder.< q →
    ℚ→DedekindCutAt ℓ p < ℚ→DedekindCutAt ℓ q
  ℚ→<-pres p q p<q =
    Prop.rec squash₁
      (λ (r , p<r , r<q) → ∣ r , lift p<r , lift r<q ∣₁)
      (ℚExtra.dense {p = p} {q = q} p<q)

  ℚ→<-reflect :
    (p q : ℚ) →
    ℚ→DedekindCutAt ℓ p < ℚ→DedekindCutAt ℓ q →
    p ℚOrder.< q
  ℚ→<-reflect p q =
    Prop.rec (ℚOrder.isProp< p q)
      (λ (r , p<r , r<q) →
        ℚOrder.isTrans< p r q (Lift.lower p<r) (Lift.lower r<q))

  ℚ→<-iff :
    (p q : ℚ) →
    (p ℚOrder.< q → ℚ→DedekindCutAt ℓ p < ℚ→DedekindCutAt ℓ q)
    ×
    (ℚ→DedekindCutAt ℓ p < ℚ→DedekindCutAt ℓ q → p ℚOrder.< q)
  ℚ→<-iff p q = ℚ→<-pres p q , ℚ→<-reflect p q

  ℚ→≤-pres :
    (p q : ℚ) → p ℚOrder.≤ q →
    ℚ→DedekindCutAt ℓ p ≤ ℚ→DedekindCutAt ℓ q
  ℚ→≤-pres p q p≤q r r<p =
    lift (ℚOrder.isTrans<≤ r p q (Lift.lower r<p) p≤q)

  ℚ→≤-reflect :
    (p q : ℚ) →
    ℚ→DedekindCutAt ℓ p ≤ ℚ→DedekindCutAt ℓ q →
    p ℚOrder.≤ q
  ℚ→≤-reflect p q p≤q =
    ℚOrder.≮→≥ q p λ q<p →
      Prop.rec Empty.isProp⊥
        (λ (r , q<r , r<p) →
          ℚOrder.isAsym< q r q<r (Lift.lower (p≤q r (lift r<p))))
        (ℚExtra.dense {p = q} {q = p} q<p)

  ℚ→≤-iff :
    (p q : ℚ) →
    (p ℚOrder.≤ q → ℚ→DedekindCutAt ℓ p ≤ ℚ→DedekindCutAt ℓ q)
    ×
    (ℚ→DedekindCutAt ℓ p ≤ ℚ→DedekindCutAt ℓ q → p ℚOrder.≤ q)
  ℚ→≤-iff p q = ℚ→≤-pres p q , ℚ→≤-reflect p q

  ℚ→-injective :
    (p q : ℚ) →
    ℚ→DedekindCutAt ℓ p ≡ ℚ→DedekindCutAt ℓ q →
    p ≡ q
  ℚ→-injective p q p*≡q* =
    ℚOrder.isAntisym≤ p q
      (ℚ→≤-reflect p q (≡→≤ p*≡q*))
      (ℚ→≤-reflect q p (≡→≤ (sym p*≡q*)))

  0<1-cut : ℚ→DedekindCutAt ℓ ℚExtra.0ℚ < ℚ→DedekindCutAt ℓ ℚExtra.1ℚ
  0<1-cut = ℚ→<-pres ℚExtra.0ℚ ℚExtra.1ℚ ℚExtra.0<1


module Archimedean {ℓ : Level} where
  open Order {ℓ}

  upper-rational-bound :
    (x : DedekindCut ℓ) →
    ∥ Σ[ n ∈ ℕ ] x < ℚ→DedekindCutAt ℓ (ℚExtra.natMul n ℚExtra.1ℚ) ∥₁
  upper-rational-bound x =
    Prop.rec squash₁
      (λ (q , q∈Ux) →
        let (n , q<n) = ℚExtra.archimedes q ℚExtra.1ℚ ℚExtra.0<1 in
        ∣ n , ∣ q , q∈Ux , lift q<n ∣₁ ∣₁)
      (upper-inhabited x)

  lower-rational-bound :
    (x : DedekindCut ℓ) →
    ∥ Σ[ n ∈ ℕ ] ℚ→DedekindCutAt ℓ (ℚ.- ℚExtra.natMul n ℚExtra.1ℚ) < x ∥₁
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

  CloseBounds : DedekindCut ℓ → ℚ → Type ℓ
  CloseBounds x ε =
    Σ[ p ∈ ℚ ] Σ[ q ∈ ℚ ]
      (p ∈ lower x) ×
      (q ∈ upper x) ×
      (p ℚOrder.< q) ×
      (q ℚOrder.< p ℚ.+ ε)

  BoundedCloseBounds : DedekindCut ℓ → ℚ → ℚ → Type ℓ
  BoundedCloseBounds x ε u =
    Σ[ p ∈ ℚ ] Σ[ q ∈ ℚ ]
      (p ∈ lower x) ×
      (q ∈ upper x) ×
      (p ℚOrder.< q) ×
      (q ℚOrder.< p ℚ.+ ε) ×
      (q ℚOrder.≤ u)

  bounds :
    (x : DedekindCut ℓ) →
    ∥ Σ[ p ∈ ℚ ] Σ[ q ∈ ℚ ]
      (p ∈ lower x) × (q ∈ upper x) × (p ℚOrder.< q) ∥₁
  bounds x =
    Prop.rec2 squash₁
      (λ (p , p∈Lx) (q , q∈Ux) →
        ∣ p , q , p∈Lx , q∈Ux , lower<upper x p q p∈Lx q∈Ux ∣₁)
      (lower-inhabited x)
      (upper-inhabited x)

  rounded-upper-close :
    (x : DedekindCut ℓ) (ε p q : ℚ) →
    p ∈ lower x →
    q ∈ upper x →
    q ℚOrder.≤ p ℚ.+ ε →
    ∥ CloseBounds x ε ∥₁
  rounded-upper-close x ε p q p∈Lx q∈Ux q≤p+ε =
    Prop.rec squash₁
      (λ (r , r<q , r∈Ux) →
        ∣ p , r
        , p∈Lx
        , r∈Ux
        , lower<upper x p r p∈Lx r∈Ux
        , ℚOrder.isTrans<≤ r q (p ℚ.+ ε) r<q q≤p+ε
        ∣₁)
      (upper-rounded x q q∈Ux)

  close-from-< :
    (x : DedekindCut ℓ) (ε p q : ℚ) →
    p ∈ lower x →
    q ∈ upper x →
    q ℚOrder.< p ℚ.+ ε →
    ∥ CloseBounds x ε ∥₁
  close-from-< x ε p q p∈Lx q∈Ux q<p+ε =
    rounded-upper-close x ε p q p∈Lx q∈Ux
      (ℚOrder.<Weaken≤ q (p ℚ.+ ε) q<p+ε)

  bounded-rounded-upper-close :
    (x : DedekindCut ℓ) (ε p q u : ℚ) →
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
    (x : DedekindCut ℓ) (ε p q u : ℚ) →
    p ∈ lower x →
    q ∈ upper x →
    q ℚOrder.< p ℚ.+ ε →
    q ℚOrder.≤ u →
    ∥ BoundedCloseBounds x ε u ∥₁
  bounded-close-from-< x ε p q u p∈Lx q∈Ux q<p+ε q≤u =
    bounded-rounded-upper-close x ε p q u p∈Lx q∈Ux
      (ℚOrder.<Weaken≤ q (p ℚ.+ ε) q<p+ε)
      q≤u

  close-from-sandwich :
    (x : DedekindCut ℓ) (ε p q : ℚ) →
    ℚ→DedekindCutAt ℓ p < x →
    x < ℚ→DedekindCutAt ℓ q →
    q ℚOrder.≤ p ℚ.+ ε →
    ∥ CloseBounds x ε ∥₁
  close-from-sandwich x ε p q p<x x<q q≤p+ε =
    rounded-upper-close x ε p q
      (ℚ<→lower x p p<x)
      (<ℚ→upper x q x<q)
      q≤p+ε

  bounded-scan-close :
    (x : DedekindCut ℓ) (ε δ : ℚ) →
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

  scan-close :
    (x : DedekindCut ℓ) (ε δ : ℚ) →
    ℚExtra.0ℚ ℚOrder.< δ →
    δ ℚ.+ δ ≡ ε →
    (n : ℕ) (p q : ℚ) →
    p ∈ lower x →
    q ∈ upper x →
    q ℚOrder.≤ p ℚ.+ ℚExtra.natMul (suc n) δ →
    ∥ CloseBounds x ε ∥₁
  scan-close x ε δ 0<δ δ+δ≡ε zero p q p∈Lx q∈Ux q≤p+δ =
    close-from-< x ε p q p∈Lx q∈Ux q<p+ε
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

  scan-close x ε δ 0<δ δ+δ≡ε (suc n) p q p∈Lx q∈Ux q≤bound =
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

    step :
      (p₁ ∈ lower x) ⊎ (p₂ ∈ upper x) →
      ∥ CloseBounds x ε ∥₁
    step (Sum.inl p₁∈Lx) =
      scan-close x ε δ 0<δ δ+δ≡ε n p₁ q p₁∈Lx q∈Ux q≤shifted
    step (Sum.inr p₂∈Ux) =
      rounded-upper-close x ε p p₂ p∈Lx p₂∈Ux p₂≤p+ε

  close-bounds :
    (x : DedekindCut ℓ) (ε : ℚ) →
    ℚExtra.0ℚ ℚOrder.< ε →
    ∥ CloseBounds x ε ∥₁
  close-bounds x ε 0<ε =
    Prop.rec2 squash₁ initial
      (lower-inhabited x)
      (upper-inhabited x)
    where
    δ : ℚ
    δ = ε ℚ.· ℚExtra.1/2

    0<δ : ℚExtra.0ℚ ℚOrder.< δ
    0<δ = ℚExtra.positive-half {ε = ε} 0<ε

    δ+δ≡ε : δ ℚ.+ δ ≡ ε
    δ+δ≡ε = ℚExtra.half+half ε

    initial :
      Σ[ p ∈ ℚ ] p ∈ lower x →
      Σ[ q ∈ ℚ ] q ∈ upper x →
      ∥ CloseBounds x ε ∥₁
    initial (p , p∈Lx) (q , q∈Ux) =
      scan-close x ε δ 0<δ δ+δ≡ε n p q p∈Lx q∈Ux q≤p+sucnδ
      where
      n : ℕ
      n = fst (ℚExtra.archimedes (q ℚ.- p) δ 0<δ)

      q-p<nδ : q ℚ.- p ℚOrder.< ℚExtra.natMul n δ
      q-p<nδ = snd (ℚExtra.archimedes (q ℚ.- p) δ 0<δ)

      q<p+nδ : q ℚOrder.< p ℚ.+ ℚExtra.natMul n δ
      q<p+nδ =
        ℚExtra.diff<→shift< p q (ℚExtra.natMul n δ) q-p<nδ

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

      q<p+sucnδ : q ℚOrder.< p ℚ.+ ℚExtra.natMul (suc n) δ
      q<p+sucnδ =
        ℚOrder.isTrans< q
          (p ℚ.+ ℚExtra.natMul n δ)
          (p ℚ.+ ℚExtra.natMul (suc n) δ)
          q<p+nδ
          p+nδ<p+sucnδ

      q≤p+sucnδ : q ℚOrder.≤ p ℚ.+ ℚExtra.natMul (suc n) δ
      q≤p+sucnδ =
        ℚOrder.<Weaken≤ q
          (p ℚ.+ ℚExtra.natMul (suc n) δ)
          q<p+sucnδ

  bounded-close-bounds :
    (x : DedekindCut ℓ) (ε u : ℚ) →
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


module Algebra {ℓ : Level} where
  -_ : DedekindCut ℓ → DedekindCut ℓ
  (- x) .lower q = (ℚ.- q ∈ upper x) , isProp∈ (upper x) (ℚ.- q)
  (- x) .upper q = (ℚ.- q ∈ lower x) , isProp∈ (lower x) (ℚ.- q)
  (- x) .is-cut .isDedekindCut.lower-inhabited =
    Prop.rec squash₁
      (λ (q , q∈Ux) →
        ∣ ℚ.- q
        , subst (λ r → r ∈ upper x) (sym (ℚ.-Invol q)) q∈Ux
        ∣₁)
      (upper-inhabited x)
  (- x) .is-cut .isDedekindCut.upper-inhabited =
    Prop.rec squash₁
      (λ (q , q∈Lx) →
        ∣ ℚ.- q
        , subst (λ r → r ∈ lower x) (sym (ℚ.-Invol q)) q∈Lx
        ∣₁)
      (lower-inhabited x)
  (- x) .is-cut .isDedekindCut.lower-closed =
    λ p q p<q -q∈Ux →
      upper-closed x (ℚ.- q) (ℚ.- p)
        (ℚExtra.negReverse< {p = p} {q = q} p<q)
        -q∈Ux
  (- x) .is-cut .isDedekindCut.upper-closed =
    λ p q p<q -p∈Lx →
      lower-closed x (ℚ.- q) (ℚ.- p)
        (ℚExtra.negReverse< {p = p} {q = q} p<q)
        -p∈Lx
  (- x) .is-cut .isDedekindCut.lower-rounded =
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
  (- x) .is-cut .isDedekindCut.upper-rounded =
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
  (- x) .is-cut .isDedekindCut.disjoint =
    λ q -q∈Ux -q∈Lx → disjoint x (ℚ.- q) -q∈Lx -q∈Ux
  (- x) .is-cut .isDedekindCut.located =
    λ p q p<q →
      Prop.rec squash₁
        (λ where
          (Sum.inl -q∈Lx) → ∣ Sum.inr -q∈Lx ∣₁
          (Sum.inr -p∈Ux) → ∣ Sum.inl -p∈Ux ∣₁)
        (located x (ℚ.- q) (ℚ.- p)
          (ℚExtra.negReverse< {p = p} {q = q} p<q))

  infix 8 -_

  neg-involutive : (x : DedekindCut ℓ) → - (- x) ≡ x
  neg-involutive x =
    cutExt (- (- x)) x
      (λ q -- -(-q) is in the lower cut of x.
        → subst (λ r → r ∈ lower x) (ℚ.-Invol q))
      (λ q → subst (λ r → r ∈ lower x) (sym (ℚ.-Invol q)))
      (λ q → subst (λ r → r ∈ upper x) (ℚ.-Invol q))
      (λ q → subst (λ r → r ∈ upper x) (sym (ℚ.-Invol q)))

  neg-≤-reverse :
    (x y : DedekindCut ℓ) →
    Order._≤_ {ℓ = ℓ} x y →
    Order._≤_ {ℓ = ℓ} (- y) (- x)
  neg-≤-reverse x y x≤y q -q∈Uy =
    Order.upper-inclusion-from-lower y x x≤y (ℚ.- q) -q∈Uy

  neg-≤-reflect :
    (x y : DedekindCut ℓ) →
    Order._≤_ {ℓ = ℓ} (- y) (- x) →
    Order._≤_ {ℓ = ℓ} x y
  neg-≤-reflect x y -y≤-x q q∈Lx =
    subst (λ r → r ∈ lower y) (ℚ.-Invol q)
      (Order.upper-inclusion-from-lower (- x) (- y) -y≤-x
        (ℚ.- q)
        (subst (λ r → r ∈ lower x) (sym (ℚ.-Invol q)) q∈Lx))

  neg-≤-iff :
    (x y : DedekindCut ℓ) →
    (Order._≤_ {ℓ = ℓ} x y → Order._≤_ {ℓ = ℓ} (- y) (- x))
    ×
    (Order._≤_ {ℓ = ℓ} (- y) (- x) → Order._≤_ {ℓ = ℓ} x y)
  neg-≤-iff x y = neg-≤-reverse x y , neg-≤-reflect x y

  neg-<-reverse :
    (x y : DedekindCut ℓ) →
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
    (x y : DedekindCut ℓ) →
    Order._<_ {ℓ = ℓ} (- y) (- x) →
    Order._<_ {ℓ = ℓ} x y
  neg-<-reflect x y -y<-x =
    subst2 (Order._<_ {ℓ = ℓ})
      (neg-involutive x)
      (neg-involutive y)
      (neg-<-reverse (- y) (- x) -y<-x)

  neg-<-iff :
    (x y : DedekindCut ℓ) →
    (Order._<_ {ℓ = ℓ} x y → Order._<_ {ℓ = ℓ} (- y) (- x))
    ×
    (Order._<_ {ℓ = ℓ} (- y) (- x) → Order._<_ {ℓ = ℓ} x y)
  neg-<-iff x y = neg-<-reverse x y , neg-<-reflect x y

  neg-rational :
    (q : ℚ) →
    - ℚ→DedekindCutAt ℓ q ≡ ℚ→DedekindCutAt ℓ (ℚ.- q)
  neg-rational q =
    cutExt (- ℚ→DedekindCutAt ℓ q) (ℚ→DedekindCutAt ℓ (ℚ.- q))
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
