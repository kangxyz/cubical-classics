{-

Constructive Dedekind reals over the rationals.

This module contains the basic definition of constructive Dedekind reals.  The
lower and upper cuts are level-polymorphic predicate-valued maps into hProp,
so using the definition does not require LEM or propositional resizing.  The
Oracle-based classical completion by cuts is kept in Classical.DedekindCut.

-}
{-# OPTIONS --safe #-}
module Constructive.DedekindReals.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (hPropExt)

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Rationals using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; squash₁)

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


record IsDedekindReal (L U : ℚPred ℓ) : Type ℓ where
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
      (p q : ℚ) → p ℚOrder.< q → ∥ (p ∈ L) ⊎ (q ∈ U) ∥₁


record DedekindReal (ℓ : Level) : Type (ℓ-suc ℓ) where
  no-eta-equality

  field
    lower : ℚPred ℓ
    upper : ℚPred ℓ
    isDedekindReal : IsDedekindReal lower upper

  open IsDedekindReal isDedekindReal public


open DedekindReal public


isPropIsDedekindReal : (L U : ℚPred ℓ) → isProp (IsDedekindReal L U)
isPropIsDedekindReal L U c d i .IsDedekindReal.lower-inhabited =
  squash₁ (c .IsDedekindReal.lower-inhabited) (d .IsDedekindReal.lower-inhabited) i
isPropIsDedekindReal L U c d i .IsDedekindReal.upper-inhabited =
  squash₁ (c .IsDedekindReal.upper-inhabited) (d .IsDedekindReal.upper-inhabited) i
isPropIsDedekindReal L U c d i .IsDedekindReal.lower-closed =
  isPropΠ4 (λ p _ _ _ → isProp∈ L p)
    (c .IsDedekindReal.lower-closed) (d .IsDedekindReal.lower-closed) i
isPropIsDedekindReal L U c d i .IsDedekindReal.upper-closed =
  isPropΠ4 (λ _ q _ _ → isProp∈ U q)
    (c .IsDedekindReal.upper-closed) (d .IsDedekindReal.upper-closed) i
isPropIsDedekindReal L U c d i .IsDedekindReal.lower-rounded =
  isPropΠ2 (λ _ _ → squash₁)
    (c .IsDedekindReal.lower-rounded) (d .IsDedekindReal.lower-rounded) i
isPropIsDedekindReal L U c d i .IsDedekindReal.upper-rounded =
  isPropΠ2 (λ _ _ → squash₁)
    (c .IsDedekindReal.upper-rounded) (d .IsDedekindReal.upper-rounded) i
isPropIsDedekindReal L U c d i .IsDedekindReal.disjoint =
  isPropΠ3 (λ _ _ _ → Empty.isProp⊥)
    (c .IsDedekindReal.disjoint) (d .IsDedekindReal.disjoint) i
isPropIsDedekindReal L U c d i .IsDedekindReal.located =
  isPropΠ3 (λ _ _ _ → squash₁)
    (c .IsDedekindReal.located) (d .IsDedekindReal.located) i


DedekindRealPath :
  (x y : DedekindReal ℓ) →
  lower x ≡ lower y →
  upper x ≡ upper y →
  x ≡ y
DedekindRealPath x y lower-path upper-path i .lower = lower-path i
DedekindRealPath x y lower-path upper-path i .upper = upper-path i
DedekindRealPath x y lower-path upper-path i .isDedekindReal =
  isProp→PathP
    (λ i → isPropIsDedekindReal (lower-path i) (upper-path i))
    (isDedekindReal x) (isDedekindReal y) i


realExt :
  (x y : DedekindReal ℓ) →
  lower x ⊆ lower y →
  lower y ⊆ lower x →
  upper x ⊆ upper y →
  upper y ⊆ upper x →
  x ≡ y
realExt x y Lx⊆Ly Ly⊆Lx Ux⊆Uy Uy⊆Ux =
  DedekindRealPath x y
    (predExt (lower x) (lower y) Lx⊆Ly Ly⊆Lx)
    (predExt (upper x) (upper y) Ux⊆Uy Uy⊆Ux)


private
  RealΣ : (ℓ : Level) → Type (ℓ-suc ℓ)
  RealΣ ℓ = Σ[ L ∈ ℚPred ℓ ] Σ[ U ∈ ℚPred ℓ ] IsDedekindReal L U

  real→Σ : DedekindReal ℓ → RealΣ ℓ
  real→Σ x = lower x , upper x , isDedekindReal x

  Σ→real : RealΣ ℓ → DedekindReal ℓ
  Σ→real (L , U , real) = record
    { lower = L
    ; upper = U
    ; isDedekindReal = real
    }

  isSetRealΣ : isSet (RealΣ ℓ)
  isSetRealΣ =
    isOfHLevelΣ 2 isSetℚPred λ L →
    isOfHLevelΣ 2 isSetℚPred λ U →
    isProp→isSet (isPropIsDedekindReal L U)


isSetDedekindReal : isSet (DedekindReal ℓ)
isSetDedekindReal =
  isSetRetract real→Σ Σ→real
    (λ x → DedekindRealPath (Σ→real (real→Σ x)) x refl refl)
    isSetRealΣ
