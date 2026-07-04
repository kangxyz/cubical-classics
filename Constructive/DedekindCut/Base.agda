{-

Constructive Dedekind cuts over the rationals.

This module contains the basic definition of Dedekind cuts.  The lower and
upper cuts are level-polymorphic predicate-valued maps into hProp, so using
the definition does not require LEM or propositional resizing.

-}
{-# OPTIONS --safe #-}
module Constructive.DedekindCut.Base where

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


record IsDedekindCut (L U : ℚPred ℓ) : Type ℓ where
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


record DedekindCut (ℓ : Level) : Type (ℓ-suc ℓ) where
  no-eta-equality

  field
    lower : ℚPred ℓ
    upper : ℚPred ℓ
    isDedekindCut : IsDedekindCut lower upper

  open IsDedekindCut isDedekindCut public


open DedekindCut public


isPropIsDedekindCut : (L U : ℚPred ℓ) → isProp (IsDedekindCut L U)
isPropIsDedekindCut L U c d i .IsDedekindCut.lower-inhabited =
  squash₁ (c .IsDedekindCut.lower-inhabited) (d .IsDedekindCut.lower-inhabited) i
isPropIsDedekindCut L U c d i .IsDedekindCut.upper-inhabited =
  squash₁ (c .IsDedekindCut.upper-inhabited) (d .IsDedekindCut.upper-inhabited) i
isPropIsDedekindCut L U c d i .IsDedekindCut.lower-closed =
  isPropΠ4 (λ p _ _ _ → isProp∈ L p)
    (c .IsDedekindCut.lower-closed) (d .IsDedekindCut.lower-closed) i
isPropIsDedekindCut L U c d i .IsDedekindCut.upper-closed =
  isPropΠ4 (λ _ q _ _ → isProp∈ U q)
    (c .IsDedekindCut.upper-closed) (d .IsDedekindCut.upper-closed) i
isPropIsDedekindCut L U c d i .IsDedekindCut.lower-rounded =
  isPropΠ2 (λ _ _ → squash₁)
    (c .IsDedekindCut.lower-rounded) (d .IsDedekindCut.lower-rounded) i
isPropIsDedekindCut L U c d i .IsDedekindCut.upper-rounded =
  isPropΠ2 (λ _ _ → squash₁)
    (c .IsDedekindCut.upper-rounded) (d .IsDedekindCut.upper-rounded) i
isPropIsDedekindCut L U c d i .IsDedekindCut.disjoint =
  isPropΠ3 (λ _ _ _ → Empty.isProp⊥)
    (c .IsDedekindCut.disjoint) (d .IsDedekindCut.disjoint) i
isPropIsDedekindCut L U c d i .IsDedekindCut.located =
  isPropΠ3 (λ _ _ _ → squash₁)
    (c .IsDedekindCut.located) (d .IsDedekindCut.located) i


DedekindCutPath :
  (x y : DedekindCut ℓ) →
  lower x ≡ lower y →
  upper x ≡ upper y →
  x ≡ y
DedekindCutPath x y lower-path upper-path i .lower = lower-path i
DedekindCutPath x y lower-path upper-path i .upper = upper-path i
DedekindCutPath x y lower-path upper-path i .isDedekindCut =
  isProp→PathP
    (λ i → isPropIsDedekindCut (lower-path i) (upper-path i))
    (isDedekindCut x) (isDedekindCut y) i


cutExt :
  (x y : DedekindCut ℓ) →
  lower x ⊆ lower y →
  lower y ⊆ lower x →
  upper x ⊆ upper y →
  upper y ⊆ upper x →
  x ≡ y
cutExt x y Lx⊆Ly Ly⊆Lx Ux⊆Uy Uy⊆Ux =
  DedekindCutPath x y
    (predExt (lower x) (lower y) Lx⊆Ly Ly⊆Lx)
    (predExt (upper x) (upper y) Ux⊆Uy Uy⊆Ux)


private
  CutΣ : (ℓ : Level) → Type (ℓ-suc ℓ)
  CutΣ ℓ = Σ[ L ∈ ℚPred ℓ ] Σ[ U ∈ ℚPred ℓ ] IsDedekindCut L U

  cut→Σ : DedekindCut ℓ → CutΣ ℓ
  cut→Σ x = lower x , upper x , isDedekindCut x

  Σ→cut : CutΣ ℓ → DedekindCut ℓ
  Σ→cut (L , U , cut) = record
    { lower = L
    ; upper = U
    ; isDedekindCut = cut
    }

  isSetCutΣ : isSet (CutΣ ℓ)
  isSetCutΣ =
    isOfHLevelΣ 2 isSetℚPred λ L →
    isOfHLevelΣ 2 isSetℚPred λ U →
    isProp→isSet (isPropIsDedekindCut L U)


isSetDedekindCut : isSet (DedekindCut ℓ)
isSetDedekindCut =
  isSetRetract cut→Σ Σ→cut
    (λ x → DedekindCutPath (Σ→cut (cut→Σ x)) x refl refl)
    isSetCutΣ
