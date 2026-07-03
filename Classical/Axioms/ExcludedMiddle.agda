{-

Law of Excluded Middle

-}
{-# OPTIONS --safe #-}
module Classical.Axioms.ExcludedMiddle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Bool
open import Cubical.Data.Bool.Properties
  using (isPropBool→Type; isPropBool→Type*; Dec≃DecBool; Dec≃DecBool*)
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidablePropositions
  using (DecProp)

open import Classical.Axioms.Resizing

private
  variable
    ℓ : Level


-- Binary operation for being inequal

_≢_ : {X : Type ℓ}(x y : X) → Type ℓ
x ≢ y = ¬ x ≡ y

isProp≢ : {X : Type ℓ}{x y : X} → isProp (x ≢ y)
isProp≢ = isProp¬ _


-- Law of Excluded Middle and Double Negation Elimination
-- (abbreviated as LEM and DNE respectively)

-- The "per universe" version

LEMOfLevel : (ℓ : Level) → Type (ℓ-suc ℓ)
LEMOfLevel ℓ = {P : Type ℓ} → isProp P → Dec P

DNEOfLevel : (ℓ : Level) → Type (ℓ-suc ℓ)
DNEOfLevel ℓ = {P : Type ℓ} → isProp P → ¬ ¬ P → P

isPropLEMOfLevel : isProp (LEMOfLevel ℓ)
isPropLEMOfLevel = isPropImplicitΠ (λ _ → isPropΠ isPropDec)

isPropDNEOfLevel : isProp (DNEOfLevel ℓ)
isPropDNEOfLevel = isPropImplicitΠ (λ _ → isPropΠ2 (λ p _ → p))


-- Equivalence between these two axioms

LEMOfLevel→DNEOfLevel : LEMOfLevel ℓ → DNEOfLevel ℓ
LEMOfLevel→DNEOfLevel decide isPropP ¬¬p with decide isPropP
... | yes p = p
... | no ¬p = Empty.rec (¬¬p ¬p)

DNEOfLevel→LEMOfLevel : DNEOfLevel ℓ → LEMOfLevel ℓ
DNEOfLevel→LEMOfLevel elim¬¬ {P = P} isPropP = elim¬¬ (isPropDec isPropP) ¬¬dec
  where
  ¬¬dec : ¬ ¬ Dec P
  ¬¬dec ¬dec = ¬dec (yes (elim¬¬ isPropP λ ¬p → ¬dec (no ¬p)))


-- The universal polymorphic or "global" version

LEM : Typeω
LEM = {ℓ : Level} → LEMOfLevel ℓ

DNE : Typeω
DNE = {ℓ : Level} → DNEOfLevel ℓ

LEM→DNE : LEM → DNE
LEM→DNE p = LEMOfLevel→DNEOfLevel p

DNE→LEM : DNE → LEM
DNE→LEM p = DNEOfLevel→LEMOfLevel p


{-

  Some corollarie of LEM

-}

open Iso

module _ (decide : LEM) where

  -- Under LEM, all propositions are decidable,
  -- and more precisely,
  -- the type of propositions is equivalent to the type of decidable propositions
  -- (of a given universe level ℓ).

  hProp→DecProp : hProp ℓ → DecProp ℓ
  hProp→DecProp P = P , decide (P .snd)

  DecProp→hProp : DecProp ℓ → hProp ℓ
  DecProp→hProp = fst

  DecProp→hProp→DecProp : (P : DecProp ℓ) → hProp→DecProp (DecProp→hProp P) ≡ P
  DecProp→hProp→DecProp P i .fst = P .fst
  DecProp→hProp→DecProp P i .snd =
    isProp→PathP (λ i → isPropDec (P .fst .snd)) (decide (P .fst .snd)) (P .snd) i

  hProp→DecProp→hProp : (P : hProp ℓ) → DecProp→hProp (hProp→DecProp P) ≡ P
  hProp→DecProp→hProp P = refl

  Iso-hProp-DecProp : Iso (hProp ℓ) (DecProp ℓ)
  Iso-hProp-DecProp = iso hProp→DecProp DecProp→hProp DecProp→hProp→DecProp hProp→DecProp→hProp

  hProp≃DecProp : hProp ℓ ≃ DecProp ℓ
  hProp≃DecProp = isoToEquiv Iso-hProp-DecProp


  -- The type Prop is a subobject classifier

  Bool→hProp : Bool → hProp ℓ
  Bool→hProp b = Bool→Type* b , isPropBool→Type*

  hProp→Bool : hProp ℓ → Bool
  hProp→Bool P = Dec→Bool (decide (P .snd))

  hProp→Bool→hProp : (P : hProp ℓ) → Bool→hProp (hProp→Bool P) ≡ P
  hProp→Bool→hProp (P , h) i .fst = ua (invEquiv (Dec≃DecBool* h (decide h))) i
  hProp→Bool→hProp (P , h) i .snd =
    isProp→PathP (λ i → isPropIsProp {A = hProp→Bool→hProp (P , h) i .fst})
      isPropBool→Type* h i

  Bool→hProp→Bool : ∀ {ℓ} (b : Bool) → hProp→Bool (Bool→hProp {ℓ = ℓ} b) ≡ b
  Bool→hProp→Bool {ℓ = ℓ} true with decide (isPropBool→Type* {ℓ = ℓ} {a = true})
  ... | yes _ = refl
  ... | no ¬p = Empty.rec (¬p tt*)
  Bool→hProp→Bool {ℓ = ℓ} false with decide (isPropBool→Type* {ℓ = ℓ} {a = false})
  ... | yes p = Empty.rec* p
  ... | no _ = refl

  Iso-Bool-hProp : Iso Bool (hProp ℓ)
  Iso-Bool-hProp = iso Bool→hProp hProp→Bool hProp→Bool→hProp Bool→hProp→Bool

  Bool≃hProp : Bool ≃ hProp ℓ
  Bool≃hProp = isoToEquiv Iso-Bool-hProp

  isSubobjectClassifierBool : isSubobjectClassifier Bool
  isSubobjectClassifierBool = getSubobjectClassifier Bool≃hProp


-- Law of Excluded Middle implies Propositional Resizing

open DropProp

LEM→Drop : LEM → Drop
LEM→Drop decide (P , h) .lower = Bool→Type (Dec→Bool (decide h)) , isPropBool→Type
LEM→Drop decide (P , h) .dropEquiv = Dec≃DecBool h (decide h)

LEM→Resizing : LEM → Resizing
LEM→Resizing decide = Drop→Resizing (LEM→Drop decide)
