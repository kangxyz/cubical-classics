{-

Constructive predicative powersets

This module follows the powerset interface in the Cubical library, but keeps
the universe level of predicates explicit.

-}
{-# OPTIONS --safe #-}
module Constructive.Foundations.Powerset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (hPropExt)
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓᴸ ℓᵁ ℓᴾ ℓˢ : Level
    X : Type ℓ


Pred : Type ℓ → (ℓᴾ : Level) → Type (ℓ-max ℓ (ℓ-suc ℓᴾ))
Pred X ℓᴾ = X → hProp ℓᴾ


isSetPred : {ℓ ℓᴾ : Level} {X : Type ℓ} → isSet (Pred X ℓᴾ)
isSetPred = isSetΠ λ _ → isSetHProp


_∈_ : {ℓ ℓᴾ : Level} {X : Type ℓ} → X → Pred X ℓᴾ → Type ℓᴾ
x ∈ A = A x .fst

infix 4 _∈_


isProp∈ : (A : Pred X ℓᴾ) → (x : X) → isProp (x ∈ A)
isProp∈ A x = A x .snd


_⊆_ :
  {ℓ ℓᴸ ℓᵁ : Level} {X : Type ℓ} →
  Pred X ℓᴸ →
  Pred X ℓᵁ →
  Type (ℓ-max ℓ (ℓ-max ℓᴸ ℓᵁ))
_⊆_ {X = X} A B = (x : X) → x ∈ A → x ∈ B

infix 4 _⊆_


isProp⊆ : (A : Pred X ℓᴸ) (B : Pred X ℓᵁ) → isProp (A ⊆ B)
isProp⊆ A B = isPropΠ2 λ x _ → isProp∈ B x


⊆-refl :
  {ℓ ℓᴾ : Level} {X : Type ℓ} →
  (A : Pred X ℓᴾ) →
  A ⊆ A
⊆-refl A x x∈A = x∈A


⊆-trans :
  {ℓ ℓᴸ ℓᵁ ℓˢ : Level} {X : Type ℓ} →
  (A : Pred X ℓᴸ) (B : Pred X ℓᵁ) (C : Pred X ℓˢ) →
  A ⊆ B →
  B ⊆ C →
  A ⊆ C
⊆-trans A B C A⊆B B⊆C x x∈A = B⊆C x (A⊆B x x∈A)


∈⊆-trans :
  {ℓ ℓᴸ ℓᵁ : Level} {X : Type ℓ} →
  {A : Pred X ℓᴸ} {B : Pred X ℓᵁ} {x : X} →
  x ∈ A →
  A ⊆ B →
  x ∈ B
∈⊆-trans x∈A A⊆B = A⊆B _ x∈A


subst-∈ :
  {ℓ ℓᴾ : Level} {X : Type ℓ} →
  (A : Pred X ℓᴾ) {x y : X} →
  x ≡ y →
  x ∈ A →
  y ∈ A
subst-∈ A = subst (_∈ A)


_⇔ᵖ_ :
  {ℓ ℓᴸ ℓᵁ : Level} {X : Type ℓ} →
  Pred X ℓᴸ →
  Pred X ℓᵁ →
  Type (ℓ-max ℓ (ℓ-max ℓᴸ ℓᵁ))
_⇔ᵖ_ {X = X} A B = (x : X) → (x ∈ A → x ∈ B) × (x ∈ B → x ∈ A)

infix 3 _⇔ᵖ_


isProp⇔ᵖ :
  {ℓ ℓᴸ ℓᵁ : Level} {X : Type ℓ} →
  (A : Pred X ℓᴸ) →
  (B : Pred X ℓᵁ) →
  isProp (A ⇔ᵖ B)
isProp⇔ᵖ A B =
  isPropΠ λ x →
    isProp×
      (isPropΠ λ _ → isProp∈ B x)
      (isPropΠ λ _ → isProp∈ A x)


predExt : (A B : Pred X ℓᴾ) → A ⊆ B → B ⊆ A → A ≡ B
predExt A B A⊆B B⊆A =
  funExt λ x →
    TypeOfHLevel≡ 1
      (hPropExt (isProp∈ A x) (isProp∈ B x) (A⊆B x) (B⊆A x))
