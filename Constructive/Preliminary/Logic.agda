{-# OPTIONS --safe #-}
module Constructive.Preliminary.Logic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Nullary

private
  variable
    ℓ ℓ' ℓ'' : Level
    X : Type ℓ
    Y : Type ℓ'


¬map : (X → Y) → ¬ Y → ¬ X
¬map f ¬y x = ¬y (f x)

→¬¬ : X → ¬ ¬ X
→¬¬ x ¬x = ¬x x


∥Π∥→Π∥∥ : {Y : X → Type ℓ'}
  → ∥ ((x : X) → Y x) ∥₁ → (x : X) → ∥ Y x ∥₁
∥Π∥→Π∥∥ = Prop.rec (isPropΠ (λ _ → squash₁)) (λ sec → λ x → ∣ sec x ∣₁)

∥Π∥→Π∥∥2 : {Y : X → Type ℓ'}{Z : (x : X) → Y x → Type ℓ''}
  → ∥ ((x : X) → (y : Y x) → Z x y) ∥₁ → (x : X) → (y : Y x) → ∥ Z x y ∥₁
∥Π∥→Π∥∥2 = Prop.rec (isPropΠ2 (λ _ _ → squash₁)) (λ sec → λ x y → ∣ sec x y ∣₁)


¬Σ→∀¬ : {P : X → Type ℓ'} → ¬ (Σ[ x ∈ X ] P x) → (x : X) → ¬ P x
¬Σ→∀¬ f x p = f (x , p)

¬∃→∀¬ : {P : X → Type ℓ'} → ¬ ∥ Σ[ x ∈ X ] P x ∥₁ → (x : X) → ¬ P x
¬∃→∀¬ f = ¬Σ→∀¬ ((¬map ∣_∣₁) f)

¬Σ→∀¬2 : {Y : X → Type ℓ'}{Z : (x : X) → Y x → Type ℓ''}
  → ¬ (Σ[ x ∈ X ] Σ[ y ∈ Y x ] Z x y)
  → (x : X) → (y : Y x) → ¬ Z x y
¬Σ→∀¬2 f x = ¬Σ→∀¬ (¬Σ→∀¬ f x)

¬∃→∀¬2 : {Y : X → Type ℓ'}{Z : (x : X) → Y x → Type ℓ''}
  → ¬ ∥ Σ[ x ∈ X ] Σ[ y ∈ Y x ] Z x y ∥₁
  → (x : X) → (y : Y x) → ¬ Z x y
¬∃→∀¬2 f = ¬Σ→∀¬2 ((¬map ∣_∣₁) f)


takeOut∥Σ∥ : {P : X → Type ℓ'} → ∥ Σ[ x ∈ X ] ∥ P x ∥₁ ∥₁ → ∥ Σ[ x ∈ X ] P x ∥₁
takeOut∥Σ∥ h = do (x , ∥p∥) ← h ; p ← ∥p∥ ; return (x , p)
