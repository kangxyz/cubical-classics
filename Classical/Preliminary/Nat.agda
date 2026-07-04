{-# OPTIONS --safe #-}
module Classical.Preliminary.Nat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Nullary
open import Constructive.Preliminary.Nat public

private
  variable
    ℓ : Level


open import Classical.Axioms

module _ ⦃ 🤖 : Oracle ⦄  where

  open Oracle 🤖

  findByOracle :
    {P : ℕ → Type ℓ}
    (isPropP : (n : ℕ) → isProp (P n))
    → ∥ Σ[ n ∈ ℕ ] P n ∥₁ → Σ[ n ∈ ℕ ] P n
  findByOracle isPropP = find (λ n → decide (isPropP n))


module LimitedOmniscience ⦃ 🤖 : Oracle ⦄  where

  open import Cubical.Axiom.Omniscience using () renaming (LPO to CubicalLPO)
  open import Cubical.Data.Bool using (Bool; Bool→Type; Dec→Bool)
  open import Cubical.Data.Bool.Properties using (Dec→DecBool; DecBool→Dec)
  open import Classical.Preliminary.Logic

  open Oracle 🤖

  CubicalLPOℕ : CubicalLPO ℕ
  CubicalLPOℕ P with decide (isPropΠ (λ n → isProp¬ (Bool→Type (P n))))
  ... | yes ∀¬p = inl ∀¬p
  ... | no ¬∀¬p = inr (¬∀¬→∃ ¬∀¬p)

  module _
    {P : ℕ → Type ℓ}
    (isPropP : (n : ℕ) → isProp (P n)) where

    decP : (n : ℕ) → Dec (P n)
    decP n = decide (isPropP n)

    boolP : ℕ → Bool
    boolP n = Dec→Bool (decP n)

    ∥LPO∥ : ∥ Σ[ n ∈ ℕ ] P n ∥₁ ⊎ ((n : ℕ) → ¬ P n)
    ∥LPO∥ with CubicalLPOℕ boolP
    ... | inl ∀¬p = inr (λ n p → ∀¬p n (Dec→DecBool (decP n) p))
    ... | inr ∃p = inl (do
      (n , p) ← ∃p
      return (n , DecBool→Dec (decP n) p))

    LPO : (Σ[ n ∈ ℕ ] P n) ⊎ ((n : ℕ) → ¬ P n)
    LPO with ∥LPO∥
    ... | inl  ∃p = inl (findByOracle isPropP ∃p)
    ... | inr ∀¬p = inr ∀¬p
