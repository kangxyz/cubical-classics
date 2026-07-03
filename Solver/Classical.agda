open import Classical.Axioms
open import Classical.Axioms.Resizing
module Solver.Classical (decide : LEM) where
open import Solver.Formula
open Models

open import Classical.Preliminary.DecidablePropositions

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_∘_; const)
open import Cubical.Data.Nat.Base
open import Cubical.Data.Fin.Base using (Fin; fzero; fsuc)
open import Cubical.Data.Bool

private variable
  n : ℕ

computeProp : {n : ℕ} (F : Formula (Fin n))
  → {Bool→Type (binFoldBool {n = n} (λ section → section ⊨ F))}
  → (P : FinVec (hProp ℓ-zero) n)
  → (fst ∘ P) ⊢ F
computeProp {n = n} F {witness} P =
  computeDec {n = n} F {witness} (hProp→DecProp decide ∘ P)

-- Evil syntax
infixr -1 _⅋_
_⅋_ = _∷_
infixl 0 _⟧
_⟧ : ∀ {ℓ}{A : Type ℓ} → A → FinVec A 1
v ⟧ = v ∷ []
infix -2 Solve_⟦_
Solve_⟦_ = computeProp

private module test (P Q R : Type) (pP : isProp P) (pQ : isProp Q) (pR : isProp R) where
  open import Cubical.Data.Sigma
    using (_×_)
  open import Cubical.Data.Sum
    using (_⊎_)
  open import Cubical.HITs.PropositionalTruncation
    using (∥_∥₁)
  open import Cubical.Relation.Nullary.Base
    using (¬_)

  _↔_ : Type → Type → Type
  P ↔ Q = (P → Q) × (Q → P)

  infix 0 _∥⊎∥_
  _∥⊎∥_ : Type → Type → Type
  P ∥⊎∥ Q = ∥ P ⊎ Q ∥₁

  F0 F1 F2 : Formula (Fin 3)
  F0 = fzero ᶠ
  F1 = fsuc fzero ᶠ
  F2 = fsuc (fsuc fzero) ᶠ

  testFormula : Formula (Fin 3)
  testFormula = (F0 ∧ᶠ F1 →ᶠ F2) ↔ᶠ (F0 →ᶠ ¬ᶠ F1 ∨ᶠ F2)

  testContext : FinVec (hProp ℓ-zero) 3
  testContext = (P , pP) ∷ (Q , pQ) ∷ (R , pR) ∷ []

  test : (P × Q → R) ↔ (P → ¬ Q ∥⊎∥ R)
  test = computeProp {n = 3} testFormula testContext
