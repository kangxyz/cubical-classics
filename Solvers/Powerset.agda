{-# OPTIONS --safe #-}
module Solvers.Powerset where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Fin.Base using (Fin; fzero; fsuc)
open import Cubical.Data.Nat.Base using (ℕ; suc)

open import Classical.Axioms
open import Classical.Foundations.Powerset.Base
open import Solvers.Formula
  using (FinVec; []; _∷_; binFoldBool)
import Solvers.Bool as BoolSolver

private variable
  n : ℕ

infixr 10 ∁ᵖ_
infixr 9 _∩ᵖ_
infixr 8 _∪ᵖ_

data Expr (n : ℕ) : Type where
  pvar : Fin n → Expr n
  ∅ᵖ totalᵖ : Expr n
  ∁ᵖ_ : Expr n → Expr n
  _∪ᵖ_ _∩ᵖ_ : Expr n → Expr n → Expr n

toBool : Expr n → BoolSolver.Expr n
toBool (pvar x) = BoolSolver.var x
toBool ∅ᵖ = BoolSolver.falseᵇ
toBool totalᵖ = BoolSolver.trueᵇ
toBool (∁ᵖ e) = BoolSolver.¬ᵇ toBool e
toBool (e ∪ᵖ f) = toBool e BoolSolver.∨ᵇ toBool f
toBool (e ∩ᵖ f) = toBool e BoolSolver.∧ᵇ toBool f

p0 : Expr (suc n)
p0 = pvar fzero

p1 : Expr (suc (suc n))
p1 = pvar (fsuc fzero)

p2 : Expr (suc (suc (suc n)))
p2 = pvar (fsuc (fsuc fzero))

p3 : Expr (suc (suc (suc (suc n))))
p3 = pvar (fsuc (fsuc (fsuc fzero)))

module _ ⦃ 🤖 : Oracle ⦄ where

  private variable
    ℓ : Level
    X : Type ℓ

  eval : FinVec (ℙ X) n → Expr n → ℙ X
  eval Γ e x = BoolSolver.eval (λ k → Γ k x) (toBool e)

  solveℙ : (e f : Expr n)
    → {Bool→Type (binFoldBool {n = n}
        (λ Γ → BoolSolver._≟ᵇ_ (BoolSolver.eval Γ (toBool e)) (BoolSolver.eval Γ (toBool f))))}
    → (Γ : FinVec (ℙ X) n)
    → eval Γ e ≡ eval Γ f
  solveℙ {n = n} e f {witness} Γ i x =
    BoolSolver.solve {n = n} (toBool e) (toBool f) {witness} (λ k → Γ k x) i

  solveℙ₁ : (e f : Expr 1)
    → {Bool→Type (binFoldBool {n = 1}
        (λ Γ → BoolSolver._≟ᵇ_ (BoolSolver.eval Γ (toBool e)) (BoolSolver.eval Γ (toBool f))))}
    → (A : ℙ X)
    → eval (A ∷ []) e ≡ eval (A ∷ []) f
  solveℙ₁ e f {witness} A = solveℙ {n = 1} e f {witness} (A ∷ [])

  solveℙ₂ : (e f : Expr 2)
    → {Bool→Type (binFoldBool {n = 2}
        (λ Γ → BoolSolver._≟ᵇ_ (BoolSolver.eval Γ (toBool e)) (BoolSolver.eval Γ (toBool f))))}
    → (A B : ℙ X)
    → eval (A ∷ B ∷ []) e ≡ eval (A ∷ B ∷ []) f
  solveℙ₂ e f {witness} A B = solveℙ {n = 2} e f {witness} (A ∷ B ∷ [])

  solveℙ₃ : (e f : Expr 3)
    → {Bool→Type (binFoldBool {n = 3}
        (λ Γ → BoolSolver._≟ᵇ_ (BoolSolver.eval Γ (toBool e)) (BoolSolver.eval Γ (toBool f))))}
    → (A B C : ℙ X)
    → eval (A ∷ B ∷ C ∷ []) e ≡ eval (A ∷ B ∷ C ∷ []) f
  solveℙ₃ e f {witness} A B C = solveℙ {n = 3} e f {witness} (A ∷ B ∷ C ∷ [])

  solveℙ₄ : (e f : Expr 4)
    → {Bool→Type (binFoldBool {n = 4}
        (λ Γ → BoolSolver._≟ᵇ_ (BoolSolver.eval Γ (toBool e)) (BoolSolver.eval Γ (toBool f))))}
    → (A B C D : ℙ X)
    → eval (A ∷ B ∷ C ∷ D ∷ []) e ≡ eval (A ∷ B ∷ C ∷ D ∷ []) f
  solveℙ₄ e f {witness} A B C D = solveℙ {n = 4} e f {witness} (A ∷ B ∷ C ∷ D ∷ [])
