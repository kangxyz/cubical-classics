{-# OPTIONS --safe #-}
module Solvers.Bool where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Bool.Properties
  using (Bool→Type×; Bool→Type×'; Bool→Type⊎; Bool→Type⊎'; false≢true; true≢false)
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Fin.Base using (Fin; fzero; fsuc)
open import Cubical.Data.Nat.Base using (ℕ; suc)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (tt)

open import Solvers.Formula
  using (FinVec; []; _∷_; binFoldBool; binFoldCorrect)

private variable
  n : ℕ

infixr 35 ¬ᵇ_
infixl 34 _∧ᵇ_ _∨ᵇ_
infix 36 _≡ᵖ_ _≡ᵖtrue _≡ᵖfalse
infixl 34 _∧ᵖ_ _∨ᵖ_
infixr 33 _→ᵖ_

data Expr (n : ℕ) : Type where
  var : Fin n → Expr n
  trueᵇ falseᵇ : Expr n
  ¬ᵇ_ : Expr n → Expr n
  _∧ᵇ_ _∨ᵇ_ : Expr n → Expr n → Expr n

eval : FinVec Bool n → Expr n → Bool
eval Γ (var x) = Γ x
eval Γ trueᵇ = true
eval Γ falseᵇ = false
eval Γ (¬ᵇ e) = not (eval Γ e)
eval Γ (e ∧ᵇ f) = eval Γ e and eval Γ f
eval Γ (e ∨ᵇ f) = eval Γ e or eval Γ f

infix 32 _≟ᵇ_
_≟ᵇ_ : Bool → Bool → Bool
x ≟ᵇ y = not (x ⊕ y)

≟ᵇ→≡ : (x y : Bool) → Bool→Type (x ≟ᵇ y) → x ≡ y
≟ᵇ→≡ false false _ = refl
≟ᵇ→≡ false true ()
≟ᵇ→≡ true false ()
≟ᵇ→≡ true true _ = refl

≡→≟ᵇ : (x y : Bool) → x ≡ y → Bool→Type (x ≟ᵇ y)
≡→≟ᵇ false false _ = tt
≡→≟ᵇ false true p = Empty.rec (false≢true p)
≡→≟ᵇ true false p = Empty.rec (true≢false p)
≡→≟ᵇ true true _ = tt

Bool→Type→≡true : (x : Bool) → Bool→Type x → x ≡ true
Bool→Type→≡true true _ = refl
Bool→Type→≡true false ()

Bool→Type→≡false : (x : Bool) → Bool→Type (not x) → x ≡ false
Bool→Type→≡false true ()
Bool→Type→≡false false _ = refl

≡true→Bool→Type : (x : Bool) → x ≡ true → Bool→Type x
≡true→Bool→Type true _ = tt
≡true→Bool→Type false p = Empty.rec (false≢true p)

≡false→Bool→Type : (x : Bool) → x ≡ false → Bool→Type (not x)
≡false→Bool→Type true p = Empty.rec (true≢false p)
≡false→Bool→Type false _ = tt

solve : (e f : Expr n)
  → {Bool→Type (binFoldBool {n = n} (λ Γ → eval Γ e ≟ᵇ eval Γ f))}
  → (Γ : FinVec Bool n)
  → eval Γ e ≡ eval Γ f
solve {n = n} e f {witness} Γ =
  ≟ᵇ→≡ (eval Γ e) (eval Γ f)
    (binFoldCorrect {n = n} Γ (λ Γ → eval Γ e ≟ᵇ eval Γ f) witness)

v0 : Expr (suc n)
v0 = var fzero

v1 : Expr (suc (suc n))
v1 = var (fsuc fzero)

v2 : Expr (suc (suc (suc n)))
v2 = var (fsuc (fsuc fzero))

v3 : Expr (suc (suc (suc (suc n))))
v3 = var (fsuc (fsuc (fsuc fzero)))

solve₁ : (e f : Expr 1)
  → {Bool→Type (binFoldBool {n = 1} (λ Γ → eval Γ e ≟ᵇ eval Γ f))}
  → (x : Bool)
  → eval (x ∷ []) e ≡ eval (x ∷ []) f
solve₁ e f {witness} x = solve {n = 1} e f {witness} (x ∷ [])

solve₂ : (e f : Expr 2)
  → {Bool→Type (binFoldBool {n = 2} (λ Γ → eval Γ e ≟ᵇ eval Γ f))}
  → (x y : Bool)
  → eval (x ∷ y ∷ []) e ≡ eval (x ∷ y ∷ []) f
solve₂ e f {witness} x y = solve {n = 2} e f {witness} (x ∷ y ∷ [])

solve₃ : (e f : Expr 3)
  → {Bool→Type (binFoldBool {n = 3} (λ Γ → eval Γ e ≟ᵇ eval Γ f))}
  → (x y z : Bool)
  → eval (x ∷ y ∷ z ∷ []) e ≡ eval (x ∷ y ∷ z ∷ []) f
solve₃ e f {witness} x y z = solve {n = 3} e f {witness} (x ∷ y ∷ z ∷ [])

solve₄ : (e f : Expr 4)
  → {Bool→Type (binFoldBool {n = 4} (λ Γ → eval Γ e ≟ᵇ eval Γ f))}
  → (w x y z : Bool)
  → eval (w ∷ x ∷ y ∷ z ∷ []) e ≡ eval (w ∷ x ∷ y ∷ z ∷ []) f
solve₄ e f {witness} w x y z = solve {n = 4} e f {witness} (w ∷ x ∷ y ∷ z ∷ [])

data Claim (n : ℕ) : Type where
  ⊥ᵖ : Claim n
  _≡ᵖ_ : Expr n → Expr n → Claim n
  _≡ᵖtrue _≡ᵖfalse : Expr n → Claim n
  _∧ᵖ_ _∨ᵖ_ _→ᵖ_ : Claim n → Claim n → Claim n

interp : FinVec Bool n → Claim n → Type
interp Γ ⊥ᵖ = ⊥
interp Γ (e ≡ᵖ f) = eval Γ e ≡ eval Γ f
interp Γ (e ≡ᵖtrue) = eval Γ e ≡ true
interp Γ (e ≡ᵖfalse) = eval Γ e ≡ false
interp Γ (P ∧ᵖ Q) = interp Γ P × interp Γ Q
interp Γ (P ∨ᵖ Q) = interp Γ P ⊎ interp Γ Q
interp Γ (P →ᵖ Q) = interp Γ P → interp Γ Q

truth : FinVec Bool n → Claim n → Bool
truth Γ ⊥ᵖ = false
truth Γ (e ≡ᵖ f) = eval Γ e ≟ᵇ eval Γ f
truth Γ (e ≡ᵖtrue) = eval Γ e
truth Γ (e ≡ᵖfalse) = not (eval Γ e)
truth Γ (P ∧ᵖ Q) = truth Γ P and truth Γ Q
truth Γ (P ∨ᵖ Q) = truth Γ P or truth Γ Q
truth Γ (P →ᵖ Q) = not (truth Γ P) or truth Γ Q

abstract
  Sound : (Γ : FinVec Bool n) (P : Claim n)
    → Bool→Type (truth Γ P)
    → interp Γ P
  Complete : (Γ : FinVec Bool n) (P : Claim n)
    → interp Γ P
    → Bool→Type (truth Γ P)

  Sound Γ ⊥ᵖ ()
  Sound Γ (e ≡ᵖ f) t = ≟ᵇ→≡ (eval Γ e) (eval Γ f) t
  Sound Γ (e ≡ᵖtrue) t = Bool→Type→≡true (eval Γ e) t
  Sound Γ (e ≡ᵖfalse) t = Bool→Type→≡false (eval Γ e) t
  Sound Γ (P ∧ᵖ Q) t =
    Sound Γ P (fst (Bool→Type× (truth Γ P) (truth Γ Q) t)) ,
    Sound Γ Q (snd (Bool→Type× (truth Γ P) (truth Γ Q) t))
  Sound Γ (P ∨ᵖ Q) t with Bool→Type⊎ (truth Γ P) (truth Γ Q) t
  ... | inl p = inl (Sound Γ P p)
  ... | inr q = inr (Sound Γ Q q)
  Sound Γ (P →ᵖ Q) t p with truth Γ P | truth Γ Q | Complete Γ P | Sound Γ Q
  ... | false | false | pᶜ | qˢ = qˢ (pᶜ p)
  ... | false | true  | pᶜ | qˢ = qˢ tt
  ... | true  | false | pᶜ | qˢ = Empty.rec t
  ... | true  | true  | pᶜ | qˢ = qˢ tt

  Complete Γ ⊥ᵖ p = p
  Complete Γ (e ≡ᵖ f) p = ≡→≟ᵇ (eval Γ e) (eval Γ f) p
  Complete Γ (e ≡ᵖtrue) p = ≡true→Bool→Type (eval Γ e) p
  Complete Γ (e ≡ᵖfalse) p = ≡false→Bool→Type (eval Γ e) p
  Complete Γ (P ∧ᵖ Q) (p , q) =
    Bool→Type×' (truth Γ P) (truth Γ Q) (Complete Γ P p , Complete Γ Q q)
  Complete Γ (P ∨ᵖ Q) (inl p) =
    Bool→Type⊎' (truth Γ P) (truth Γ Q) (inl (Complete Γ P p))
  Complete Γ (P ∨ᵖ Q) (inr q) =
    Bool→Type⊎' (truth Γ P) (truth Γ Q) (inr (Complete Γ Q q))
  Complete Γ (P →ᵖ Q) f with truth Γ P | truth Γ Q | Sound Γ P | Complete Γ Q
  ... | false | false | pˢ | qᶜ = tt
  ... | false | true  | pˢ | qᶜ = tt
  ... | true  | false | pˢ | qᶜ = qᶜ (f (pˢ tt))
  ... | true  | true  | pˢ | qᶜ = tt

solveᵖ : (P : Claim n)
  → {Bool→Type (binFoldBool {n = n} (λ Γ → truth Γ P))}
  → (Γ : FinVec Bool n)
  → interp Γ P
solveᵖ {n = n} P {witness} Γ =
  Sound Γ P (binFoldCorrect {n = n} Γ (λ Γ → truth Γ P) witness)

solveᵖ₁ : (P : Claim 1)
  → {Bool→Type (binFoldBool {n = 1} (λ Γ → truth Γ P))}
  → (x : Bool)
  → interp (x ∷ []) P
solveᵖ₁ P {witness} x = solveᵖ {n = 1} P {witness} (x ∷ [])

solveᵖ₂ : (P : Claim 2)
  → {Bool→Type (binFoldBool {n = 2} (λ Γ → truth Γ P))}
  → (x y : Bool)
  → interp (x ∷ y ∷ []) P
solveᵖ₂ P {witness} x y = solveᵖ {n = 2} P {witness} (x ∷ y ∷ [])

solveᵖ₃ : (P : Claim 3)
  → {Bool→Type (binFoldBool {n = 3} (λ Γ → truth Γ P))}
  → (x y z : Bool)
  → interp (x ∷ y ∷ z ∷ []) P
solveᵖ₃ P {witness} x y z = solveᵖ {n = 3} P {witness} (x ∷ y ∷ z ∷ [])

solveᵖ₄ : (P : Claim 4)
  → {Bool→Type (binFoldBool {n = 4} (λ Γ → truth Γ P))}
  → (w x y z : Bool)
  → interp (w ∷ x ∷ y ∷ z ∷ []) P
solveᵖ₄ P {witness} w x y z = solveᵖ {n = 4} P {witness} (w ∷ x ∷ y ∷ z ∷ [])
