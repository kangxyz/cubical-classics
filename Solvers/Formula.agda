{-# OPTIONS --safe --lossy-unification #-}
module Solvers.Formula where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isProp×; isPropΠ)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.Function using (_∘_; const)
open import Cubical.Data.Bool
open import Cubical.Data.Bool.Properties
  using (Bool→Type×; Dec≃DecBool)
open import Cubical.Data.Unit
open import Cubical.Data.Empty
  using (⊥*; isProp⊥*)
  renaming (rec to rec⊥)
open import Cubical.Data.Sigma
  using (_×_)
open import Cubical.Data.Sum
  using (_⊎_; inl; inr)
  renaming (rec to rec⊎; map to map⊎)
open import Cubical.HITs.PropositionalTruncation
  using (∥_∥₁; ∣_∣₁; squash₁; isPropPropTrunc)
  renaming (map to map∥∥)
open import Cubical.Relation.Nullary.Base
  using (Dec; yes; no; ¬_; Dec¬)
open import Cubical.Relation.Nullary.Properties
  using (isProp¬; Dec∥∥; Dec×)
open import Cubical.Relation.Nullary.DecidablePropositions
  using (DecProp)

private variable
  ℓ ℓ' : Level

module _ where -- Stuff that should be in other modules
  Dec⊎ : {P : Type ℓ} {Q : Type ℓ'}
    → Dec P → Dec Q → Dec (P ⊎ Q)
  Dec⊎ (yes p) _       = yes (inl p)
  Dec⊎ (no ¬p) (yes q) = yes (inr q)
  Dec⊎ (no ¬p) (no ¬q) = no (rec⊎ ¬p ¬q)

  -- We might try to do a DecΠ, but that's slightly more complicated.
  Dec→ : {P : Type ℓ} {Q : Type ℓ'}
    → Dec P → Dec Q → Dec (P → Q)
  Dec→ _       (yes q) = yes λ _ → q
  Dec→ (yes p) (no ¬q) = no λ z → ¬q (z p)
  Dec→ (no ¬p) (no ¬q) = yes λ p → rec⊥ (¬p p)

  Bool→Type∥⊎∥' : (a b : Bool) → ∥ Bool→Type a ⊎ Bool→Type b ∥₁ → Bool→Type (a or b)
  Bool→Type∥⊎∥' true  false ∣ _ ∣₁ = tt
  Bool→Type∥⊎∥' true  true  ∣ _ ∣₁ = tt
  Bool→Type∥⊎∥' false true  ∣ _ ∣₁ = tt
  Bool→Type∥⊎∥' false false ∣ inl () ∣₁
  Bool→Type∥⊎∥' false false ∣ inr () ∣₁
  Bool→Type∥⊎∥' a b (squash₁ r₁ r₂ i)
    = isPropBool→Type (Bool→Type∥⊎∥' a b r₁) (Bool→Type∥⊎∥' a b r₂) i

infixr 35 ¬ᶠ_
infixl 34 _∧ᶠ_ _∨ᶠ_
infixl 33 _↔ᶠ_
infixr 33 _→ᶠ_
infix 100 _ᶠ
data Formula (a : Type) : Type where
  _ᶠ : (ϕ : a) → Formula a
  ⊤ᶠ ⊥ᶠ : Formula a
  ¬ᶠ_ : (F : Formula a) → Formula a
  _∧ᶠ_ _∨ᶠ_ _→ᶠ_ _↔ᶠ_ : (F G : Formula a) → Formula a

module Models {a : Type} where
  infix 30 _⊢_
  _⊢_ : (a → Type ℓ) → Formula a → Type ℓ
  Γ ⊢ (ϕ ᶠ) = Γ ϕ
  Γ ⊢ ⊤ᶠ = Unit*
  Γ ⊢ ⊥ᶠ = ⊥*
  Γ ⊢ (¬ᶠ F) = ¬ Γ ⊢ F
  Γ ⊢ (F ∧ᶠ G) = Γ ⊢ F × Γ ⊢ G
  Γ ⊢ (F ∨ᶠ G) = ∥ Γ ⊢ F ⊎ Γ ⊢ G ∥₁
  Γ ⊢ (F →ᶠ G) = Γ ⊢ F → Γ ⊢ G
  Γ ⊢ (F ↔ᶠ G) = (Γ ⊢ F → Γ ⊢ G) × (Γ ⊢ G → Γ ⊢ F)

  isProp⊢ : {Γ : a → Type ℓ}
    → (∀ a → isProp (Γ a))
    → (F : Formula a) → isProp (Γ ⊢ F)
  isProp⊢ Γ (ϕ ᶠ) = Γ ϕ
  isProp⊢ Γ ⊤ᶠ = isPropUnit*
  isProp⊢ Γ ⊥ᶠ = isProp⊥*
  isProp⊢ Γ (¬ᶠ F) = isProp¬ _
  isProp⊢ Γ (F ∧ᶠ G) = isProp× (isProp⊢ Γ F) (isProp⊢ Γ G)
  isProp⊢ Γ (F ∨ᶠ G) = isPropPropTrunc
  isProp⊢ Γ (F →ᶠ G) = isPropΠ λ _ → isProp⊢ Γ G
  isProp⊢ Γ (F ↔ᶠ G) =
    isProp× (isPropΠ λ _ → isProp⊢ Γ G) (isPropΠ λ _ → isProp⊢ Γ F)

  Dec⊢ : {Γ : a → Type ℓ}
    → (∀ a → Dec (Γ a))
    → (F : Formula a) → Dec (Γ ⊢ F)
  Dec⊢ Γ (ϕ ᶠ) = Γ ϕ
  Dec⊢ Γ ⊤ᶠ = yes tt*
  Dec⊢ Γ ⊥ᶠ = no lower
  Dec⊢ Γ (¬ᶠ F) = Dec¬ (Dec⊢ Γ F)
  Dec⊢ Γ (F ∧ᶠ G) = Dec× (Dec⊢ Γ F) (Dec⊢ Γ G)
  Dec⊢ Γ (F ∨ᶠ G) = Dec∥∥ (Dec⊎ (Dec⊢ Γ F) (Dec⊢ Γ G))
  Dec⊢ Γ (F →ᶠ G) = Dec→ (Dec⊢ Γ F) (Dec⊢ Γ G)
  Dec⊢ Γ (F ↔ᶠ G) = Dec× (Dec→ (Dec⊢ Γ F) (Dec⊢ Γ G)) (Dec→ (Dec⊢ Γ G) (Dec⊢ Γ F))

  _⊨_ : (a → Bool) → Formula a → Bool
  Γ ⊨ (ϕ ᶠ) = Γ ϕ
  Γ ⊨ ⊤ᶠ = true
  Γ ⊨ ⊥ᶠ = false
  Γ ⊨ (¬ᶠ F) = not (Γ ⊨ F)
  Γ ⊨ (F ∧ᶠ G) = Γ ⊨ F and Γ ⊨ G
  Γ ⊨ (F ∨ᶠ G) = Γ ⊨ F or Γ ⊨ G
  Γ ⊨ (F →ᶠ G) = not (Γ ⊨ F) or (Γ ⊨ G)
  Γ ⊨ (F ↔ᶠ G) = not (Γ ⊨ F) ⊕ (Γ ⊨ G)
    -- A strange case where  (not p) ⊕ q = not (p ⊕ q)

  abstract  -- Since they are proved to be propositions, we don't need the details.
    Sound : (Γ : a → Bool) (F : Formula a)
      → Bool→Type (Γ ⊨ F) → (Bool→Type ∘ Γ) ⊢ F
    Complete : (Γ : a → Bool) (F : Formula a)
      → (Bool→Type ∘ Γ) ⊢ F → Bool→Type (Γ ⊨ F)

    Sound Γ (ϕ ᶠ) t = t
    Sound Γ ⊤ᶠ t = tt*
    Sound Γ (¬ᶠ F) t u with Γ ⊨ F | Complete Γ F u
    ... | false | ()
    Sound Γ (F ∧ᶠ G) t with Γ ⊨ F | Γ ⊨ G | Sound Γ F | Sound Γ G
    ... | true  | true  | f | g = f tt , g tt
    ... | false | false | _ | _ = Cubical.Data.Empty.rec t
      -- ^ This case is needed to hint Agda's case splitting system
    Sound Γ (F ∨ᶠ G) t with Γ ⊨ F | Γ ⊨ G | Sound Γ F | Sound Γ G
    ... | true | true | f | g = ∣ inl (f tt) ∣₁
    ... | false | true | f | g = ∣ inr (g tt) ∣₁
    ... | true | false | f | g = ∣ inl (f tt) ∣₁
    Sound Γ (F →ᶠ G) t u with Γ ⊨ F | Γ ⊨ G | Complete Γ F | Sound Γ G
    ... | false | false | f | g = g (f u)
    ... | false | true  | f | g = g tt
    ... | true  | true  | f | g = g tt
    Sound Γ (F ↔ᶠ G) t with Γ ⊨ F | Γ ⊨ G
      | Sound Γ F | Complete Γ F | Sound Γ G | Complete Γ G
    ... | false | false | fˢ | fᶜ | gˢ | gᶜ = (gˢ ∘ fᶜ) , (fˢ ∘ gᶜ)
    ... | true  | true  | fˢ | fᶜ | gˢ | gᶜ = (gˢ ∘ fᶜ) , (fˢ ∘ gᶜ)

    Complete Γ (ϕ ᶠ) t = t
    Complete Γ ⊤ᶠ t = tt
    Complete Γ (¬ᶠ F) t with Γ ⊨ F | Sound Γ F
    ... | false | f = tt
    ... | true | f = t (f tt)
    Complete Γ (F ∧ᶠ G) (f , g) with Γ ⊨ F | Γ ⊨ G | Complete Γ F f | Complete Γ G g
    ... | true | true | _ | _ = tt
    Complete Γ (F ∨ᶠ G) t = -- Special treatment for the truncation
      Bool→Type∥⊎∥' _ _ (map∥∥ (map⊎ (Complete Γ F) (Complete Γ G)) t)
    Complete Γ (F →ᶠ G) t with Γ ⊨ F | Γ ⊨ G | Sound Γ F | Complete Γ G
    ... | false | false | _ | _ = tt
    ... | false | true  | _ | _ = tt
    ... | true  | true  | _ | _ = tt
    ... | true  | false | f | g = g (t (f tt))
    Complete Γ (F ↔ᶠ G) t with Γ ⊨ F | Γ ⊨ G
      | Sound Γ F | Complete Γ F | Sound Γ G | Complete Γ G
    ... | false | false | fˢ | fᶜ | gˢ | gᶜ = tt
    ... | false | true  | fˢ | fᶜ | gˢ | gᶜ = fᶜ (snd t (gˢ tt))
    ... | true  | false | fˢ | fᶜ | gˢ | gᶜ = gᶜ (fst t (fˢ tt))
    ... | true  | true  | fˢ | fᶜ | gˢ | gᶜ = tt
open Models
-- Next, we put the automation to use.

open import Cubical.Data.Nat.Base
open import Cubical.Data.Fin.Base
  using (Fin; fzero; fsuc; ¬Fin0; fsplit)
  renaming (elim to elimFin)
FinVec : Type ℓ → ℕ → Type ℓ
FinVec A n = Fin n → A
module _ {A : Type ℓ} where -- Should also be in agda-cubical
  [] : FinVec A zero
  [] = rec⊥ ∘ ¬Fin0

  infixr 10 _∷_
  _∷_ : {n : ℕ} → A → FinVec A n → FinVec A (suc n)
  (a ∷ v) i with fsplit i
  ... | inl _ = a
  ... | inr (j , _) = v j

  FinVecNil : (v : FinVec A zero) → [] ≡ v
  FinVecNil v i r with ¬Fin0 r
  ... | ()

  FinVecCon : ∀ {n} → (v : FinVec A (suc n))
    → v fzero ∷ (v ∘ fsuc) ≡ v
  FinVecCon {n} v = funExt helper
    where
      helper : (i : Fin (suc n)) → (v fzero ∷ (v ∘ fsuc)) i ≡ v i
      helper i with fsplit i
      ... | inl fzero≡i = cong v fzero≡i
      ... | inr (j , fsucj≡i) = cong v fsucj≡i

  elimFinVec : (P : ∀ {n} → FinVec A n → Type ℓ')
    → P {n = zero} [] → (∀ {k} a (v : FinVec A k) → P {n = k} v → P {n = suc k} (a ∷ v))
    → ∀ {n} (v : FinVec A n) → P {n = n} v
  elimFinVec P nil con {zero} v = subst (P {n = zero}) (FinVecNil v) nil
  elimFinVec P nil con {suc n} v = subst (P {n = suc n}) (FinVecCon v)
    (con {k = n} (v (fzero {k = n})) tail ih)
    where
    tail : FinVec A n
    tail = v ∘ fsuc {k = n}

    ih : P {n = n} tail
    ih = elimFinVec P nil con {n = n} tail

module NbE where
  private variable
    n : ℕ
  binFoldBool : {n : ℕ} → (FinVec Bool n → Bool) → Bool
  binFoldBool {zero} α = α []
  binFoldBool {suc n} α
    = binFoldBool {n = n} (λ τ → α (false ∷ τ))
    and binFoldBool {n = n} (λ τ → α (true ∷ τ))

  abstract
    binFoldCorrect :
        {n : ℕ}
      → (Γ : FinVec Bool n)
      → (α : FinVec Bool n → Bool)
      → Bool→Type (binFoldBool {n = n} α)
      → Bool→Type (α Γ)
    binFoldCorrect {zero} Γ α H = subst (λ Γ → Bool→Type (α Γ)) (FinVecNil Γ) H
    binFoldCorrect {suc n} Γ α H = subst (λ Γ → Bool→Type (α Γ)) (FinVecCon Γ) (headProof (Γ fzero) refl)
      where
      tail : FinVec Bool n
      tail = Γ ∘ fsuc

      headProof : (b : Bool) → Γ fzero ≡ b → Bool→Type (α (Γ fzero ∷ tail))
      headProof false eq = subst (λ b → Bool→Type (α (b ∷ tail))) (sym eq)
        (binFoldCorrect {n = n} tail (λ τ → α (false ∷ τ)) (fst (Bool→Type× _ _ H)))
      headProof true eq = subst (λ b → Bool→Type (α (b ∷ tail))) (sym eq)
        (binFoldCorrect {n = n} tail (λ τ → α (true ∷ τ)) (snd (Bool→Type× _ _ H)))

    computeBool : {n : ℕ} (F : Formula (Fin n))
      → {Bool→Type (binFoldBool {n = n} (λ section → section ⊨ F))}
      → (P : FinVec Bool n)
      → (Bool→Type ∘ P) ⊢ F
    computeBool {n = n} F {witness} P = Sound P F (binFoldCorrect {n = n} P (λ section → section ⊨ F) witness)

    computeDec : {n : ℕ} (F : Formula (Fin n))
      → {Bool→Type (binFoldBool {n = n} (λ section → section ⊨ F))}
      → (P : FinVec (DecProp ℓ-zero) n)
      → (fst ∘ fst ∘ P) ⊢ F
    computeDec {n = n} F {witness} P =
      transport (λ i → (λ x → eq (P x) i) ⊢ F)
        (computeBool {n = n} F {witness} (λ x → Dec→Bool (P x .snd)))
      where
        eq : (H : DecProp ℓ-zero)
          → Bool→Type (Dec→Bool (H .snd)) ≡ H .fst .fst
        eq H = sym (ua (Dec≃DecBool (H .fst .snd) (H .snd)))
open NbE public

module Literals {n : ℕ} where
  open import Agda.Builtin.FromNat
    renaming (Number to HasFromNat)
  open import Cubical.Data.Fin.Literals
  instance
    fromNatFormula : HasFromNat (Formula (Fin (suc n)))
    fromNatFormula = record
      { Constraint = fromNatFin {n} .HasFromNat.Constraint
      ; fromNat    = λ m ⦃ m≤n ⦄ → fromNatFin .HasFromNat.fromNat m ᶠ
      }
open Literals public
