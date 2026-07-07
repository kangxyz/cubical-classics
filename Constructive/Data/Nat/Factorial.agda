{-

Factorials as positive natural numbers

-}
{-# OPTIONS --safe #-}
module Constructive.Data.Nat.Factorial where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.NatPlusOne using (ℕ₊₁ ; 1+_ ; ℕ₊₁→ℕ)
open import Cubical.Data.NatPlusOne.Properties using (_·₊₁_)


factorial₊₁ :
  ℕ →
  ℕ₊₁
factorial₊₁ zero =
  1+ zero
factorial₊₁ (suc n) =
  (1+ n) ·₊₁ factorial₊₁ n


factorial :
  ℕ →
  ℕ
factorial n =
  ℕ₊₁→ℕ (factorial₊₁ n)


factorial₊₁-zero :
  factorial₊₁ zero ≡ 1+ zero
factorial₊₁-zero =
  refl


factorial₊₁-suc :
  (n : ℕ) →
  factorial₊₁ (suc n) ≡ (1+ n) ·₊₁ factorial₊₁ n
factorial₊₁-suc n =
  refl


factorial-zero :
  factorial zero ≡ suc zero
factorial-zero =
  refl
