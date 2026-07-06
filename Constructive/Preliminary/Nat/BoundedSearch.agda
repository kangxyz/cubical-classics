{-

Bounded decidable search on natural numbers.

This complements Constructive.Preliminary.Nat.  The search principles there
split truncated global existence proofs for decidable predicates; here the
input is a concrete bound N with P N, and the recursion searches only up to
that bound.

-}
{-# OPTIONS --safe #-}
module Constructive.Preliminary.Nat.BoundedSearch where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; _×_)
import Cubical.Data.Sum as Sum
open import Cubical.Relation.Nullary using (Dec ; yes ; no ; ¬_)


private
  variable
    ℓ : Level


BoundedLeast : (ℕ → Type ℓ) → Type ℓ
BoundedLeast P =
  Σ[ n ∈ ℕ ] P n × ((m : ℕ) → NatOrder._<_ m n → ¬ P m)


boundedLeast :
  {P : ℕ → Type ℓ} →
  ((n : ℕ) → Dec (P n)) →
  (N : ℕ) →
  P N →
  BoundedLeast P
boundedLeast decP zero pN =
  zero , pN , λ m m<0 → Empty.rec (NatOrder.¬-<-zero m<0)
boundedLeast {P = P} decP (suc N) pN with decP zero
... | yes p0 =
  zero , p0 , λ m m<0 → Empty.rec (NatOrder.¬-<-zero m<0)
... | no ¬p0 =
  suc n , pn , noPrev
  where
  Q : ℕ → Type _
  Q n =
    P (suc n)

  decQ : (n : ℕ) → Dec (Q n)
  decQ n =
    decP (suc n)

  leastQ : BoundedLeast Q
  leastQ =
    boundedLeast decQ N pN

  n : ℕ
  n =
    leastQ .fst

  pn : P (suc n)
  pn =
    leastQ .snd .fst

  noPrev :
    (m : ℕ) →
    NatOrder._<_ m (suc n) →
    ¬ P m
  noPrev zero _ =
    ¬p0
  noPrev (suc m) sm<sn =
    leastQ .snd .snd m (NatOrder.pred-≤-pred sm<sn)


boundedLeast-monotone :
  {P Q : ℕ → Type ℓ} →
  (pLeast : BoundedLeast P) →
  (qLeast : BoundedLeast Q) →
  ((n : ℕ) → P n → Q n) →
  NatOrder._≤_ (qLeast .fst) (pLeast .fst)
boundedLeast-monotone pLeast qLeast p→q
  with NatOrder.splitℕ-≤ (qLeast .fst) (pLeast .fst)
... | Sum.inl q≤p =
  q≤p
... | Sum.inr p<q =
  Empty.rec
    (qLeast .snd .snd
      (pLeast .fst)
      p<q
      (p→q (pLeast .fst) (pLeast .snd .fst)))
