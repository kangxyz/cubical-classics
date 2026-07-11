{-

Finite triangular rearrangement of Cauchy-real arrays

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Series.Rearrangement where

open import Cubical.Foundations.Prelude

import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _∸_)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.Series.Finite
  using (partialSum)
open import Constructive.Analysis.Reals.Series.Tail
  using (partialSum-snoc)


antiDiagonalSumᶜ :
  (ℕ → ℕ → ℝᶜ) →
  ℕ →
  ℝᶜ
antiDiagonalSumᶜ u m =
  partialSum (λ n → u n (m Nat.∸ n)) (suc m)


triangularRowsSumᶜ :
  (ℕ → ℕ → ℝᶜ) →
  ℕ →
  ℝᶜ
triangularRowsSumᶜ u N =
  partialSum (λ n → partialSum (u n) (N Nat.∸ n)) N


triangularDiagonalsSumᶜ :
  (ℕ → ℕ → ℝᶜ) →
  ℕ →
  ℝᶜ
triangularDiagonalsSumᶜ u N =
  partialSum (antiDiagonalSumᶜ u) N


antiDiagonalSumᶜ-zero :
  (u : ℕ → ℕ → ℝᶜ) →
  antiDiagonalSumᶜ u zero ≡ u zero zero
antiDiagonalSumᶜ-zero u =
  add-zero-right (u zero zero)


antiDiagonalSumᶜ-suc :
  (u : ℕ → ℕ → ℝᶜ) →
  (N : ℕ) →
  antiDiagonalSumᶜ u (suc N) ≡
  u zero (suc N) +ᶜ
  antiDiagonalSumᶜ (λ n k → u (suc n) k) N
antiDiagonalSumᶜ-suc u N =
  refl


triangularRowsSumᶜ-suc :
  (u : ℕ → ℕ → ℝᶜ) →
  (N : ℕ) →
  triangularRowsSumᶜ u (suc N) ≡
  partialSum (u zero) (suc N) +ᶜ
  triangularRowsSumᶜ (λ n k → u (suc n) k) N
triangularRowsSumᶜ-suc u N =
  refl


private
  triangular-snoc-step :
    (p b r s : ℝᶜ) →
    (p +ᶜ b) +ᶜ (r +ᶜ s) ≡
    (p +ᶜ r) +ᶜ (b +ᶜ s)
  triangular-snoc-step p b r s =
    add-assoc (p +ᶜ b) r s ∙
    cong
      (_+ᶜ s)
      (sym (add-assoc p b r) ∙
       cong (p +ᶜ_) (add-comm b r) ∙
       add-assoc p r b) ∙
    sym (add-assoc (p +ᶜ r) b s)


triangularRowsSumᶜ-snoc :
  (u : ℕ → ℕ → ℝᶜ) →
  (N : ℕ) →
  triangularRowsSumᶜ u (suc N) ≡
  triangularRowsSumᶜ u N +ᶜ antiDiagonalSumᶜ u N
triangularRowsSumᶜ-snoc u zero =
  add-zero-right (antiDiagonalSumᶜ u zero) ∙
  sym (add-zero-left (antiDiagonalSumᶜ u zero))
triangularRowsSumᶜ-snoc u (suc N) =
  triangularRowsSumᶜ-suc u (suc N) ∙
  cong₂
    _+ᶜ_
    (partialSum-snoc (u zero) (suc N))
    (triangularRowsSumᶜ-snoc shifted N) ∙
  triangular-snoc-step
    rowHead
    boundaryHead
    shiftedRows
    shiftedDiagonal ∙
  cong₂
    _+ᶜ_
    (sym (triangularRowsSumᶜ-suc u N))
    (sym (antiDiagonalSumᶜ-suc u N))
  where
  shifted : ℕ → ℕ → ℝᶜ
  shifted n k =
    u (suc n) k

  rowHead : ℝᶜ
  rowHead =
    partialSum (u zero) (suc N)

  boundaryHead : ℝᶜ
  boundaryHead =
    u zero (suc N)

  shiftedRows : ℝᶜ
  shiftedRows =
    triangularRowsSumᶜ shifted N

  shiftedDiagonal : ℝᶜ
  shiftedDiagonal =
    antiDiagonalSumᶜ shifted N


triangularRowsSumᶜ-diagonals :
  (u : ℕ → ℕ → ℝᶜ) →
  (N : ℕ) →
  triangularRowsSumᶜ u N ≡
  triangularDiagonalsSumᶜ u N
triangularRowsSumᶜ-diagonals u zero =
  refl
triangularRowsSumᶜ-diagonals u (suc N) =
  triangularRowsSumᶜ-snoc u N ∙
  cong
    (_+ᶜ antiDiagonalSumᶜ u N)
    (triangularRowsSumᶜ-diagonals u N) ∙
  sym (partialSum-snoc (antiDiagonalSumᶜ u) N)
