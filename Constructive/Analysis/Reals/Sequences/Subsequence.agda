{-

Shifts and subsequences of Cauchy-real sequences

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Sequences.Subsequence where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; _+_)
import Cubical.Data.Nat.Order as NatOrder

open import Constructive.Analysis.Modulus
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.Sequences.Base
open import Constructive.Analysis.Reals.Sequences.Cauchy
open import Constructive.Analysis.Reals.Sequences.Convergence


shift : ℕ → Sequence → Sequence
shift k u n =
  u (k + n)


IsSubsequenceIndex :
  (ℕ → ℕ) →
  Type₀
IsSubsequenceIndex φ =
  (n : ℕ) → NatOrder._≤_ n (φ n)


subsequence :
  (ℕ → ℕ) →
  Sequence →
  Sequence
subsequence φ u n =
  u (φ n)


shiftConvergesWithModulus :
  {u : Sequence} →
  {x : ℝᶜ} →
  {μ : NatModulus} →
  (k : ℕ) →
  ConvergesWithModulus u x μ →
  ConvergesWithModulus (shift k u) x μ
shiftConvergesWithModulus {μ = μ} k u→x ε n μ≤n =
  u→x ε (k + n)
    (NatOrder.≤-trans μ≤n NatOrder.≤SumRight)


shiftCauchyWithModulus :
  {u : Sequence} →
  {μ : NatModulus} →
  (k : ℕ) →
  CauchyWithModulus u μ →
  CauchyWithModulus (shift k u) μ
shiftCauchyWithModulus k u-cauchy ε m n μ≤m μ≤n =
  u-cauchy
    ε
    (k + m)
    (k + n)
    (NatOrder.≤-trans μ≤m NatOrder.≤SumRight)
    (NatOrder.≤-trans μ≤n NatOrder.≤SumRight)


subsequenceConvergesWithModulus :
  {u : Sequence} →
  {x : ℝᶜ} →
  {μ : NatModulus} →
  {φ : ℕ → ℕ} →
  IsSubsequenceIndex φ →
  ConvergesWithModulus u x μ →
  ConvergesWithModulus (subsequence φ u) x μ
subsequenceConvergesWithModulus {μ = μ} {φ = φ} φ-lower u→x ε n μ≤n =
  u→x ε (φ n)
    (NatOrder.≤-trans μ≤n (φ-lower n))


subsequenceCauchyWithModulus :
  {u : Sequence} →
  {μ : NatModulus} →
  {φ : ℕ → ℕ} →
  IsSubsequenceIndex φ →
  CauchyWithModulus u μ →
  CauchyWithModulus (subsequence φ u) μ
subsequenceCauchyWithModulus {μ = μ} {φ = φ} φ-lower u-cauchy ε m n μ≤m μ≤n =
  u-cauchy
    ε
    (φ m)
    (φ n)
    (NatOrder.≤-trans μ≤m (φ-lower m))
    (NatOrder.≤-trans μ≤n (φ-lower n))
