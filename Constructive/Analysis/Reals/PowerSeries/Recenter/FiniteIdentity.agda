{-

Finite triangular algebra for re-centering power series.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Recenter.FiniteIdentity where

open import Cubical.Foundations.Prelude

import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.FinData.Base using (Fin)
import Cubical.Data.FinData.Properties as FinProperties
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.Series
  using (partialSum ; partialSum-snoc)
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Binomial
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Base
  using (recenterCoefficientTerm ; recenterCoefficientTerm-full)


private
  module SolverHelpers where
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

    binomial-term-rearrange :
      (a b h d : ℝᶜ) →
      a ·ᶜ ((b ·ᶜ h) ·ᶜ d) ≡
      ((b ·ᶜ a) ·ᶜ d) ·ᶜ h
    binomial-term-rearrange a b h d =
      mulᶜ-assoc a (b ·ᶜ h) d ∙
      cong
        (_·ᶜ d)
        (mulᶜ-comm a (b ·ᶜ h) ∙
        sym (mulᶜ-assoc b h a) ∙
        cong (b ·ᶜ_) (mulᶜ-comm h a) ∙
        mulᶜ-assoc b a h) ∙
      sym (mulᶜ-assoc (b ·ᶜ a) h d) ∙
      cong ((b ·ᶜ a) ·ᶜ_) (mulᶜ-comm h d) ∙
      mulᶜ-assoc (b ·ᶜ a) d h


partialSum-CRSum :
  (u : ℕ → ℝᶜ) →
  (n : ℕ) →
  CRSum.∑ (λ (i : Fin n) → u (Fin.toℕ i)) ≡
  partialSum u n
partialSum-CRSum u zero =
  refl
partialSum-CRSum u (suc n) =
  cong (u zero +ᶜ_) (partialSum-CRSum (λ k → u (suc k)) n)


recenterDiagonalTerm-path :
  (a : PowerSeries) →
  (d h : ℝᶜ) →
  (m : ℕ) →
  (i : Fin (suc m)) →
  a m ·ᶜ binomialVecᶜ m h d i ≡
  recenterCoefficientTerm
    a
    d
    (Fin.toℕ i)
    (m Nat.∸ Fin.toℕ i) ·ᶜ
  realPower h (Fin.toℕ i)
recenterDiagonalTerm-path a d h m i =
  SolverHelpers.binomial-term-rearrange
    (a m)
    B
    hpow
    dpow ∙
  cong
    (_·ᶜ hpow)
    coefficient-path
  where
  n : ℕ
  n =
    Fin.toℕ i

  k : ℕ
  k =
    m Nat.∸ n

  B : ℝᶜ
  B =
    binomialᶜ m n

  hpow : ℝᶜ
  hpow =
    realPower h n

  dpow : ℝᶜ
  dpow =
    realPower d k

  n≤m : NatOrder._≤_ n m
  n≤m =
    NatOrder.pred-≤-pred (FinProperties.toℕ<n i)

  n+k≡m : n Nat.+ k ≡ m
  n+k≡m =
    Nat.+-comm n k ∙
    NatOrder.≤-∸-+-cancel n≤m

  coefficient-path :
    (binomialᶜ m n ·ᶜ a m) ·ᶜ dpow ≡
    recenterCoefficientTerm a d n k
  coefficient-path =
    sym
      (recenterCoefficientTerm-full a d n k ∙
      cong
        (λ l → (binomialᶜ l n ·ᶜ a l) ·ᶜ dpow)
        n+k≡m)


powerSeriesTerm-recenterDiagonal :
  (a : PowerSeries) →
  (d h : ℝᶜ) →
  (m : ℕ) →
  powerSeriesTerm a (h +ᶜ d) m ≡
  antiDiagonalSumᶜ
    (λ n k →
      recenterCoefficientTerm a d n k ·ᶜ
      realPower h n)
    m
powerSeriesTerm-recenterDiagonal a d h m =
  cong (a m ·ᶜ_) (binomialTheoremᶜ m h d) ∙
  CRSum.∑Mulrdist (a m) (binomialVecᶜ m h d) ∙
  CRSum.∑Ext (recenterDiagonalTerm-path a d h m) ∙
  partialSum-CRSum
    (λ n →
      recenterCoefficientTerm a d n (m Nat.∸ n) ·ᶜ
      realPower h n)
    (suc m)


antiDiagonalSumᶜ-suc :
  (u : ℕ → ℕ → ℝᶜ) →
  (N : ℕ) →
  antiDiagonalSumᶜ u (suc N) ≡
  u zero (suc N) +ᶜ
  antiDiagonalSumᶜ (λ n k → u (suc n) k) N
antiDiagonalSumᶜ-suc u N =
  refl


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
  SolverHelpers.triangular-snoc-step
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


powerSeriesPartialSum-recenterTriangle :
  (a : PowerSeries) →
  (d h : ℝᶜ) →
  (N : ℕ) →
  powerSeriesPartialSum a (h +ᶜ d) N ≡
  triangularRowsSumᶜ
    (λ n k →
      recenterCoefficientTerm a d n k ·ᶜ
      realPower h n)
    N
powerSeriesPartialSum-recenterTriangle a d h N =
  cong
    (λ u → partialSum u N)
    (funExt (powerSeriesTerm-recenterDiagonal a d h)) ∙
  sym
    (triangularRowsSumᶜ-diagonals
      (λ n k →
        recenterCoefficientTerm a d n k ·ᶜ
        realPower h n)
      N)


powerSeriesPartialSum-recenterTriangle-shifted :
  (a : PowerSeries) →
  (d h : ℝᶜ) →
  (N : ℕ) →
  powerSeriesPartialSum a (d +ᶜ h) N ≡
  triangularRowsSumᶜ
    (λ n k →
      recenterCoefficientTerm a d n k ·ᶜ
      realPower h n)
    N
powerSeriesPartialSum-recenterTriangle-shifted a d h N =
  powerSeriesPartialSum-cong
    (λ _ → refl)
    (add-comm d h)
    N ∙
  powerSeriesPartialSum-recenterTriangle a d h N
