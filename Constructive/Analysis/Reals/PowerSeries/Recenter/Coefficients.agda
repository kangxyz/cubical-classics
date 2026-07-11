{-

Basic re-centering coefficient data.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Recenter.Coefficients where

open import Cubical.Foundations.Prelude

import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder

open import Constructive.Analysis.Modulus using (AntitoneNatModulus)
open import Constructive.Analysis.Metric.Base
  using (MetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Metric
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  using (BoundedByᶜ ; bounded-byᶜ-zero)
open import Constructive.Analysis.Reals.Series
  using
    ( TailBound
    ; shift
    ; shift-index
    ; partialSum
    ; partialSum-suc
    ; partialSum-zero-sequence
    ; seriesSumFromFiniteTailBound
    ; seriesSumFromFiniteTailBoundConvergesAt
    ; tailSum
    )
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Power
  using (realPower)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Binomial
open import Constructive.Analysis.Reals.PowerSeries.Algebra.Finite
  using (realPower-zero-suc)
open import Constructive.Data.PositiveRationals
  using (ℚ⁺)


recenterCoefficientTerm :
  PowerSeries →
  ℝᶜ →
  ℕ →
  ℕ →
  ℝᶜ
recenterCoefficientTerm a d n zero =
  a n
recenterCoefficientTerm a d n (suc k) =
  binomialᶜ (n Nat.+ suc k) n ·ᶜ
  a (n Nat.+ suc k) ·ᶜ
  realPower d (suc k)


recenterCoefficientTerm-full :
  (a : PowerSeries) →
  (d : ℝᶜ) →
  (n k : ℕ) →
  recenterCoefficientTerm a d n k ≡
  binomialᶜ (n Nat.+ k) n ·ᶜ
  a (n Nat.+ k) ·ᶜ
  realPower d k
recenterCoefficientTerm-full a d n zero =
  sym rhs-to-lhs
  where
  rhs-to-lhs :
    binomialᶜ (n Nat.+ zero) n ·ᶜ
    a (n Nat.+ zero) ·ᶜ
    realPower d zero ≡
    a n
  rhs-to-lhs =
    cong₂
      (λ b x → b ·ᶜ x ·ᶜ 1ᶜ)
      (cong (λ m → binomialᶜ m n) (Nat.+-zero n))
      (cong a (Nat.+-zero n)) ∙
    cong
      (λ b → b ·ᶜ a n ·ᶜ 1ᶜ)
      (binomialᶜ-diagonal n) ∙
    cong
      (_·ᶜ 1ᶜ)
      (mulᶜ-one-left (a n)) ∙
    mulᶜ-one-right (a n)
recenterCoefficientTerm-full a d n (suc k) =
  refl


recenterCoefficientPartial :
  PowerSeries →
  ℝᶜ →
  ℕ →
  ℕ →
  ℝᶜ
recenterCoefficientPartial a d n =
  partialSum (recenterCoefficientTerm a d n)


record RecenterCoefficientConvergenceData
    (a : PowerSeries)
    (d : ℝᶜ)
    (n : ℕ)
    : Type₀ where
  field
    modulus :
      ℚ⁺ →
      ℕ

    tailBound :
      TailBound (recenterCoefficientTerm a d n) modulus

    modulus-antitone :
      AntitoneNatModulus modulus


open RecenterCoefficientConvergenceData public


recenterCoefficientSumWith :
  (a : PowerSeries) →
  (d : ℝᶜ) →
  (n : ℕ) →
  RecenterCoefficientConvergenceData a d n →
  ℝᶜ
recenterCoefficientSumWith a d n conv =
  seriesSumFromFiniteTailBound
    (recenterCoefficientTerm a d n)
    (modulus conv)
    (tailBound conv)
    (modulus-antitone conv)


record RecenterPowerSeriesData
    (a : PowerSeries)
    (d : ℝᶜ)
    : Type₀ where
  field
    coefficientData :
      (n : ℕ) →
      RecenterCoefficientConvergenceData a d n


open RecenterPowerSeriesData public


recenterPowerSeriesWith :
  (a : PowerSeries) →
  (d : ℝᶜ) →
  RecenterPowerSeriesData a d →
  PowerSeries
recenterPowerSeriesWith a d recenterData n =
  recenterCoefficientSumWith a d n (coefficientData recenterData n)




recenterCoefficientTerm-at-zero-suc :
  (a : PowerSeries) →
  (n k : ℕ) →
  recenterCoefficientTerm a 0ᶜ n (suc k) ≡ 0ᶜ
recenterCoefficientTerm-at-zero-suc a n k =
  cong
    (binomialᶜ (n Nat.+ suc k) n ·ᶜ a (n Nat.+ suc k) ·ᶜ_)
    (realPower-zero-suc k) ∙
  mulᶜ-zero-right
    (binomialᶜ (n Nat.+ suc k) n ·ᶜ a (n Nat.+ suc k))


shift-recenterCoefficientTerm-at-zero-suc :
  (a : PowerSeries) →
  (n m : ℕ) →
  shift (suc m) (recenterCoefficientTerm a 0ᶜ n) ≡
  (λ _ → 0ᶜ)
shift-recenterCoefficientTerm-at-zero-suc a n m =
  funExt λ k →
    shift-index
      (suc m)
      (recenterCoefficientTerm a 0ᶜ n)
      k ∙
    recenterCoefficientTerm-at-zero-suc a n (m Nat.+ k)


tailSum-recenterCoefficientTerm-at-zero :
  (a : PowerSeries) →
  (n m k : ℕ) →
  NatOrder._≤_ (suc zero) m →
  tailSum (recenterCoefficientTerm a 0ᶜ n) m k ≡ 0ᶜ
tailSum-recenterCoefficientTerm-at-zero a n m k (j , j+1≡m) =
  subst
    (λ l → tailSum (recenterCoefficientTerm a 0ᶜ n) l k ≡ 0ᶜ)
    sucJ≡m
    tail-at-suc
  where
  sucJ≡m : suc j ≡ m
  sucJ≡m =
    sym (Nat.+-suc j zero ∙ cong suc (Nat.+-zero j)) ∙
    j+1≡m

  tail-at-suc :
    tailSum (recenterCoefficientTerm a 0ᶜ n) (suc j) k ≡ 0ᶜ
  tail-at-suc =
    cong
      (λ u → partialSum u k)
      (shift-recenterCoefficientTerm-at-zero-suc a n j) ∙
    partialSum-zero-sequence k


recenterCoefficientTermAtZeroTailBound :
  (a : PowerSeries) →
  (n : ℕ) →
  TailBound (recenterCoefficientTerm a 0ᶜ n) (λ _ → suc zero)
recenterCoefficientTermAtZeroTailBound a n ε m k 1≤m =
  subst
    (λ x → BoundedByᶜ ε x)
    (sym (tailSum-recenterCoefficientTerm-at-zero a n m k 1≤m))
    (bounded-byᶜ-zero ε)


recenterCoefficientTermAtZeroModulusAntitone :
  AntitoneNatModulus (λ _ → suc zero)
recenterCoefficientTermAtZeroModulusAntitone _ =
  NatOrder.≤-refl


recenterCoefficientConvergenceDataAtZero :
  (a : PowerSeries) →
  (n : ℕ) →
  RecenterCoefficientConvergenceData a 0ᶜ n
modulus (recenterCoefficientConvergenceDataAtZero a n) =
  λ _ → suc zero
tailBound (recenterCoefficientConvergenceDataAtZero a n) =
  recenterCoefficientTermAtZeroTailBound a n
modulus-antitone (recenterCoefficientConvergenceDataAtZero a n) =
  recenterCoefficientTermAtZeroModulusAntitone


recenterPowerSeriesDataAtZero :
  (a : PowerSeries) →
  RecenterPowerSeriesData a 0ᶜ
coefficientData (recenterPowerSeriesDataAtZero a) =
  recenterCoefficientConvergenceDataAtZero a


recenterCoefficientPartial-at-zero-suc :
  (a : PowerSeries) →
  (n k : ℕ) →
  recenterCoefficientPartial a 0ᶜ n (suc k) ≡ a n
recenterCoefficientPartial-at-zero-suc a n k =
  partialSum-suc (recenterCoefficientTerm a 0ᶜ n) k ∙
  cong₂
    _+ᶜ_
    refl
    (cong
      (λ u → partialSum u k)
      (funExt (recenterCoefficientTerm-at-zero-suc a n)) ∙
    partialSum-zero-sequence k) ∙
  add-zero-right (a n)


recenterCoefficientSumAtZero-path :
  (a : PowerSeries) →
  (n : ℕ) →
  recenterCoefficientSumWith
    a
    0ᶜ
    n
    (recenterCoefficientConvergenceDataAtZero a n)
  ≡
  a n
recenterCoefficientSumAtZero-path a n =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    coefficientSum
    (a n)
    (λ ε →
      subst
        (λ x → MetricSpace.Close CauchyRealsMetricSpace coefficientSum ε x)
        (recenterCoefficientPartial-at-zero-suc a n zero)
        (seriesSumFromFiniteTailBoundConvergesAt
          (recenterCoefficientTerm a 0ᶜ n)
          (λ _ → suc zero)
          (recenterCoefficientTermAtZeroTailBound a n)
          recenterCoefficientTermAtZeroModulusAntitone
          ε
          (suc zero)
          NatOrder.≤-refl))
  where
  coefficientSum : ℝᶜ
  coefficientSum =
    recenterCoefficientSumWith
      a
      0ᶜ
      n
      (recenterCoefficientConvergenceDataAtZero a n)


recenterPowerSeriesWithAtZero-path :
  (a : PowerSeries) →
  recenterPowerSeriesWith a 0ᶜ (recenterPowerSeriesDataAtZero a) ≡ a
recenterPowerSeriesWithAtZero-path a =
  funExt (recenterCoefficientSumAtZero-path a)
