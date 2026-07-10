{-

Series finite infrastructure for HoTT Cauchy reals

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Series.Finite where

open import Cubical.Foundations.Prelude

import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.FinData.Base using (Fin)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Data.Sum using (inl ; inr)

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Base
import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Reals.CauchyReals.Metric
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
  using (≤ᶜ-add ; negᶜ-pres≤ᶜ)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open ClosenessOf RationalsMetricSpace

sumFin :
  (n : ℕ) →
  (Fin n → ℝᶜ) →
  ℝᶜ
sumFin zero _ =
  0ᶜ
sumFin (suc n) x =
  x Fin.zero +ᶜ sumFin n (λ i → x (Fin.suc i))


sumFin-zero :
  (x : Fin zero → ℝᶜ) →
  sumFin zero x ≡ 0ᶜ
sumFin-zero x =
  refl


sumFin-suc :
  (n : ℕ) →
  (x : Fin (suc n) → ℝᶜ) →
  sumFin (suc n) x ≡
  x Fin.zero +ᶜ sumFin n (λ i → x (Fin.suc i))
sumFin-suc n x =
  refl


sumFin-one :
  (x : Fin (suc zero) → ℝᶜ) →
  sumFin (suc zero) x ≡ x Fin.zero
sumFin-one x =
  add-zero-right (x Fin.zero)


sumFin-zero-sequence :
  (n : ℕ) →
  sumFin n (λ _ → 0ᶜ) ≡ 0ᶜ
sumFin-zero-sequence zero =
  refl
sumFin-zero-sequence (suc n) =
  cong (0ᶜ +ᶜ_) (sumFin-zero-sequence n) ∙
  add-zero-left 0ᶜ


sumFin-add :
  (n : ℕ) →
  (x y : Fin n → ℝᶜ) →
  sumFin n (λ i → x i +ᶜ y i) ≡
  sumFin n x +ᶜ sumFin n y
sumFin-add zero x y =
  sym (add-zero-left 0ᶜ)
sumFin-add (suc n) x y =
  cong ((x Fin.zero +ᶜ y Fin.zero) +ᶜ_) (sumFin-add n x-tail y-tail) ∙
  add-interchange (x Fin.zero) (y Fin.zero) (sumFin n x-tail) (sumFin n y-tail)
  where
  x-tail : Fin n → ℝᶜ
  x-tail i =
    x (Fin.suc i)

  y-tail : Fin n → ℝᶜ
  y-tail i =
    y (Fin.suc i)


sumFin-neg :
  (n : ℕ) →
  (x : Fin n → ℝᶜ) →
  sumFin n (λ i → -ᶜ x i) ≡ -ᶜ sumFin n x
sumFin-neg zero x =
  sym neg-zeroᶜ
sumFin-neg (suc n) x =
  cong ((-ᶜ x Fin.zero) +ᶜ_) (sumFin-neg n x-tail) ∙
  sym (neg-add (x Fin.zero) (sumFin n x-tail))
  where
  x-tail : Fin n → ℝᶜ
  x-tail i =
    x (Fin.suc i)


sumFin-++Fin :
  (n m : ℕ) →
  (x : Fin n → ℝᶜ) →
  (y : Fin m → ℝᶜ) →
  sumFin (n + m) (Fin._++Fin_ x y) ≡
  sumFin n x +ᶜ sumFin m y
sumFin-++Fin zero m x y =
  sym (add-zero-left (sumFin m y))
sumFin-++Fin (suc n) m x y =
  cong (x Fin.zero +ᶜ_) (sumFin-++Fin n m x-tail y) ∙
  add-assoc (x Fin.zero) (sumFin n x-tail) (sumFin m y)
  where
  x-tail : Fin n → ℝᶜ
  x-tail i =
    x (Fin.suc i)


sumFin-abs-bound :
  (n : ℕ) →
  (x : Fin n → ℝᶜ) →
  absᶜ (sumFin n x) ≤ᶜ sumFin n (λ i → absᶜ (x i))
sumFin-abs-bound zero x =
  subst
    (λ w → w ≤ᶜ 0ᶜ)
    (sym absᶜ-zero)
    (≤ᶜ-refl 0ᶜ)
sumFin-abs-bound (suc n) x =
  ≤ᶜ-trans
    {x = absᶜ (x Fin.zero +ᶜ sumFin n x-tail)}
    {y = absᶜ (x Fin.zero) +ᶜ absᶜ (sumFin n x-tail)}
    {z = absᶜ (x Fin.zero) +ᶜ sumFin n abs-tail}
    (absᶜ-triangle (x Fin.zero) (sumFin n x-tail))
    (≤ᶜ-add
      {a = absᶜ (x Fin.zero)}
      {b = absᶜ (x Fin.zero)}
      {c = absᶜ (sumFin n x-tail)}
      {d = sumFin n abs-tail}
      (≤ᶜ-refl (absᶜ (x Fin.zero)))
      (sumFin-abs-bound n x-tail))
  where
  x-tail : Fin n → ℝᶜ
  x-tail i =
    x (Fin.suc i)

  abs-tail : Fin n → ℝᶜ
  abs-tail i =
    absᶜ (x-tail i)


sumFin-mono :
  (n : ℕ) →
  (x y : Fin n → ℝᶜ) →
  ((i : Fin n) → x i ≤ᶜ y i) →
  sumFin n x ≤ᶜ sumFin n y
sumFin-mono zero x y x≤y =
  ≤ᶜ-refl 0ᶜ
sumFin-mono (suc n) x y x≤y =
  ≤ᶜ-add
    {a = x Fin.zero}
    {b = y Fin.zero}
    {c = sumFin n x-tail}
    {d = sumFin n y-tail}
    (x≤y Fin.zero)
    (sumFin-mono n x-tail y-tail λ i → x≤y (Fin.suc i))
  where
  x-tail : Fin n → ℝᶜ
  x-tail i =
    x (Fin.suc i)

  y-tail : Fin n → ℝᶜ
  y-tail i =
    y (Fin.suc i)


sumFin-nonnegative :
  (n : ℕ) →
  (x : Fin n → ℝᶜ) →
  ((i : Fin n) → 0ᶜ ≤ᶜ x i) →
  0ᶜ ≤ᶜ sumFin n x
sumFin-nonnegative n x 0≤x =
  subst
    (λ z → z ≤ᶜ sumFin n x)
    (sumFin-zero-sequence n)
    (sumFin-mono n (λ _ → 0ᶜ) x 0≤x)


sumFin-comparison :
  (n : ℕ) →
  (x y : Fin n → ℝᶜ) →
  ((i : Fin n) → absᶜ (x i) ≤ᶜ y i) →
  absᶜ (sumFin n x) ≤ᶜ sumFin n y
sumFin-comparison n x y x≤y =
  ≤ᶜ-trans
    {x = absᶜ (sumFin n x)}
    {y = sumFin n (λ i → absᶜ (x i))}
    {z = sumFin n y}
    (sumFin-abs-bound n x)
    (sumFin-mono n (λ i → absᶜ (x i)) y x≤y)


partialSum :
  (ℕ → ℝᶜ) →
  ℕ →
  ℝᶜ
partialSum u n =
  sumFin n (λ i → u (Fin.toℕ i))


partialSum-zero :
  (u : ℕ → ℝᶜ) →
  partialSum u zero ≡ 0ᶜ
partialSum-zero u =
  refl


partialSum-suc :
  (u : ℕ → ℝᶜ) →
  (n : ℕ) →
  partialSum u (suc n) ≡
  u zero +ᶜ partialSum (λ k → u (suc k)) n
partialSum-suc u n =
  refl


partialSum-zero-sequence :
  (n : ℕ) →
  partialSum (λ _ → 0ᶜ) n ≡ 0ᶜ
partialSum-zero-sequence =
  sumFin-zero-sequence


partialSum-add :
  (u v : ℕ → ℝᶜ) →
  (n : ℕ) →
  partialSum (λ k → u k +ᶜ v k) n ≡
  partialSum u n +ᶜ partialSum v n
partialSum-add u v n =
  sumFin-add n (λ i → u (Fin.toℕ i)) (λ i → v (Fin.toℕ i))


partialSum-neg :
  (u : ℕ → ℝᶜ) →
  (n : ℕ) →
  partialSum (λ k → -ᶜ u k) n ≡ -ᶜ partialSum u n
partialSum-neg u n =
  sumFin-neg n (λ i → u (Fin.toℕ i))


partialSum-abs-bound :
  (u : ℕ → ℝᶜ) →
  (n : ℕ) →
  absᶜ (partialSum u n) ≤ᶜ partialSum (λ k → absᶜ (u k)) n
partialSum-abs-bound u n =
  sumFin-abs-bound n (λ i → u (Fin.toℕ i))


partialSum-comparison :
  (u v : ℕ → ℝᶜ) →
  ((n : ℕ) → absᶜ (u n) ≤ᶜ v n) →
  (n : ℕ) →
  absᶜ (partialSum u n) ≤ᶜ partialSum v n
partialSum-comparison u v u≤v n =
  sumFin-comparison
    n
    (λ i → u (Fin.toℕ i))
    (λ i → v (Fin.toℕ i))
    (λ i → u≤v (Fin.toℕ i))


partialSum-nonnegative :
  (u : ℕ → ℝᶜ) →
  ((n : ℕ) → 0ᶜ ≤ᶜ u n) →
  (n : ℕ) →
  0ᶜ ≤ᶜ partialSum u n
partialSum-nonnegative u 0≤u n =
  sumFin-nonnegative n (λ i → u (Fin.toℕ i)) (λ i → 0≤u (Fin.toℕ i))
