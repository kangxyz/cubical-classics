{-

Part of Constructive.Analysis.Reals.PowerSeries.Examples.Polynomial

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Examples.Polynomial.FiniteSupport where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.FinData.Base using (Fin)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using (neg-zeroᶜ)
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Power
  using (realPower)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Analytic
  using (HasPowerSeriesAt)
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    (tailSum-zero-sequence)
open import Constructive.Data.PositiveRationals


PowerSeriesZeroAfter :
  PowerSeries →
  ℕ →
  Type₀
PowerSeriesZeroAfter a N =
  (n : ℕ) →
  NatOrder._≤_ N n →
  a n ≡ 0ᶜ


IsPolynomialPowerSeries :
  PowerSeries →
  Type₀
IsPolynomialPowerSeries a =
  Σ[ N ∈ ℕ ] PowerSeriesZeroAfter a N


powerSeriesZeroAfter-weaken :
  {a : PowerSeries} →
  {N M : ℕ} →
  NatOrder._≤_ N M →
  PowerSeriesZeroAfter a N →
  PowerSeriesZeroAfter a M
powerSeriesZeroAfter-weaken N≤M zeroAfter n M≤n =
  zeroAfter n (NatOrder.≤-trans N≤M M≤n)


powerSeriesTerm-zeroAfter :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a N →
  (h : ℝᶜ) →
  (n : ℕ) →
  NatOrder._≤_ N n →
  powerSeriesTerm a h n ≡ 0ᶜ
powerSeriesTerm-zeroAfter {a = a} N zeroAfter h n N≤n =
  cong
    (λ c → c ·ᶜ realPower h n)
    (zeroAfter n N≤n) ∙
  mulᶜ-zero-left (realPower h n)


shift-powerSeriesTerm-zeroAfter :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a N →
  (h : ℝᶜ) →
  (m n : ℕ) →
  NatOrder._≤_ N m →
  shift m (powerSeriesTerm a h) n ≡ 0ᶜ
shift-powerSeriesTerm-zeroAfter {a = a} N zeroAfter h m n N≤m =
  shift-index m (powerSeriesTerm a h) n ∙
  powerSeriesTerm-zeroAfter N zeroAfter h (m Nat.+ n) N≤m+n
  where
  N≤m+n : NatOrder._≤_ N (m Nat.+ n)
  N≤m+n =
    NatOrder.≤-trans
      N≤m
      (NatOrder.≤SumLeft {n = m} {k = n})


tailSum-powerSeriesTerm-zeroAfter :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a N →
  (h : ℝᶜ) →
  (m k : ℕ) →
  NatOrder._≤_ N m →
  tailSum (powerSeriesTerm a h) m k ≡ 0ᶜ
tailSum-powerSeriesTerm-zeroAfter N zeroAfter h m k N≤m =
  cong
    (λ u → partialSum u k)
    (funExt
      (λ n →
        shift-powerSeriesTerm-zeroAfter N zeroAfter h m n N≤m))
    ∙ tailSum-zero-sequence 0 k


finiteSupportPowerSeriesTailBound :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a N →
  (h : ℝᶜ) →
  PowerSeriesTailBound a h (λ _ → N)
finiteSupportPowerSeriesTailBound N zeroAfter h ε m k N≤m =
  subst
    (BoundedByᶜ ε)
    (sym (tailSum-powerSeriesTerm-zeroAfter N zeroAfter h m k N≤m))
    (bounded-byᶜ-zero ε)


finiteSupportPowerSeriesOnBallWith :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a N →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBallWith a ρ (λ _ → N)
finiteSupportPowerSeriesOnBallWith {a = a} N zeroAfter {ρ = ρ} =
  hasPowerSeriesOnBallWith
    {a = a}
    {ρ = ρ}
    {μ = λ _ → N}
    (λ _ → NatOrder.≤-refl)
    (λ (h : ℝᶜ) _ →
      finiteSupportPowerSeriesTailBound N zeroAfter h)


finiteSupportPowerSeriesOnBall :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a N →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBall a ρ
finiteSupportPowerSeriesOnBall N zeroAfter =
  (λ _ → N) , finiteSupportPowerSeriesOnBallWith N zeroAfter


finiteSupportPowerSeriesInfiniteRadius :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a N →
  HasInfinitePowerSeriesRadius a
finiteSupportPowerSeriesInfiniteRadius N zeroAfter _ =
  finiteSupportPowerSeriesOnBall N zeroAfter


polynomialPowerSeriesOnBallWith :
  {a : PowerSeries} →
  (poly : IsPolynomialPowerSeries a) →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBallWith a ρ (λ _ → fst poly)
polynomialPowerSeriesOnBallWith (N , zeroAfter) =
  finiteSupportPowerSeriesOnBallWith N zeroAfter


polynomialPowerSeriesOnBall :
  {a : PowerSeries} →
  IsPolynomialPowerSeries a →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBall a ρ
polynomialPowerSeriesOnBall (N , zeroAfter) =
  finiteSupportPowerSeriesOnBall N zeroAfter


polynomialPowerSeriesInfiniteRadius :
  {a : PowerSeries} →
  IsPolynomialPowerSeries a →
  HasInfinitePowerSeriesRadius a
polynomialPowerSeriesInfiniteRadius (N , zeroAfter) =
  finiteSupportPowerSeriesInfiniteRadius N zeroAfter


finiteSupportPowerSeriesSumOnBall-partialSum :
  {a : PowerSeries} →
  (N : ℕ) →
  (zeroAfter : PowerSeriesZeroAfter a N) →
  {ρ : ℚ⁺} →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    a
    ρ
    (λ _ → N)
    (finiteSupportPowerSeriesOnBallWith N zeroAfter)
    h
    h-bound
  ≡ powerSeriesPartialSum a h N
finiteSupportPowerSeriesSumOnBall-partialSum N zeroAfter h h-bound =
  powerSeriesSumOnBall-constantModulusPartialSum
    N
    (finiteSupportPowerSeriesOnBallWith N zeroAfter)
    h
    h-bound


centeredFiniteSupportPowerSeriesSumOnBall-partialSum :
  {a : PowerSeries} →
  (N : ℕ) →
  (zeroAfter : PowerSeriesZeroAfter a N) →
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  (x : ℝᶜ) →
  (inBall : InPowerSeriesBall c ρ x) →
  centeredPowerSeriesSumOnBall
    a
    c
    ρ
    (λ _ → N)
    (finiteSupportPowerSeriesOnBallWith N zeroAfter)
    x
    inBall
  ≡ powerSeriesPartialSum a (centeredDisplacement c x) N
centeredFiniteSupportPowerSeriesSumOnBall-partialSum N zeroAfter c x inBall =
  centeredPowerSeriesSumOnBall-constantModulusPartialSum
    N
    (finiteSupportPowerSeriesOnBallWith N zeroAfter)
    x
    inBall


polynomialPowerSeriesSumOnBall-partialSum :
  {a : PowerSeries} →
  (poly : IsPolynomialPowerSeries a) →
  {ρ : ℚ⁺} →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    a
    ρ
    (λ _ → fst poly)
    (polynomialPowerSeriesOnBallWith poly)
    h
    h-bound
  ≡ powerSeriesPartialSum a h (fst poly)
polynomialPowerSeriesSumOnBall-partialSum (N , zeroAfter) =
  finiteSupportPowerSeriesSumOnBall-partialSum N zeroAfter


centeredPolynomialPowerSeriesSumOnBall-partialSum :
  {a : PowerSeries} →
  (poly : IsPolynomialPowerSeries a) →
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  (x : ℝᶜ) →
  (inBall : InPowerSeriesBall c ρ x) →
  centeredPowerSeriesSumOnBall
    a
    c
    ρ
    (λ _ → fst poly)
    (polynomialPowerSeriesOnBallWith poly)
    x
    inBall
  ≡ powerSeriesPartialSum a (centeredDisplacement c x) (fst poly)
centeredPolynomialPowerSeriesSumOnBall-partialSum (N , zeroAfter) =
  centeredFiniteSupportPowerSeriesSumOnBall-partialSum N zeroAfter
