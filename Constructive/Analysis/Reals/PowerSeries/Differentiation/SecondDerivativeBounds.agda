{-

Finite-prefix bounds for power-series partial sums

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Differentiation.SecondDerivativeBounds where

open import Cubical.Foundations.Prelude

import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; suc ; zero)
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Data.Sum as Sum using (inl ; inr)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using (shiftPowerSeries ; powerSeriesPartialSum-shift)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.FormalDerivative
  using (derivativePowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Radius
  using (HasPowerSeriesOnBallWith)
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.UniformPartialSums
  using (PowerSeriesSecondDerivativePartialSumsBoundOnBallWith)
open import Constructive.Analysis.Reals.Series
  using (partialSum ; partialSum-append ; tailSum)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


PowerSeriesSecondDerivativePartialSumsBoundOnBall :
  PowerSeries →
  ℚ⁺ →
  Type₀
PowerSeriesSecondDerivativePartialSumsBoundOnBall a ρ =
  Σ[ Γ ∈ ℚ⁺ ]
    PowerSeriesSecondDerivativePartialSumsBoundOnBallWith a ρ Γ


private
  PowerSeriesPartialSumBoundedOnBallWith :
    PowerSeries →
    ℚ⁺ →
    ℕ →
    ℚ⁺ →
    Type₀
  PowerSeriesPartialSumBoundedOnBallWith a ρ n Γ =
    (y : ℝᶜ) →
    BoundedByᶜ ρ y →
    BoundedByᶜ Γ (powerSeriesPartialSum a y n)

  PowerSeriesPartialSumBoundedOnBall :
    PowerSeries →
    ℚ⁺ →
    ℕ →
    Type₀
  PowerSeriesPartialSumBoundedOnBall a ρ n =
    Σ[ Γ ∈ ℚ⁺ ] PowerSeriesPartialSumBoundedOnBallWith a ρ n Γ

  finitePartialSumBoundedOnBall :
    (a : PowerSeries) →
    (ρ : ℚ⁺) →
    (n : ℕ) →
    ∥ PowerSeriesPartialSumBoundedOnBall a ρ n ∥₁
  finitePartialSumBoundedOnBall a ρ zero =
    ∣ 1⁺ , (λ _ _ → bounded-byᶜ-zero 1⁺) ∣₁
  finitePartialSumBoundedOnBall a ρ (suc n) =
    Prop.rec
      squash₁
      coefficientCase
      (merely-boundedᶜ (a zero))
    where
    coefficientCase :
      Σ[ κ ∈ ℚ⁺ ] BoundedByᶜ κ (a zero) →
      ∥ PowerSeriesPartialSumBoundedOnBall a ρ (suc n) ∥₁
    coefficientCase (κ , a0-bound) =
      Prop.rec
        squash₁
        tailCase
        (finitePartialSumBoundedOnBall (shiftPowerSeries a) ρ n)
      where
      tailCase :
        PowerSeriesPartialSumBoundedOnBall (shiftPowerSeries a) ρ n →
        ∥ PowerSeriesPartialSumBoundedOnBall a ρ (suc n) ∥₁
      tailCase (Γ , tailBound) =
        ∣ κ +⁺ (ρ *⁺ Γ) , bound ∣₁
        where
        bound :
          PowerSeriesPartialSumBoundedOnBallWith
            a
            ρ
            (suc n)
            (κ +⁺ (ρ *⁺ Γ))
        bound y y-bound =
          subst
            (BoundedByᶜ (κ +⁺ (ρ *⁺ Γ)))
            (sym (powerSeriesPartialSum-shift a y n))
            shiftedBound
          where
          shiftedTail : ℝᶜ
          shiftedTail =
            powerSeriesPartialSum (shiftPowerSeries a) y n

          productBound :
            BoundedByᶜ (ρ *⁺ Γ) (y ·ᶜ shiftedTail)
          productBound =
            bounded-byᶜ-mul
              ρ
              Γ
              y
              shiftedTail
              y-bound
              (tailBound y y-bound)

          shiftedBound :
            BoundedByᶜ
              (κ +⁺ (ρ *⁺ Γ))
              (a zero +ᶜ y ·ᶜ shiftedTail)
          shiftedBound =
            bounded-byᶜ-add
              κ
              (ρ *⁺ Γ)
              (a zero)
              (y ·ᶜ shiftedTail)
              a0-bound
              productBound

  PowerSeriesPartialSumsPrefixBoundedOnBallWith :
    PowerSeries →
    ℚ⁺ →
    ℕ →
    ℚ⁺ →
    Type₀
  PowerSeriesPartialSumsPrefixBoundedOnBallWith a ρ m Γ =
    (y : ℝᶜ) →
    BoundedByᶜ ρ y →
    (n : ℕ) →
    NatOrder._≤_ n m →
    BoundedByᶜ Γ (powerSeriesPartialSum a y n)

  PowerSeriesPartialSumsPrefixBoundedOnBall :
    PowerSeries →
    ℚ⁺ →
    ℕ →
    Type₀
  PowerSeriesPartialSumsPrefixBoundedOnBall a ρ m =
    Σ[ Γ ∈ ℚ⁺ ]
      PowerSeriesPartialSumsPrefixBoundedOnBallWith a ρ m Γ

  finitePartialSumsPrefixBoundedOnBall :
    (a : PowerSeries) →
    (ρ : ℚ⁺) →
    (m : ℕ) →
    ∥ PowerSeriesPartialSumsPrefixBoundedOnBall a ρ m ∥₁
  finitePartialSumsPrefixBoundedOnBall a ρ zero =
    ∣ 1⁺ , bound ∣₁
    where
    bound :
      PowerSeriesPartialSumsPrefixBoundedOnBallWith a ρ zero 1⁺
    bound y y-bound n n≤0 =
      subst
        (λ k → BoundedByᶜ 1⁺ (powerSeriesPartialSum a y k))
        (sym (NatOrder.≤0→≡0 n≤0))
        (bounded-byᶜ-zero 1⁺)
  finitePartialSumsPrefixBoundedOnBall a ρ (suc m) =
    Prop.rec
      squash₁
      prefixCase
      (finitePartialSumsPrefixBoundedOnBall a ρ m)
    where
    prefixCase :
      PowerSeriesPartialSumsPrefixBoundedOnBall a ρ m →
      ∥ PowerSeriesPartialSumsPrefixBoundedOnBall a ρ (suc m) ∥₁
    prefixCase (Γ , prefixBound) =
      Prop.rec
        squash₁
        lastCase
        (finitePartialSumBoundedOnBall a ρ (suc m))
      where
      lastCase :
        PowerSeriesPartialSumBoundedOnBall a ρ (suc m) →
        ∥ PowerSeriesPartialSumsPrefixBoundedOnBall a ρ (suc m) ∥₁
      lastCase (Λ , lastBound) =
        ∣ Γ +⁺ Λ , bound ∣₁
        where
        Γ≤Γ+Λ : radius Γ ℚOrder.≤ radius (Γ +⁺ Λ)
        Γ≤Γ+Λ =
          Rational.<→≤
            {p = radius Γ}
            {q = radius (Γ +⁺ Λ)}
            (summand-left<sum Γ Λ)

        Λ≤Γ+Λ : radius Λ ℚOrder.≤ radius (Γ +⁺ Λ)
        Λ≤Γ+Λ =
          Rational.<→≤
            {p = radius Λ}
            {q = radius (Γ +⁺ Λ)}
            (summand-right<sum Γ Λ)

        bound :
          PowerSeriesPartialSumsPrefixBoundedOnBallWith
            a
            ρ
            (suc m)
            (Γ +⁺ Λ)
        bound y y-bound n n≤sucm =
          Sum.rec left right (NatOrder.≤-split n≤sucm)
          where
          left :
            n NatOrder.< suc m →
            BoundedByᶜ (Γ +⁺ Λ) (powerSeriesPartialSum a y n)
          left n<sucm =
            bounded-byᶜ-monotone
              Γ≤Γ+Λ
              (prefixBound
                y
                y-bound
                n
                (NatOrder.pred-≤-pred n<sucm))

          right :
            n ≡ suc m →
            BoundedByᶜ (Γ +⁺ Λ) (powerSeriesPartialSum a y n)
          right n≡sucm =
            bounded-byᶜ-monotone
              Λ≤Γ+Λ
              (subst
                (λ k → BoundedByᶜ Λ (powerSeriesPartialSum a y k))
                (sym n≡sucm)
                (lastBound y y-bound))


partialSumBoundOnBallFromConvergence :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesOnBallWith a ρ μ →
  ∥ Σ[ Γ ∈ ℚ⁺ ]
      ((y : ℝᶜ) →
      BoundedByᶜ ρ y →
      (n : ℕ) →
      BoundedByᶜ Γ (powerSeriesPartialSum a y n)) ∥₁
partialSumBoundOnBallFromConvergence {a = a} {ρ = ρ} {μ = μ} convergence =
  Prop.rec
    squash₁
    prefixCase
    (finitePartialSumsPrefixBoundedOnBall a ρ (μ 1⁺))
  where
  prefixCase :
    PowerSeriesPartialSumsPrefixBoundedOnBall a ρ (μ 1⁺) →
    ∥ Σ[ Γ ∈ ℚ⁺ ]
        ((y : ℝᶜ) →
        BoundedByᶜ ρ y →
        (n : ℕ) →
        BoundedByᶜ Γ (powerSeriesPartialSum a y n)) ∥₁
  prefixCase (Γ , prefixBound) =
    ∣ Γ +⁺ 1⁺ , bound ∣₁
    where
    cutoff : ℕ
    cutoff =
      μ 1⁺

    Γ≤Γ+1 : radius Γ ℚOrder.≤ radius (Γ +⁺ 1⁺)
    Γ≤Γ+1 =
      Rational.<→≤
        {p = radius Γ}
        {q = radius (Γ +⁺ 1⁺)}
        (summand-left<sum Γ 1⁺)

    tailBound :
      (y : ℝᶜ) →
      BoundedByᶜ ρ y →
      (k : ℕ) →
      BoundedByᶜ 1⁺ (tailSum (powerSeriesTerm a y) cutoff k)
    tailBound y y-bound k =
      HasPowerSeriesOnBallWith.tailBound
        convergence
        y
        y-bound
        1⁺
        cutoff
        k
        NatOrder.≤-refl

    tailCase :
      (y : ℝᶜ) →
      BoundedByᶜ ρ y →
      (n : ℕ) →
      cutoff NatOrder.< n →
      BoundedByᶜ (Γ +⁺ 1⁺) (powerSeriesPartialSum a y n)
    tailCase y y-bound n cutoff<n =
      subst
        (BoundedByᶜ (Γ +⁺ 1⁺))
        (sym sum-path)
        combined
      where
      u : ℕ → ℝᶜ
      u =
        powerSeriesTerm a y

      cutoff≤n : NatOrder._≤_ cutoff n
      cutoff≤n =
        NatOrder.<-weaken cutoff<n

      k : ℕ
      k =
        cutoff≤n .fst

      cutoff+k≡n : cutoff Nat.+ k ≡ n
      cutoff+k≡n =
        Nat.+-comm cutoff k ∙ cutoff≤n .snd

      sum-path :
        powerSeriesPartialSum a y n ≡
        powerSeriesPartialSum a y cutoff +ᶜ tailSum u cutoff k
      sum-path =
        sym (cong (partialSum u) cutoff+k≡n) ∙
        partialSum-append u cutoff k

      combined :
        BoundedByᶜ
          (Γ +⁺ 1⁺)
          (powerSeriesPartialSum a y cutoff +ᶜ tailSum u cutoff k)
      combined =
        bounded-byᶜ-add
          Γ
          1⁺
          (powerSeriesPartialSum a y cutoff)
          (tailSum u cutoff k)
          (prefixBound y y-bound cutoff NatOrder.≤-refl)
          (tailBound y y-bound k)

    bound :
      (y : ℝᶜ) →
      BoundedByᶜ ρ y →
      (n : ℕ) →
      BoundedByᶜ (Γ +⁺ 1⁺) (powerSeriesPartialSum a y n)
    bound y y-bound n =
      Sum.rec left right (NatOrder.splitℕ-≤ n cutoff)
      where
      left :
        NatOrder._≤_ n cutoff →
        BoundedByᶜ (Γ +⁺ 1⁺) (powerSeriesPartialSum a y n)
      left n≤cutoff =
        bounded-byᶜ-monotone
          Γ≤Γ+1
          (prefixBound y y-bound n n≤cutoff)

      right :
        cutoff NatOrder.< n →
        BoundedByᶜ (Γ +⁺ 1⁺) (powerSeriesPartialSum a y n)
      right cutoff<n =
        tailCase y y-bound n cutoff<n


powerSeriesSecondDerivativePartialSumsBoundOnBallFromConvergence :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesOnBallWith
    (derivativePowerSeries (derivativePowerSeries a))
    ρ
    μ →
  ∥ PowerSeriesSecondDerivativePartialSumsBoundOnBall a ρ ∥₁
powerSeriesSecondDerivativePartialSumsBoundOnBallFromConvergence {a = a} convergence =
  partialSumBoundOnBallFromConvergence
    {a = derivativePowerSeries (derivativePowerSeries a)}
    convergence
