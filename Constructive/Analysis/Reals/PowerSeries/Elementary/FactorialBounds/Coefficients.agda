{-

Positive-rational bounds for reciprocal factorials

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.FactorialBounds.Coefficients where

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (_,_)

open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  using (RationalClosedBoundᶜ ; rational-closed-boundᶜ)
open import Constructive.Data.PositiveRationals
  using (ℚ⁺ ; 1⁺)
import Constructive.Data.Rationals.Base as RationalBase
import Constructive.Data.Rationals.Factorial as Factorial


reciprocalFactorialClosedBoundOne :
  (n : ℕ) →
  RationalClosedBoundᶜ 1⁺ (Factorial.reciprocalFactorial n)
reciprocalFactorialClosedBoundOne n =
  rational-closed-boundᶜ
    (Factorial.reciprocalFactorial≤1 n)
    negative≤1
  where
  reciprocalNonnegative :
    RationalBase.0ℚ ℚOrder.≤ Factorial.reciprocalFactorial n
  reciprocalNonnegative =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = Factorial.reciprocalFactorial n}
      (Factorial.reciprocalFactorial-positive n)

  negative≤0 :
    ℚ.- Factorial.reciprocalFactorial n ℚOrder.≤ RationalBase.0ℚ
  negative≤0 =
    RationalBase.neg-nonpositive
      {q = Factorial.reciprocalFactorial n}
      reciprocalNonnegative

  0≤1 :
    RationalBase.0ℚ ℚOrder.≤ RationalBase.1ℚ
  0≤1 =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = RationalBase.1ℚ}
      RationalBase.0<1

  negative≤1 :
    ℚ.- Factorial.reciprocalFactorial n ℚOrder.≤ RationalBase.1ℚ
  negative≤1 =
    RationalBase.≤-trans
      {p = ℚ.- Factorial.reciprocalFactorial n}
      {q = RationalBase.0ℚ}
      {r = RationalBase.1ℚ}
      negative≤0
      0≤1


reciprocalFactorial⁺ :
  ℕ →
  ℚ⁺
reciprocalFactorial⁺ n =
  Factorial.reciprocalFactorial n ,
  Factorial.reciprocalFactorial-positive n


reciprocalFactorialClosedBoundSelf :
  (n : ℕ) →
  RationalClosedBoundᶜ (reciprocalFactorial⁺ n) (Factorial.reciprocalFactorial n)
reciprocalFactorialClosedBoundSelf n =
  rational-closed-boundᶜ
    (RationalBase.≤-refl reciprocal)
    negative≤reciprocal
  where
  reciprocal : ℚ
  reciprocal =
    Factorial.reciprocalFactorial n

  reciprocal-nonnegative :
    RationalBase.0ℚ ℚOrder.≤ reciprocal
  reciprocal-nonnegative =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = reciprocal}
      (Factorial.reciprocalFactorial-positive n)

  negative≤0 :
    ℚ.- reciprocal ℚOrder.≤ RationalBase.0ℚ
  negative≤0 =
    RationalBase.neg-nonpositive {q = reciprocal} reciprocal-nonnegative

  negative≤reciprocal :
    ℚ.- reciprocal ℚOrder.≤ reciprocal
  negative≤reciprocal =
    RationalBase.≤-trans
      {p = ℚ.- reciprocal}
      {q = RationalBase.0ℚ}
      {r = reciprocal}
      negative≤0
      reciprocal-nonnegative
