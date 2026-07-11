{-

Basic coefficient bounds shared by elementary power series

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.CoefficientBounds where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
  using (0ᶜ ; 1ᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  using
    ( BoundedByᶜ
    ; rational-closed-boundᶜ
    ; rational-closed-bound→boundedᶜ
    )
open import Constructive.Analysis.Reals.PowerSeries.FormalDerivative
  using (inverseSucReal ; primitivePowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Base
  using (PowerSeries)
open import Constructive.Data.PositiveRationals
  using (ℚ⁺ ; 1⁺ ; *⁺-identity-left ; radius)
import Constructive.Data.Rationals.Archimedean as Rational
import Constructive.Data.Rationals.Base as RationalBase
import Constructive.Data.Rationals.Factorial as Factorial


zeroBoundOne :
  BoundedByᶜ 1⁺ 0ᶜ
zeroBoundOne =
  rational-closed-bound→boundedᶜ
    1⁺
    RationalBase.0ℚ
    (rational-closed-boundᶜ 0≤1 0≤1)
  where
  0≤1 :
    RationalBase.0ℚ ℚOrder.≤ RationalBase.1ℚ
  0≤1 =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = RationalBase.1ℚ}
      RationalBase.0<1


oneBoundOne :
  BoundedByᶜ 1⁺ 1ᶜ
oneBoundOne =
  rational-closed-bound→boundedᶜ
    1⁺
    RationalBase.1ℚ
    (rational-closed-boundᶜ 1≤1 -1≤1)
  where
  1≤1 :
    RationalBase.1ℚ ℚOrder.≤ RationalBase.1ℚ
  1≤1 =
    RationalBase.≤-refl RationalBase.1ℚ

  -1≤1 :
    ℚ.- RationalBase.1ℚ ℚOrder.≤ RationalBase.1ℚ
  -1≤1 =
    RationalBase.<→≤
      {p = RationalBase.-1ℚ}
      {q = RationalBase.1ℚ}
      (ℚOrder.isTrans<
        RationalBase.-1ℚ
        RationalBase.0ℚ
        RationalBase.1ℚ
        RationalBase.-1<0
        RationalBase.0<1)


inverseSucRealBoundOne :
  (n : ℕ) →
  BoundedByᶜ 1⁺ (inverseSucReal n)
inverseSucRealBoundOne n =
  rational-closed-bound→boundedᶜ
    1⁺
    inverse
    (rational-closed-boundᶜ inverse≤1 negative≤1)
  where
  inverse : ℚ
  inverse =
    Rational.divideBySuc RationalBase.1ℚ n

  unit : ℚ
  unit =
    Rational.unitFraction n

  inverse≡unit :
    inverse ≡ unit
  inverse≡unit =
    Rational.divideBySuc-as-unitFraction RationalBase.1ℚ n ∙
    ℚ.·IdL unit

  inverse≤1 :
    inverse ℚOrder.≤ RationalBase.1ℚ
  inverse≤1 =
    subst
      (λ q → q ℚOrder.≤ RationalBase.1ℚ)
      (sym inverse≡unit)
      (Factorial.unitFraction≤1 n)

  inverseNonnegative :
    RationalBase.0ℚ ℚOrder.≤ inverse
  inverseNonnegative =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = inverse}
      (Rational.divideBySuc-positive
        {q = RationalBase.1ℚ}
        RationalBase.0<1
        n)

  negative≤0 :
    ℚ.- inverse ℚOrder.≤ RationalBase.0ℚ
  negative≤0 =
    RationalBase.neg-nonpositive
      {q = inverse}
      inverseNonnegative

  0≤1 :
    RationalBase.0ℚ ℚOrder.≤ RationalBase.1ℚ
  0≤1 =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = RationalBase.1ℚ}
      RationalBase.0<1

  negative≤1 :
    ℚ.- inverse ℚOrder.≤ RationalBase.1ℚ
  negative≤1 =
    RationalBase.≤-trans
      {p = ℚ.- inverse}
      {q = RationalBase.0ℚ}
      {r = RationalBase.1ℚ}
      negative≤0
      0≤1


zeroBound :
  (κ : ℚ⁺) →
  BoundedByᶜ κ 0ᶜ
zeroBound κ =
  rational-closed-bound→boundedᶜ
    κ
    RationalBase.0ℚ
    (rational-closed-boundᶜ 0≤κ 0≤κ)
  where
  0≤κ :
    RationalBase.0ℚ ℚOrder.≤ radius κ
  0≤κ =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = radius κ}
      (κ .snd)


primitivePowerSeriesCoefficientBoundOne :
  (a : PowerSeries) →
  ((n : ℕ) → BoundedByᶜ 1⁺ (a n)) →
  (n : ℕ) →
  BoundedByᶜ 1⁺ (primitivePowerSeries a n)
primitivePowerSeriesCoefficientBoundOne a coefficientBound zero =
  zeroBoundOne
primitivePowerSeriesCoefficientBoundOne a coefficientBound (suc n) =
  subst
    (λ κ → BoundedByᶜ κ (primitivePowerSeries a (suc n)))
    (*⁺-identity-left 1⁺)
    (bounded-byᶜ-mul
      1⁺
      1⁺
      (inverseSucReal n)
      (a n)
      (inverseSucRealBoundOne n)
      (coefficientBound n))
