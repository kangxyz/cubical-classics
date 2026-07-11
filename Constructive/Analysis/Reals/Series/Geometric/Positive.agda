{-

Positive rational majorants for geometric series

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Series.Geometric.Positive where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.GeometricDecay.Modulus
open import Constructive.Analysis.GeometricDecay.Rate
  hiding
    ( scaledGeometricSegmentModulus
    ; scaledGeometricSegmentModulus-antitone
    ; scaled-target-cancel
    ; scaledGeometricSegmentUpperBound
    ; scaledGeometricSegment
    ; scaledGeometricSegment-radius
    ; scaledGeometricSegmentUpperBound⁺
    )
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.Series.Tail
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open import Constructive.Analysis.Reals.Series.Geometric.Rational


positiveGeometricTerm :
  ℚ⁺ →
  ℕ →
  ℝᶜ
positiveGeometricTerm ρ n =
  rational (radius (positivePower ρ n))


positiveGeometricTerm-nonnegative :
  (ρ : ℚ⁺) →
  (n : ℕ) →
  0ᶜ ≤ᶜ positiveGeometricTerm ρ n
positiveGeometricTerm-nonnegative ρ n =
  ≤ℚ→rational≤ᶜ
    {q = Rational.0ℚ}
    {r = radius (positivePower ρ n)}
    (ℚOrder.<Weaken≤
      Rational.0ℚ
      (radius (positivePower ρ n))
      (positivePower ρ n .snd))


private
  positiveGeometricTerm-rational :
    (ρ : ℚ⁺) →
    (n : ℕ) →
    positiveGeometricTerm ρ n ≡ rationalGeometricTerm (radius ρ) n
  positiveGeometricTerm-rational ρ n =
    cong rational (positivePower-radius ρ n)

  positiveGeometricTailSum-segment :
    (ρ : ℚ⁺) →
    (m k : ℕ) →
    tailSum (positiveGeometricTerm ρ) m k ≡
    rationalGeometricSegmentSumᶜ (radius ρ) m k
  positiveGeometricTailSum-segment ρ m k =
    cong
      (λ u → tailSum u m k)
      (funExt (positiveGeometricTerm-rational ρ)) ∙
    rationalGeometricSegmentTailSum (radius ρ) m k


positiveGeometricFiniteTailBoundFromRatio :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  TailBound
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
positiveGeometricFiniteTailBoundFromRatio ρ ρ<1 =
  nonnegative-tail-upper→TailBound
    (positiveGeometricTerm-nonnegative ρ)
    upper
  where
  upper :
    (ε : ℚ⁺) →
    (m k : ℕ) →
    NatOrder._≤_ (positiveGeometricPowerModulus ρ ρ<1 ε) m →
    tailSum (positiveGeometricTerm ρ) m k ≤ᶜ rational (radius ε)
  upper ε m k μ≤m =
    subst
      (λ x → x ≤ᶜ rational (radius ε))
      (sym (positiveGeometricTailSum-segment ρ m k))
      (≤ℚ→rational≤ᶜ
        (positiveGeometricSegmentUpperBoundFromRatio ρ ρ<1 ε m k μ≤m))
