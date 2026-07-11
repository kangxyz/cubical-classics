{-

Part of Constructive.Analysis.Reals.PowerSeries.Elementary.Exponential

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.FactorialBounds.Tail where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Modulus using (AntitoneNatModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using (scalarMulᶜ-nonnegative ; scalarMulᶜ-pres≤ᶜ-scalar)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_ ; ≤ᶜ-refl)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.DerivativeData
  using (HasDerivativeAtWith)
open import Constructive.Analysis.Reals.Calculus.DerivativeRules
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Quantitative
  using (bounded-byᶜ-scale-rational-closed-bound)
open import Constructive.Analysis.GeometricDecay
open import Constructive.Analysis.Reals.Series.Geometric.Positive
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Power
  using (realPower)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( centeredPowerSeriesSumEverywhere-center
    ; constantPowerSeries
    ; constantPowerSeriesInfiniteRadius
    ; rationalScaleModulus
    ; rationalScaleModulus-antitone
    ; rationalScalePrecision
    ; rationalScalePrecision-mono
    ; rationalScaleTailBound
    ; subPowerSeries
    ; subPowerSeriesInfiniteRadius
    )
open import Constructive.Analysis.Reals.PowerSeries.FormalDerivative
  using
    ( derivativePowerSeries
    ; inverseSucReal
    ; naturalTimesInverseSucReal-cancel
    ; primitivePowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals
  using
    ( ℚ⁺
    ; 1⁺
    ; _+⁺_
    ; _*⁺_
    ; *⁺-comm
    ; *⁺-identity-left
    ; half⁺
    ; half<
    ; radius
    ; scalar-bound
    )
import Constructive.Data.Rationals.Base as RationalBase
import Constructive.Data.Rationals.Archimedean as Rational
import Constructive.Data.Rationals.Factorial as Factorial
import Constructive.Data.Rationals.Multiplication as RationalMul

open import Constructive.Analysis.Reals.PowerSeries.Elementary.FactorialBounds.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Elementary.FactorialBounds.Majorant

factorialMajorantCutoff :
  (ρ : ℚ⁺) →
  FactorialMajorantRatioCutoff ρ
factorialMajorantCutoff =
  factorialMajorantRatioCutoff


factorialMajorantCanonicalScale :
  ℚ⁺ →
  ℚ⁺
factorialMajorantCanonicalScale ρ =
  factorialMajorantScale ρ (factorialMajorantCutoff ρ)


factorialMajorantDropModulus :
  ℚ⁺ →
  ℚ⁺ →
  ℕ
factorialMajorantDropModulus ρ ε =
  rationalScaleModulus
    (radius (factorialMajorantCanonicalScale ρ))
    (positiveGeometricPowerModulus
      factorialHalfRatio
      factorialHalfRatio<1)
    ε


factorialMajorantModulus :
  ℚ⁺ →
  ℚ⁺ →
  ℕ
factorialMajorantModulus ρ ε =
  (factorialMajorantCutoff ρ .fst) Nat.+
  factorialMajorantDropModulus ρ ε


factorialMajorantDropTailBoundByScaledGeometric :
  (ρ : ℚ⁺) →
  (cutoff : FactorialMajorantRatioCutoff ρ) →
  TailBound
    (shift (cutoff .fst) (factorialMajorantTerm ρ))
    (rationalScaleModulus
      (radius (factorialMajorantScale ρ cutoff))
      (positiveGeometricPowerModulus
        factorialHalfRatio
        factorialHalfRatio<1))
factorialMajorantDropTailBoundByScaledGeometric ρ cutoff =
  comparisonTest
    (factorialMajorantDropMajorizedByScaledGeometric ρ cutoff)
    (factorialScaledGeometricTailBound
      (factorialMajorantScale ρ cutoff)
      factorialHalfRatio
      factorialHalfRatio<1)


factorialMajorantTailBound :
  (ρ : ℚ⁺) →
  TailBound
    (factorialMajorantTerm ρ)
    (factorialMajorantModulus ρ)
factorialMajorantTailBound ρ =
  tailBound-lift-shift
    {u = factorialMajorantTerm ρ}
    {μ = factorialMajorantDropModulus ρ}
    (factorialMajorantCutoff ρ .fst)
    shiftTail
  where
  shiftTail :
    TailBound
      (shift (factorialMajorantCutoff ρ .fst)
        (factorialMajorantTerm ρ))
      (factorialMajorantDropModulus ρ)
  shiftTail =
    factorialMajorantDropTailBoundByScaledGeometric
      ρ
      (factorialMajorantCutoff ρ)


factorialMajorantDropModulusAntitone :
  (ρ : ℚ⁺) →
  AntitoneNatModulus (factorialMajorantDropModulus ρ)
factorialMajorantDropModulusAntitone ρ {ε = ε} {δ = δ} ε≤δ =
  factorialScaledGeometricModulusAntitone
    (factorialMajorantCanonicalScale ρ)
    factorialHalfRatio
    factorialHalfRatio<1
    {ε = ε}
    {δ = δ}
    ε≤δ


factorialMajorantModulusAntitone :
  (ρ : ℚ⁺) →
  AntitoneNatModulus (factorialMajorantModulus ρ)
factorialMajorantModulusAntitone ρ {ε = ε} {δ = δ} ε≤δ =
  NatOrder.≤-k+
    (factorialMajorantDropModulusAntitone
      ρ
      {ε = ε}
      {δ = δ}
      ε≤δ)
