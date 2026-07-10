{-

Part of Constructive.Analysis.Reals.PowerSeries.Instances.Exponential

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Exponential.Tail where

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
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (scalarMulᶜ-nonnegative ; scalarMulᶜ-pres≤ᶜ-scalar)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_ ; ≤ᶜ-refl)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.Derivative.Base
  using (HasDerivativeAtWith)
open import Constructive.Analysis.Reals.Calculus.Derivative.Rules
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Estimates
  using (bounded-byᶜ-scale-rational-closed-bound)
open import Constructive.Analysis.GeometricDecay
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
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
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using
    ( derivativePowerSeries
    ; inverseSucReal
    ; naturalTimesInverseSucReal-cancel
    ; primitivePowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative
  using
    ( PowerSeriesIteratedFormalPartialDerivativeBounds
    ; PowerSeriesPartialSumsDerivativeModulusLarge
    ; centeredPowerSeriesHasDerivativeFromIteratedBounds
    ; positivePartialSum
    ; powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
    ; powerSeriesFormalPartialSumsDerivativeModulus
    ; termwiseConvergenceIndex
    )
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

open import Constructive.Analysis.Reals.PowerSeries.Instances.Exponential.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Instances.Exponential.Majorant

expPositiveMajorantFactorialCutoff :
  (ρ : ℚ⁺) →
  ExpMajorantRatioCutoff ρ
expPositiveMajorantFactorialCutoff =
  expMajorantRatioCutoff


expPositiveMajorantFactorialScale :
  ℚ⁺ →
  ℚ⁺
expPositiveMajorantFactorialScale ρ =
  expMajorantScale ρ (expPositiveMajorantFactorialCutoff ρ)


expPositiveMajorantFactorialDropModulus :
  ℚ⁺ →
  ℚ⁺ →
  ℕ
expPositiveMajorantFactorialDropModulus ρ ε =
  rationalScaleModulus
    (radius (expPositiveMajorantFactorialScale ρ))
    (positiveGeometricPowerModulus
      expPositiveHalfRatio
      expPositiveHalfRatio<1)
    ε


expPositiveMajorantFactorialModulus :
  ℚ⁺ →
  ℚ⁺ →
  ℕ
expPositiveMajorantFactorialModulus ρ ε =
  (expPositiveMajorantFactorialCutoff ρ .fst) Nat.+
  expPositiveMajorantFactorialDropModulus ρ ε


expMajorantDropTailBoundByScaledGeometric :
  (ρ : ℚ⁺) →
  (cutoff : ExpMajorantRatioCutoff ρ) →
  TailBound
    (drop (cutoff .fst) (expPositiveMajorantTerm ρ))
    (rationalScaleModulus
      (radius (expMajorantScale ρ cutoff))
      (positiveGeometricPowerModulus
        expPositiveHalfRatio
        expPositiveHalfRatio<1))
expMajorantDropTailBoundByScaledGeometric ρ cutoff =
  comparisonTest
    (expMajorantDropMajorizedByScaledGeometric ρ cutoff)
    (expScaledGeometricTailBound
      (expMajorantScale ρ cutoff)
      expPositiveHalfRatio
      expPositiveHalfRatio<1)


expPositiveMajorantFactorialTailBound :
  (ρ : ℚ⁺) →
  TailBound
    (expPositiveMajorantTerm ρ)
    (expPositiveMajorantFactorialModulus ρ)
expPositiveMajorantFactorialTailBound ρ =
  tailBound-lift-drop
    {u = expPositiveMajorantTerm ρ}
    {μ = expPositiveMajorantFactorialDropModulus ρ}
    (expPositiveMajorantFactorialCutoff ρ .fst)
    dropTail
  where
  dropTail :
    TailBound
      (drop (expPositiveMajorantFactorialCutoff ρ .fst)
        (expPositiveMajorantTerm ρ))
      (expPositiveMajorantFactorialDropModulus ρ)
  dropTail =
    expMajorantDropTailBoundByScaledGeometric
      ρ
      (expPositiveMajorantFactorialCutoff ρ)


expPositiveMajorantFactorialDropModulusAntitone :
  (ρ : ℚ⁺) →
  AntitoneNatModulus (expPositiveMajorantFactorialDropModulus ρ)
expPositiveMajorantFactorialDropModulusAntitone ρ {ε = ε} {δ = δ} ε≤δ =
  expScaledGeometricModulusAntitone
    (expPositiveMajorantFactorialScale ρ)
    expPositiveHalfRatio
    expPositiveHalfRatio<1
    {ε = ε}
    {δ = δ}
    ε≤δ


expPositiveMajorantFactorialModulusAntitone :
  (ρ : ℚ⁺) →
  AntitoneNatModulus (expPositiveMajorantFactorialModulus ρ)
expPositiveMajorantFactorialModulusAntitone ρ {ε = ε} {δ = δ} ε≤δ =
  NatOrder.≤-k+
    (expPositiveMajorantFactorialDropModulusAntitone
      ρ
      {ε = ε}
      {δ = δ}
      ε≤δ)


expPowerSeriesTerm-scalarReciprocal :
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesTerm expPowerSeries h n ≡
  scalarMulᶜ (Factorial.reciprocalFactorial n) (realPower h n)
expPowerSeriesTerm-scalarReciprocal h n =
  cong
    (_·ᶜ realPower h n)
    (expPowerSeries-reciprocalFactorial n) ∙
  mulᶜ-rational-left
    (Factorial.reciprocalFactorial n)
    (realPower h n)




expPowerSeriesTermBoundByPositiveMajorant :
  (ρ : ℚ⁺) →
  (h : ℝᶜ) →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower h n) →
  BoundedByᶜ (expPositiveMajorantRadius ρ n)
    (powerSeriesTerm expPowerSeries h n)
expPowerSeriesTermBoundByPositiveMajorant ρ h n powerBound =
  subst2
    BoundedByᶜ
    (*⁺-comm (reciprocalFactorial⁺ n) (positivePower ρ n))
    (sym (expPowerSeriesTerm-scalarReciprocal h n))
    (bounded-byᶜ-scale-rational-closed-bound
      (Factorial.reciprocalFactorial n)
      (positivePower ρ n)
      (reciprocalFactorial⁺ n)
      (realPower h n)
      (reciprocalFactorialClosedBoundSelf n)
      powerBound)
