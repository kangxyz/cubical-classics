{-

Formal exponential power-series coefficients

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Exponential where

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
open import Constructive.Analysis.Reals.Calculus.Derivative
  using (HasDerivativeAtWith)
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Majorant
  using
    ( bounded-byᶜ-abs
    ; bounded-byᶜ-scale-rational-closed-bound
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
  using
    ( positiveGeometricPowerModulus
    ; positiveGeometricPowerModulus-antitone
    ; positiveGeometricFiniteTailBoundFromRatio
    ; positiveGeometricTerm
    ; positiveGeometricTerm-nonnegative
    ; positivePower
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using
    ( RealGeometricBound
    ; RealGeometricPowerBounds
    ; realGeometricPowerBoundsFromBound
    ; realPowerBoundsFromBound
    ; realPower
    )
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
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence
  using
    ( derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    ; primitivePowerSeriesInfiniteRadiusFromCoefficientPath
    )
open import Constructive.Analysis.Reals.PowerSeries.Analytic
  using
    ( AnalyticAt
    ; HasPowerSeriesAt
    ; HasPowerSeriesAtOnBall
    ; HasPowerSeriesAtWith
    ; centeredPowerSeriesSumEverywhereAnalyticAt
    ; centeredPowerSeriesSumEverywhereHasPowerSeriesAt
    ; centeredPowerSeriesSumEverywhereHasPowerSeriesAtOnBall
    ; centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative
  using
    ( PowerSeriesIteratedFormalPartialDerivativeBounds
    ; PowerSeriesPartialSumsDerivativeModulusLarge
    ; centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
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


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    exp-majorant-step :
      (ρ p r u : 𝓡 .fst) →
      (ρ · p) · (r · u) ≡ (ρ · u) · (p · r)
    exp-majorant-step _ _ _ _ =
      solve! 𝓡

    exp-geometric-scale-step :
      (h s p : 𝓡 .fst) →
      h · (s · p) ≡ s · (h · p)
    exp-geometric-scale-step _ _ _ =
      solve! 𝓡


expPowerSeries :
  PowerSeries
expPowerSeries zero =
  1ᶜ
expPowerSeries (suc n) =
  inverseSucReal n ·ᶜ expPowerSeries n


expPowerSeriesCoefficient-zero :
  expPowerSeries zero ≡ 1ᶜ
expPowerSeriesCoefficient-zero =
  refl


expPowerSeriesCoefficient-suc :
  (n : ℕ) →
  expPowerSeries (suc n) ≡
  inverseSucReal n ·ᶜ expPowerSeries n
expPowerSeriesCoefficient-suc n =
  refl


inverseSucReal-rational :
  (n : ℕ) →
  (q : ℚ) →
  inverseSucReal n ·ᶜ rational q ≡
  rational (Rational.divideBySuc q n)
inverseSucReal-rational n q =
  mulᶜ-rational-rational inverse q ∙
  cong rational inverse-times-q≡q-div
  where
  inverse : ℚ
  inverse =
    Rational.divideBySuc RationalBase.1ℚ n

  unit : ℚ
  unit =
    Rational.unitFraction n

  inverse≡unit : inverse ≡ unit
  inverse≡unit =
    Rational.divideBySuc-as-unitFraction RationalBase.1ℚ n ∙
    ℚ.·IdL unit

  inverse-times-q≡q-div :
    inverse ℚ.· q ≡ Rational.divideBySuc q n
  inverse-times-q≡q-div =
    cong (λ r → r ℚ.· q) inverse≡unit ∙
    ℚ.·Comm unit q ∙
    sym (Rational.divideBySuc-as-unitFraction q n)


expPowerSeries-reciprocalFactorial :
  (n : ℕ) →
  expPowerSeries n ≡
  rational (Factorial.reciprocalFactorial n)
expPowerSeries-reciprocalFactorial zero =
  refl
expPowerSeries-reciprocalFactorial (suc n) =
  cong
    (inverseSucReal n ·ᶜ_)
    (expPowerSeries-reciprocalFactorial n) ∙
  inverseSucReal-rational n (Factorial.reciprocalFactorial n)


expPowerSeries-divideByFactorial :
  (n : ℕ) →
  expPowerSeries n ≡
  rational (Factorial.divideByFactorial RationalBase.1ℚ n)
expPowerSeries-divideByFactorial n =
  expPowerSeries-reciprocalFactorial n ∙
  cong rational (sym (Factorial.divideByFactorial-one n))


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


expPowerSeriesCoefficientBoundOne :
  (n : ℕ) →
  BoundedByᶜ 1⁺ (expPowerSeries n)
expPowerSeriesCoefficientBoundOne n =
  subst
    (BoundedByᶜ 1⁺)
    (sym (expPowerSeries-reciprocalFactorial n))
    (rational-closed-bound→boundedᶜ
      1⁺
      (Factorial.reciprocalFactorial n)
      (reciprocalFactorialClosedBoundOne n))


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


expPositiveMajorantRadius :
  ℚ⁺ →
  ℕ →
  ℚ⁺
expPositiveMajorantRadius ρ n =
  positivePower ρ n *⁺ reciprocalFactorial⁺ n


expPositiveMajorantTerm :
  ℚ⁺ →
  ℕ →
  ℝᶜ
expPositiveMajorantTerm ρ n =
  rational (radius (expPositiveMajorantRadius ρ n))


expPositiveMajorantRadius-step :
  (ρ : ℚ⁺) →
  (n : ℕ) →
  radius (expPositiveMajorantRadius ρ (suc n)) ≡
  (radius ρ ℚ.· Rational.unitFraction n) ℚ.·
  radius (expPositiveMajorantRadius ρ n)
expPositiveMajorantRadius-step ρ n =
  cong
    (λ r → radius (positivePower ρ (suc n)) ℚ.· r)
    (Factorial.reciprocalFactorial-suc n) ∙
  cong
    (λ r → radius (positivePower ρ (suc n)) ℚ.· r)
    (Rational.divideBySuc-as-unitFraction reciprocal n) ∙
  SolverHelpers.exp-majorant-step
    ℚCommRing
    (radius ρ)
    (radius (positivePower ρ n))
    reciprocal
    unit
  where
  reciprocal : ℚ
  reciprocal =
    Factorial.reciprocalFactorial n

  unit : ℚ
  unit =
    Rational.unitFraction n


expPositiveMajorantTerm-step :
  (ρ : ℚ⁺) →
  (n : ℕ) →
  expPositiveMajorantTerm ρ (suc n) ≡
  scalarMulᶜ
    (radius ρ ℚ.· Rational.unitFraction n)
    (expPositiveMajorantTerm ρ n)
expPositiveMajorantTerm-step ρ n =
  cong rational radius-step ∙
  sym (scalarMulᶜ-rational coefficient base)
  where
  coefficient : ℚ
  coefficient =
    radius ρ ℚ.· Rational.unitFraction n

  base : ℚ
  base =
    radius (expPositiveMajorantRadius ρ n)

  radius-step :
    radius (expPositiveMajorantRadius ρ (suc n)) ≡
    coefficient ℚ.· base
  radius-step =
    expPositiveMajorantRadius-step ρ n


expPositiveMajorantTerm-nonnegative :
  (ρ : ℚ⁺) →
  (n : ℕ) →
  0ᶜ ≤ᶜ expPositiveMajorantTerm ρ n
expPositiveMajorantTerm-nonnegative ρ n =
  ≤ℚ→rational≤ᶜ
    {q = RationalBase.0ℚ}
    {r = radius (expPositiveMajorantRadius ρ n)}
    (ℚOrder.<Weaken≤
      RationalBase.0ℚ
      (radius (expPositiveMajorantRadius ρ n))
      (expPositiveMajorantRadius ρ n .snd))


expMajorantCoefficientDouble≤1 :
  (ρ : ℚ⁺) →
  (n : ℕ) →
  radius ρ ℚ.+ radius ρ ℚOrder.≤
    Rational.natMul (suc n) RationalBase.1ℚ →
  (radius ρ ℚ.· Rational.unitFraction n) ℚ.+
  (radius ρ ℚ.· Rational.unitFraction n)
    ℚOrder.≤ RationalBase.1ℚ
expMajorantCoefficientDouble≤1 ρ n double≤natural =
  subst2
    ℚOrder._≤_
    double-coefficient-path
    natural-unit-path
    double-unit≤natural-unit
  where
  unit : ℚ
  unit =
    Rational.unitFraction n

  natural : ℚ
  natural =
    Rational.natMul (suc n) RationalBase.1ℚ

  unit-nonnegative :
    RationalBase.0ℚ ℚOrder.≤ unit
  unit-nonnegative =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = unit}
      (Rational.unitFraction-positive n)

  double-unit≤natural-unit :
    (radius ρ ℚ.+ radius ρ) ℚ.· unit ℚOrder.≤ natural ℚ.· unit
  double-unit≤natural-unit =
    ℚOrder.≤-·o
      (radius ρ ℚ.+ radius ρ)
      natural
      unit
      unit-nonnegative
      double≤natural

  double-coefficient-path :
    (radius ρ ℚ.+ radius ρ) ℚ.· unit ≡
    (radius ρ ℚ.· unit) ℚ.+ (radius ρ ℚ.· unit)
  double-coefficient-path =
    ℚ.·DistR+ (radius ρ) (radius ρ) unit

  natural-unit-path :
    natural ℚ.· unit ≡ RationalBase.1ℚ
  natural-unit-path =
    ℚ.·Comm natural unit ∙
    sym (Rational.natMul-mul-left (suc n) unit RationalBase.1ℚ) ∙
    cong (Rational.natMul (suc n)) (ℚ.·IdR unit) ∙
    Rational.natMul-unitFraction n


expMajorantCoefficient≤half :
  (ρ : ℚ⁺) →
  (n : ℕ) →
  radius ρ ℚ.+ radius ρ ℚOrder.≤
    Rational.natMul (suc n) RationalBase.1ℚ →
  radius ρ ℚ.· Rational.unitFraction n ℚOrder.≤ radius (half⁺ 1⁺)
expMajorantCoefficient≤half ρ n double≤natural =
  subst
    (λ q → q ℚOrder.≤ radius (half⁺ 1⁺))
    (RationalBase.double-half coefficient)
    scaled≤half
  where
  coefficient : ℚ
  coefficient =
    radius ρ ℚ.· Rational.unitFraction n

  coefficient-double≤1 :
    coefficient ℚ.+ coefficient ℚOrder.≤ RationalBase.1ℚ
  coefficient-double≤1 =
    expMajorantCoefficientDouble≤1 ρ n double≤natural

  half-nonnegative :
    RationalBase.0ℚ ℚOrder.≤ RationalBase.1/2
  half-nonnegative =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = RationalBase.1/2}
      RationalBase.0<1/2

  scaled≤half :
    (coefficient ℚ.+ coefficient) ℚ.· RationalBase.1/2
      ℚOrder.≤ radius (half⁺ 1⁺)
  scaled≤half =
    ℚOrder.≤-·o
      (coefficient ℚ.+ coefficient)
      RationalBase.1ℚ
      RationalBase.1/2
      half-nonnegative
      coefficient-double≤1


expPositiveMajorantTerm-ratio-half :
  (ρ : ℚ⁺) →
  (n : ℕ) →
  (radius ρ ℚ.+ radius ρ) ℚOrder.≤
    Rational.natMul (suc n) RationalBase.1ℚ →
  expPositiveMajorantTerm ρ (suc n) +ᶜ
  expPositiveMajorantTerm ρ (suc n) ≤ᶜ
  expPositiveMajorantTerm ρ n
expPositiveMajorantTerm-ratio-half ρ n double≤natural =
  subst
    (λ x → x ≤ᶜ term)
    (sym doubled-step-path)
    scaled≤term
  where
  coefficient : ℚ
  coefficient =
    radius ρ ℚ.· Rational.unitFraction n

  term : ℝᶜ
  term =
    expPositiveMajorantTerm ρ n

  coefficient-double≤1 :
    coefficient ℚ.+ coefficient ℚOrder.≤ RationalBase.1ℚ
  coefficient-double≤1 =
    expMajorantCoefficientDouble≤1 ρ n double≤natural

  doubled-step-path :
    expPositiveMajorantTerm ρ (suc n) +ᶜ
    expPositiveMajorantTerm ρ (suc n) ≡
    scalarMulᶜ (coefficient ℚ.+ coefficient) term
  doubled-step-path =
    cong₂
      _+ᶜ_
      (expPositiveMajorantTerm-step ρ n)
      (expPositiveMajorantTerm-step ρ n) ∙
    sym (scalarMulᶜ-distrib-scalar-add coefficient coefficient term)

  scaled≤one-scaled :
    scalarMulᶜ (coefficient ℚ.+ coefficient) term ≤ᶜ
    scalarMulᶜ RationalBase.1ℚ term
  scaled≤one-scaled =
    scalarMulᶜ-pres≤ᶜ-scalar
      {a = coefficient ℚ.+ coefficient}
      {b = RationalBase.1ℚ}
      coefficient-double≤1
      {x = term}
      (expPositiveMajorantTerm-nonnegative ρ n)

  scaled≤term :
    scalarMulᶜ (coefficient ℚ.+ coefficient) term ≤ᶜ term
  scaled≤term =
    subst
      (λ x → scalarMulᶜ (coefficient ℚ.+ coefficient) term ≤ᶜ x)
      (scalarMulᶜ-one term)
      scaled≤one-scaled


ExpMajorantRatioCutoff :
  ℚ⁺ →
  Type₀
ExpMajorantRatioCutoff ρ =
  Σ[ N ∈ ℕ ]
    ((n : ℕ) →
      NatOrder._≤_ N n →
      (radius ρ ℚ.+ radius ρ) ℚOrder.≤
        Rational.natMul (suc n) RationalBase.1ℚ)


expMajorantRatioCutoff :
  (ρ : ℚ⁺) →
  ExpMajorantRatioCutoff ρ
expMajorantRatioCutoff ρ =
  N , cutoff
  where
  doubleρ : ℚ
  doubleρ =
    radius ρ ℚ.+ radius ρ

  cutoffData :
    Σ[ N ∈ ℕ ]
      doubleρ ℚOrder.< Rational.natMul N RationalBase.1ℚ
  cutoffData =
    Rational.archimedean doubleρ RationalBase.1ℚ RationalBase.0<1

  N : ℕ
  N =
    cutoffData .fst

  N-large :
    doubleρ ℚOrder.< Rational.natMul N RationalBase.1ℚ
  N-large =
    cutoffData .snd

  cutoff :
    (n : ℕ) →
    NatOrder._≤_ N n →
    doubleρ ℚOrder.≤ Rational.natMul (suc n) RationalBase.1ℚ
  cutoff n N≤n =
    RationalBase.≤-trans
      {p = doubleρ}
      {q = Rational.natMul N RationalBase.1ℚ}
      {r = Rational.natMul (suc n) RationalBase.1ℚ}
      (RationalBase.<→≤ {p = doubleρ} {q = Rational.natMul N RationalBase.1ℚ} N-large)
      (Rational.natMul-mono-≤
        N
        (suc n)
        RationalBase.0<1
        (NatOrder.≤-trans N≤n (suc zero , refl)))


expPositiveMajorantTerm-eventual-ratio-half :
  (ρ : ℚ⁺) →
  (cutoff : ExpMajorantRatioCutoff ρ) →
  (n : ℕ) →
  NatOrder._≤_ (cutoff .fst) n →
  expPositiveMajorantTerm ρ (suc n) +ᶜ
  expPositiveMajorantTerm ρ (suc n) ≤ᶜ
  expPositiveMajorantTerm ρ n
expPositiveMajorantTerm-eventual-ratio-half ρ cutoff n cutoff≤n =
  expPositiveMajorantTerm-ratio-half ρ n
    (cutoff .snd n cutoff≤n)


expPositiveHalfRatio :
  ℚ⁺
expPositiveHalfRatio =
  half⁺ 1⁺


expPositiveHalfRatio<1 :
  radius expPositiveHalfRatio ℚOrder.< RationalBase.1ℚ
expPositiveHalfRatio<1 =
  half< 1⁺


expMajorantScale :
  (ρ : ℚ⁺) →
  ExpMajorantRatioCutoff ρ →
  ℚ⁺
expMajorantScale ρ cutoff =
  q ℚ.+ q ,
  RationalBase.positive-sum {p = q} {q = q} q-positive q-positive
  where
  N : ℕ
  N =
    cutoff .fst

  q : ℚ
  q =
    radius (expPositiveMajorantRadius ρ N)

  q-positive : RationalBase.0ℚ ℚOrder.< q
  q-positive =
    expPositiveMajorantRadius ρ N .snd


expScaledGeometricTerm :
  ℚ⁺ →
  ℚ⁺ →
  ℕ →
  ℝᶜ
expScaledGeometricTerm scale σ n =
  rational (radius scale ℚ.· radius (positivePower σ n))


expScaledGeometricTerm-rationalScale :
  (scale σ : ℚ⁺) →
  (n : ℕ) →
  rational (radius scale) ·ᶜ positiveGeometricTerm σ n ≡
  expScaledGeometricTerm scale σ n
expScaledGeometricTerm-rationalScale scale σ n =
  mulᶜ-rational-rational
    (radius scale)
    (radius (positivePower σ n))


expScaledGeometricTerm-nonnegative :
  (scale σ : ℚ⁺) →
  (n : ℕ) →
  0ᶜ ≤ᶜ expScaledGeometricTerm scale σ n
expScaledGeometricTerm-nonnegative scale σ n =
  ≤ℚ→rational≤ᶜ
    {q = RationalBase.0ℚ}
    {r = radius scale ℚ.· radius (positivePower σ n)}
    (ℚOrder.<Weaken≤
      RationalBase.0ℚ
      (radius scale ℚ.· radius (positivePower σ n))
      ((scale *⁺ positivePower σ n) .snd))


expScaledGeometricTailBound :
  (scale σ : ℚ⁺) →
  (σ<1 : radius σ ℚOrder.< RationalBase.1ℚ) →
  TailBound
    (expScaledGeometricTerm scale σ)
    (rationalScaleModulus
      (radius scale)
      (positiveGeometricPowerModulus σ σ<1))
expScaledGeometricTailBound scale σ σ<1 =
  subst
    (λ v →
      TailBound
        v
        (rationalScaleModulus
          (radius scale)
          (positiveGeometricPowerModulus σ σ<1)))
    (funExt (expScaledGeometricTerm-rationalScale scale σ))
    (rationalScaleTailBound
      (radius scale)
      (positiveGeometricFiniteTailBoundFromRatio σ σ<1))


expScaledGeometricModulusAntitone :
  (scale σ : ℚ⁺) →
  (σ<1 : radius σ ℚOrder.< RationalBase.1ℚ) →
  AntitoneTailModulus
    (rationalScaleModulus
      (radius scale)
      (positiveGeometricPowerModulus σ σ<1))
expScaledGeometricModulusAntitone scale σ σ<1 {ε = ε} {δ = δ} ε≤δ =
  positiveGeometricPowerModulus-antitone
    σ
    σ<1
    {ε = rationalScalePrecision (radius scale) ε}
    {δ = rationalScalePrecision (radius scale) δ}
    (rationalScalePrecision-mono
      (radius scale)
      {ε = ε}
      {δ = δ}
      ε≤δ)


expMajorantDropRadiusBound :
  (ρ : ℚ⁺) →
  (cutoff : ExpMajorantRatioCutoff ρ) →
  (t : ℕ) →
  radius (expPositiveMajorantRadius ρ ((cutoff .fst) Nat.+ t))
    ℚOrder.≤
  radius (expMajorantScale ρ cutoff) ℚ.·
  radius (positivePower expPositiveHalfRatio t)
expMajorantDropRadiusBound ρ cutoff zero =
  subst2
    ℚOrder._≤_
    (sym (cong
      (λ n → radius (expPositiveMajorantRadius ρ n))
      (Nat.+-zero N)))
    (sym (ℚ.·IdR scale))
    qN≤scale
  where
  N : ℕ
  N =
    cutoff .fst

  qN : ℚ
  qN =
    radius (expPositiveMajorantRadius ρ N)

  scale : ℚ
  scale =
    radius (expMajorantScale ρ cutoff)

  qN-nonnegative :
    RationalBase.0ℚ ℚOrder.≤ qN
  qN-nonnegative =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = qN}
      (expPositiveMajorantRadius ρ N .snd)

  qN≤scale :
    qN ℚOrder.≤ scale
  qN≤scale =
    RationalBase.q≤q+nonnegative qN qN qN-nonnegative
expMajorantDropRadiusBound ρ cutoff (suc t) =
  subst
    (λ q → q ℚOrder.≤ target)
    (sym (cong
      (λ n → radius (expPositiveMajorantRadius ρ n))
      (Nat.+-suc N t)))
    next≤target
  where
  N : ℕ
  N =
    cutoff .fst

  n : ℕ
  n =
    N Nat.+ t

  current : ℚ
  current =
    radius (expPositiveMajorantRadius ρ n)

  next : ℚ
  next =
    radius (expPositiveMajorantRadius ρ (suc n))

  coefficient : ℚ
  coefficient =
    radius ρ ℚ.· Rational.unitFraction n

  scale : ℚ
  scale =
    radius (expMajorantScale ρ cutoff)

  halfRadius : ℚ
  halfRadius =
    radius expPositiveHalfRatio

  currentPower : ℚ
  currentPower =
    radius (positivePower expPositiveHalfRatio t)

  target : ℚ
  target =
    scale ℚ.· radius (positivePower expPositiveHalfRatio (suc t))

  current-nonnegative :
    RationalBase.0ℚ ℚOrder.≤ current
  current-nonnegative =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = current}
      (expPositiveMajorantRadius ρ n .snd)

  halfRadius-nonnegative :
    RationalBase.0ℚ ℚOrder.≤ halfRadius
  halfRadius-nonnegative =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = halfRadius}
      (expPositiveHalfRatio .snd)

  coefficient≤halfRadius :
    coefficient ℚOrder.≤ halfRadius
  coefficient≤halfRadius =
    expMajorantCoefficient≤half ρ n
      (cutoff .snd n NatOrder.≤SumLeft)

  coefficient-current≤halfRadius-current :
    coefficient ℚ.· current ℚOrder.≤ halfRadius ℚ.· current
  coefficient-current≤halfRadius-current =
    ℚOrder.≤-·o
      coefficient
      halfRadius
      current
      current-nonnegative
      coefficient≤halfRadius

  current≤bound :
    current ℚOrder.≤ scale ℚ.· currentPower
  current≤bound =
    expMajorantDropRadiusBound ρ cutoff t

  halfRadius-current≤halfRadius-bound :
    halfRadius ℚ.· current ℚOrder.≤ halfRadius ℚ.· (scale ℚ.· currentPower)
  halfRadius-current≤halfRadius-bound =
    RationalMul.mul-left-nonnegative-≤
      {a = halfRadius}
      {b = current}
      {c = scale ℚ.· currentPower}
      halfRadius-nonnegative
      current≤bound

  halfRadius-bound≡target :
    halfRadius ℚ.· (scale ℚ.· currentPower) ≡ target
  halfRadius-bound≡target =
    SolverHelpers.exp-geometric-scale-step ℚCommRing halfRadius scale currentPower

  coefficient-current≤target :
    coefficient ℚ.· current ℚOrder.≤ target
  coefficient-current≤target =
    RationalBase.≤-trans
      {p = coefficient ℚ.· current}
      {q = halfRadius ℚ.· current}
      {r = target}
      coefficient-current≤halfRadius-current
      (subst
        (λ q → halfRadius ℚ.· current ℚOrder.≤ q)
        halfRadius-bound≡target
        halfRadius-current≤halfRadius-bound)

  next≤target :
    next ℚOrder.≤ target
  next≤target =
    subst
      (λ q → q ℚOrder.≤ target)
      (sym (expPositiveMajorantRadius-step ρ n))
      coefficient-current≤target


expMajorantDropBoundedByScaledGeometric :
  (ρ : ℚ⁺) →
  (cutoff : ExpMajorantRatioCutoff ρ) →
  (t : ℕ) →
  BoundedByᶜ
    (expMajorantScale ρ cutoff *⁺
      positivePower expPositiveHalfRatio t)
    (drop (cutoff .fst) (expPositiveMajorantTerm ρ) t)
expMajorantDropBoundedByScaledGeometric ρ cutoff t =
  subst
    (BoundedByᶜ κ)
    (sym (drop-index N (expPositiveMajorantTerm ρ) t))
    (rational-closed-bound→boundedᶜ
      κ
      current
      (rational-closed-boundᶜ current≤κ neg-current≤κ))
  where
  N : ℕ
  N =
    cutoff .fst

  κ : ℚ⁺
  κ =
    expMajorantScale ρ cutoff *⁺ positivePower expPositiveHalfRatio t

  current : ℚ
  current =
    radius (expPositiveMajorantRadius ρ (N Nat.+ t))

  current-nonnegative :
    RationalBase.0ℚ ℚOrder.≤ current
  current-nonnegative =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = current}
      (expPositiveMajorantRadius ρ (N Nat.+ t) .snd)

  current≤κ :
    current ℚOrder.≤ radius κ
  current≤κ =
    expMajorantDropRadiusBound ρ cutoff t

  neg-current≤0 :
    ℚ.- current ℚOrder.≤ RationalBase.0ℚ
  neg-current≤0 =
    RationalBase.neg-nonpositive {q = current} current-nonnegative

  0≤κ :
    RationalBase.0ℚ ℚOrder.≤ radius κ
  0≤κ =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = radius κ}
      (κ .snd)

  neg-current≤κ :
    ℚ.- current ℚOrder.≤ radius κ
  neg-current≤κ =
    RationalBase.≤-trans
      {p = ℚ.- current}
      {q = RationalBase.0ℚ}
      {r = radius κ}
      neg-current≤0
      0≤κ


expMajorantDropMajorizedByScaledGeometric :
  (ρ : ℚ⁺) →
  (cutoff : ExpMajorantRatioCutoff ρ) →
  SeriesMajorizedBy
    (drop (cutoff .fst) (expPositiveMajorantTerm ρ))
    (expScaledGeometricTerm
      (expMajorantScale ρ cutoff)
      expPositiveHalfRatio)
expMajorantDropMajorizedByScaledGeometric ρ cutoff =
  seriesMajorizedByTerms
    (λ t →
      bounded-byᶜ-abs
        (expMajorantDropBoundedByScaledGeometric ρ cutoff t))
    (expScaledGeometricTerm-nonnegative
      (expMajorantScale ρ cutoff)
      expPositiveHalfRatio)


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
  AntitoneTailModulus (expPositiveMajorantFactorialDropModulus ρ)
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
  AntitoneTailModulus (expPositiveMajorantFactorialModulus ρ)
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


expPowerSeriesTermBoundFromPowerBound :
  (ρ : ℚ⁺) →
  (h : ℝᶜ) →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower h n) →
  BoundedByᶜ (positivePower ρ n) (powerSeriesTerm expPowerSeries h n)
expPowerSeriesTermBoundFromPowerBound ρ h n powerBound =
  subst2
    BoundedByᶜ
    (*⁺-identity-left (positivePower ρ n))
    (sym (expPowerSeriesTerm-scalarReciprocal h n))
    scaledBound
  where
  scaledBound :
    BoundedByᶜ
      (1⁺ *⁺ positivePower ρ n)
      (scalarMulᶜ (Factorial.reciprocalFactorial n) (realPower h n))
  scaledBound =
    bounded-byᶜ-scale-rational-closed-bound
      (Factorial.reciprocalFactorial n)
      (positivePower ρ n)
      1⁺
      (realPower h n)
      (reciprocalFactorialClosedBoundOne n)
      powerBound


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


derivativePowerSeries-exp :
  (n : ℕ) →
  derivativePowerSeries expPowerSeries n ≡ expPowerSeries n
derivativePowerSeries-exp n =
  naturalTimesInverseSucReal-cancel n (expPowerSeries n)


primitivePowerSeries-exp-zero :
  primitivePowerSeries expPowerSeries zero ≡ 0ᶜ
primitivePowerSeries-exp-zero =
  refl


primitivePowerSeries-exp-suc :
  (n : ℕ) →
  primitivePowerSeries expPowerSeries (suc n) ≡
  expPowerSeries (suc n)
primitivePowerSeries-exp-suc n =
  refl


primitivePowerSeries-exp :
  (n : ℕ) →
  primitivePowerSeries expPowerSeries n ≡
  subPowerSeries expPowerSeries (constantPowerSeries 1ᶜ) n
primitivePowerSeries-exp zero =
  sym (add-inverse-right 1ᶜ)
primitivePowerSeries-exp (suc n) =
  sym (add-zero-right (expPowerSeries (suc n)))


ExpPowerSeriesMajorizedOnBall :
  ℚ⁺ →
  (ℕ → ℝᶜ) →
  (ℚ⁺ → ℕ) →
  Type₀
ExpPowerSeriesMajorizedOnBall ρ v μ =
  PowerSeriesMajorizedOnBall expPowerSeries ρ v μ


ExpPowerSeriesPowerBoundsOnBall :
  ℚ⁺ →
  Type₀
ExpPowerSeriesPowerBoundsOnBall ρ =
  (h : ℝᶜ) →
  BoundedByᶜ ρ h →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower h n)


ExpPositiveMajorantTailBound :
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type₀
ExpPositiveMajorantTailBound ρ μ =
  TailBound (expPositiveMajorantTerm ρ) μ


ExpPositiveMajorantDoubledUpper :
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type₀
ExpPositiveMajorantDoubledUpper ρ μ =
  (ε : ℚ⁺) →
  (m : ℕ) →
  NatOrder._≤_ (μ ε) m →
  expPositiveMajorantTerm ρ m +ᶜ expPositiveMajorantTerm ρ m
    ≤ᶜ rational (radius ε)


expPositiveMajorantTailBoundFromDoubledUpper :
  (ρ : ℚ⁺) →
  (cutoff : ExpMajorantRatioCutoff ρ) →
  {μ : ℚ⁺ → ℕ} →
  ((ε : ℚ⁺) → NatOrder._≤_ (cutoff .fst) (μ ε)) →
  ExpPositiveMajorantDoubledUpper ρ μ →
  ExpPositiveMajorantTailBound ρ μ
expPositiveMajorantTailBoundFromDoubledUpper ρ cutoff cutoff≤μ doubledUpper =
  eventual-ratio-half-tailBound
    (expPositiveMajorantTerm-nonnegative ρ)
    (cutoff .fst)
    (expPositiveMajorantTerm-eventual-ratio-half ρ cutoff)
    cutoff≤μ
    doubledUpper


expPowerSeriesFactorialMajorizedFromPowerBounds :
  (ρ : ℚ⁺) →
  {μ : ℚ⁺ → ℕ} →
  ExpPowerSeriesPowerBoundsOnBall ρ →
  ExpPositiveMajorantTailBound ρ μ →
  AntitoneTailModulus μ →
  ExpPowerSeriesMajorizedOnBall ρ (expPositiveMajorantTerm ρ) μ
expPowerSeriesFactorialMajorizedFromPowerBounds ρ powerBounds tailBound antitone =
  powerSeriesMajorizedOnBallFromBoundedTerms
    {a = expPowerSeries}
    {ρ = ρ}
    {κ = expPositiveMajorantRadius ρ}
    {v = expPositiveMajorantTerm ρ}
    (λ h h-bound n →
      expPowerSeriesTermBoundByPositiveMajorant
        ρ
        h
        n
        (powerBounds h h-bound n))
    (λ n → ≤ᶜ-refl (expPositiveMajorantTerm ρ n))
    (expPositiveMajorantTerm-nonnegative ρ)
    tailBound
    antitone


expPowerSeriesSubunitMajorizedFromPowerBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : ℚOrder._<_ (Constructive.Data.PositiveRationals.radius ρ) RationalBase.1ℚ) →
  ExpPowerSeriesPowerBoundsOnBall ρ →
  ExpPowerSeriesMajorizedOnBall
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
expPowerSeriesSubunitMajorizedFromPowerBounds ρ ρ<1 powerBounds =
  powerSeriesMajorizedOnBallFromBoundedTerms
    {a = expPowerSeries}
    {ρ = ρ}
    {κ = positivePower ρ}
    {v = positiveGeometricTerm ρ}
    (λ h h-bound n →
      expPowerSeriesTermBoundFromPowerBound
        ρ
        h
        n
        (powerBounds h h-bound n))
    (λ n → ≤ᶜ-refl (positiveGeometricTerm ρ n))
    (positiveGeometricTerm-nonnegative ρ)
    (λ ε m k μ≤m →
      positiveGeometricFiniteTailBoundFromRatio ρ ρ<1 ε m k μ≤m)
    (λ {ε} {δ} ε≤δ →
      positiveGeometricPowerModulus-antitone
        ρ
        ρ<1
        {ε = ε}
        {δ = δ}
        ε≤δ)


expPowerSeriesPowerBoundsFromBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  ExpPowerSeriesPowerBoundsOnBall ρ
expPowerSeriesPowerBoundsFromBall ρ ρ<1 h h-bound n =
  RealGeometricPowerBounds.powerBound
    (realGeometricPowerBoundsFromBound h bound)
    n
  where
  bound : RealGeometricBound h
  bound =
    record
      { ratioBound = ρ
      ; ratioBound<1 = ρ<1
      ; termBound = h-bound
      }


expPowerSeriesPowerBoundsOnAnyBall :
  (ρ : ℚ⁺) →
  ExpPowerSeriesPowerBoundsOnBall ρ
expPowerSeriesPowerBoundsOnAnyBall ρ h h-bound n =
  realPowerBoundsFromBound ρ h h-bound n


expPowerSeriesFactorialMajorized :
  (ρ : ℚ⁺) →
  ExpPowerSeriesMajorizedOnBall
    ρ
    (expPositiveMajorantTerm ρ)
    (expPositiveMajorantFactorialModulus ρ)
expPowerSeriesFactorialMajorized ρ =
  expPowerSeriesFactorialMajorizedFromPowerBounds
    ρ
    (expPowerSeriesPowerBoundsOnAnyBall ρ)
    (expPositiveMajorantFactorialTailBound ρ)
    (λ {ε} {δ} ε≤δ →
      expPositiveMajorantFactorialModulusAntitone
        ρ
        {ε = ε}
        {δ = δ}
        ε≤δ)


expPowerSeriesSubunitMajorized :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  ExpPowerSeriesMajorizedOnBall
    ρ
    (positiveGeometricTerm ρ)
    (positiveGeometricPowerModulus ρ ρ<1)
expPowerSeriesSubunitMajorized ρ ρ<1 =
  expPowerSeriesSubunitMajorizedFromPowerBounds
    ρ
    ρ<1
    (expPowerSeriesPowerBoundsFromBall ρ ρ<1)


expPowerSeriesOnSubunitBallWithFromPowerBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : ℚOrder._<_ (Constructive.Data.PositiveRationals.radius ρ) RationalBase.1ℚ) →
  ExpPowerSeriesPowerBoundsOnBall ρ →
  HasPowerSeriesOnBallWith
    expPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
expPowerSeriesOnSubunitBallWithFromPowerBounds ρ ρ<1 powerBounds =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (expPowerSeriesSubunitMajorizedFromPowerBounds ρ ρ<1 powerBounds)


expPowerSeriesOnSubunitBallWith :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  HasPowerSeriesOnBallWith
    expPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
expPowerSeriesOnSubunitBallWith ρ ρ<1 =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (expPowerSeriesSubunitMajorized ρ ρ<1)


expPowerSeriesOnSubunitBallFromPowerBounds :
  (ρ : ℚ⁺) →
  (ρ<1 : ℚOrder._<_ (Constructive.Data.PositiveRationals.radius ρ) RationalBase.1ℚ) →
  ExpPowerSeriesPowerBoundsOnBall ρ →
  HasPowerSeriesOnBall expPowerSeries ρ
expPowerSeriesOnSubunitBallFromPowerBounds ρ ρ<1 powerBounds =
  positiveGeometricPowerModulus ρ ρ<1 ,
  expPowerSeriesOnSubunitBallWithFromPowerBounds ρ ρ<1 powerBounds


expPowerSeriesOnSubunitBall :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< RationalBase.1ℚ) →
  HasPowerSeriesOnBall expPowerSeries ρ
expPowerSeriesOnSubunitBall ρ ρ<1 =
  positiveGeometricPowerModulus ρ ρ<1 ,
  expPowerSeriesOnSubunitBallWith ρ ρ<1


expPowerSeriesOnBallWith :
  (ρ : ℚ⁺) →
  HasPowerSeriesOnBallWith
    expPowerSeries
    ρ
    (expPositiveMajorantFactorialModulus ρ)
expPowerSeriesOnBallWith ρ =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (expPowerSeriesFactorialMajorized ρ)


expPowerSeriesOnBall :
  (ρ : ℚ⁺) →
  HasPowerSeriesOnBall expPowerSeries ρ
expPowerSeriesOnBall ρ =
  expPositiveMajorantFactorialModulus ρ ,
  expPowerSeriesOnBallWith ρ


expPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius expPowerSeries
expPowerSeriesInfiniteRadius =
  expPowerSeriesOnBall


expᶜ :
  ℝᶜ →
  ℝᶜ
expᶜ =
  centeredPowerSeriesSumEverywhere
    expPowerSeries
    0ᶜ
    expPowerSeriesInfiniteRadius


expᶜ-zero :
  expᶜ 0ᶜ ≡ 1ᶜ
expᶜ-zero =
  centeredPowerSeriesSumEverywhere-center
    expPowerSeriesInfiniteRadius
    0ᶜ


expᶜHasPowerSeriesAtWithZero :
  (ρ : ℚ⁺) →
  HasPowerSeriesAtWith
    expᶜ
    0ᶜ
    expPowerSeries
    ρ
    (expPowerSeriesInfiniteRadius ρ .fst)
expᶜHasPowerSeriesAtWithZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
    expPowerSeriesInfiniteRadius


expᶜHasPowerSeriesAtOnBallZero :
  (ρ : ℚ⁺) →
  HasPowerSeriesAtOnBall expᶜ 0ᶜ expPowerSeries ρ
expᶜHasPowerSeriesAtOnBallZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAtOnBall
    expPowerSeriesInfiniteRadius


expᶜHasPowerSeriesAtZero :
  HasPowerSeriesAt expᶜ 0ᶜ expPowerSeries
expᶜHasPowerSeriesAtZero =
  centeredPowerSeriesSumEverywhereHasPowerSeriesAt
    expPowerSeriesInfiniteRadius


expᶜAnalyticAtZero :
  AnalyticAt expᶜ 0ᶜ
expᶜAnalyticAtZero =
  centeredPowerSeriesSumEverywhereAnalyticAt
    expPowerSeries
    0ᶜ
    expPowerSeriesInfiniteRadius


derivativeExpPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius (derivativePowerSeries expPowerSeries)
derivativeExpPowerSeriesInfiniteRadius =
  derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = expPowerSeries}
    {b = expPowerSeries}
    derivativePowerSeries-exp
    expPowerSeriesInfiniteRadius


expPowerSeriesIteratedFormalPartialDerivativeBounds :
  (σ : ℚ⁺) →
  {x : ℝᶜ} →
  BoundedByᶜ σ x →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    expPowerSeries
    x
    (λ s n →
      positivePartialSum
        (λ k →
          scalar-bound (Rational.natMul (suc k) RationalBase.1ℚ) *⁺
          1⁺ *⁺
          positivePower σ k)
        n)
expPowerSeriesIteratedFormalPartialDerivativeBounds σ x-bound =
  powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
    σ
    x-bound
    (λ _ → 1⁺)
    expPowerSeriesCoefficientBoundOne


expᶜHasDerivativeAtWithFromIteratedBoundsOnSubball :
  {x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  {δ : ℕ → ℕ → ℚ⁺} →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement 0ᶜ x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    expPowerSeries
    (centeredDisplacement 0ᶜ x)
    δ →
  PowerSeriesPartialSumsDerivativeModulusLarge
    (termwiseConvergenceIndex
      (expPowerSeriesInfiniteRadius ρ .fst)
      (derivativeExpPowerSeriesInfiniteRadius σ .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus σ δ) →
  HasDerivativeAtWith expᶜ x (expᶜ x) μ
expᶜHasDerivativeAtWithFromIteratedBoundsOnSubball
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {δ = δ}
  x-displacement-bound
  margin
  derivative-bounds
  partialModulus-large =
  centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
    {a = expPowerSeries}
    {b = expPowerSeries}
    {c = 0ᶜ}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ = μ}
    {δ = δ}
    derivativePowerSeries-exp
    expPowerSeriesInfiniteRadius
    derivativeExpPowerSeriesInfiniteRadius
    expPowerSeriesInfiniteRadius
    x-displacement-bound
    margin
    derivative-bounds
    partialModulus-large


primitiveExpPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius (primitivePowerSeries expPowerSeries)
primitiveExpPowerSeriesInfiniteRadius =
  primitivePowerSeriesInfiniteRadiusFromCoefficientPath
    {a = expPowerSeries}
    {b = subPowerSeries expPowerSeries (constantPowerSeries 1ᶜ)}
    primitivePowerSeries-exp
    (subPowerSeriesInfiniteRadius
      expPowerSeriesInfiniteRadius
      (constantPowerSeriesInfiniteRadius 1ᶜ))


expPowerSeriesOnBallWithFromMajorant :
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  ExpPowerSeriesMajorizedOnBall ρ v μ →
  HasPowerSeriesOnBallWith expPowerSeries ρ μ
expPowerSeriesOnBallWithFromMajorant =
  majorizedOnBall→hasPowerSeriesOnBallWith


expPowerSeriesOnBallFromMajorant :
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  ExpPowerSeriesMajorizedOnBall ρ v μ →
  HasPowerSeriesOnBall expPowerSeries ρ
expPowerSeriesOnBallFromMajorant =
  majorizedOnBall→hasPowerSeriesOnBall


ExpPowerSeriesMajorants :
  Type₀
ExpPowerSeriesMajorants =
  (ρ : ℚ⁺) →
  Σ[ v ∈ (ℕ → ℝᶜ) ]
  Σ[ μ ∈ (ℚ⁺ → ℕ) ]
    ExpPowerSeriesMajorizedOnBall ρ v μ


expPowerSeriesInfiniteRadiusFromMajorants :
  ExpPowerSeriesMajorants →
  HasInfinitePowerSeriesRadius expPowerSeries
expPowerSeriesInfiniteRadiusFromMajorants majorants ρ =
  μ , expPowerSeriesOnBallWithFromMajorant majorant
  where
  v : ℕ → ℝᶜ
  v =
    majorants ρ .fst

  μ : ℚ⁺ → ℕ
  μ =
    majorants ρ .snd .fst

  majorant : ExpPowerSeriesMajorizedOnBall ρ v μ
  majorant =
    majorants ρ .snd .snd
