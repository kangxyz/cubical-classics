{-

Part of Constructive.Analysis.Reals.PowerSeries.Instances.Exponential

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Exponential.Majorant where

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
  using (bounded-byᶜ-abs≤rational)
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

open import Constructive.Analysis.Reals.PowerSeries.Instances.Exponential.Internal
open import Constructive.Analysis.Reals.PowerSeries.Instances.Exponential.Coefficients

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
  AntitoneNatModulus
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
      bounded-byᶜ-abs≤rational
        (expMajorantDropBoundedByScaledGeometric ρ cutoff t))
    (expScaledGeometricTerm-nonnegative
      (expMajorantScale ρ cutoff)
      expPositiveHalfRatio)
