{-

Real geometric series from explicit majorants

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Series.Instances.Geometric.Real where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst)
import Cubical.Data.Sum as Sum
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Modulus using (AntitoneNatModulus)
open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Reals.CauchyReals.Metric
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.CommRing
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Inverse
  using (HasRightInverseᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.Series.Cauchy
open import Constructive.Analysis.Reals.Series.Comparison
open import Constructive.Analysis.Reals.Series.Finite
open import Constructive.Analysis.Reals.Series.Tail
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open import Constructive.Analysis.GeometricDecay
open import Constructive.Analysis.GeometricDecay.Algebra
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Rational
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Majorant

RealGeometricBound : ℝᶜ → Type₀
RealGeometricBound x =
  Σ[ ratioBound ∈ ℚ⁺ ]
    Σ[ ratioBound<1 ∈ radius ratioBound ℚOrder.< Rational.1ℚ ]
      BoundedByᶜ ratioBound x


module RealGeometricBound where
  ratioBound :
    {x : ℝᶜ} →
    RealGeometricBound x →
    ℚ⁺
  ratioBound bound =
    bound .fst

  ratioBound<1 :
    {x : ℝᶜ} →
    (bound : RealGeometricBound x) →
    radius (ratioBound bound) ℚOrder.< Rational.1ℚ
  ratioBound<1 bound =
    bound .snd .fst

  termBound :
    {x : ℝᶜ} →
    (bound : RealGeometricBound x) →
    BoundedByᶜ (ratioBound bound) x
  termBound bound =
    bound .snd .snd


RealGeometricTerms : ℝᶜ → Type₀
RealGeometricTerms x =
  Σ[ term ∈ (ℕ → ℝᶜ) ]
    term zero ≡ rationalGeometricTerm Rational.1ℚ zero


module RealGeometricTerms where
  term :
    {x : ℝᶜ} →
    RealGeometricTerms x →
    ℕ →
    ℝᶜ
  term terms =
    terms .fst

  firstTerm :
    {x : ℝᶜ} →
    (terms : RealGeometricTerms x) →
    term {x = x} terms zero ≡ rationalGeometricTerm Rational.1ℚ zero
  firstTerm terms =
    terms .snd


realPower :
  ℝᶜ →
  ℕ →
  ℝᶜ
realPower x zero =
  1ᶜ
realPower x (suc n) =
  x ·ᶜ realPower x n


realPower-zero :
  (x : ℝᶜ) →
  realPower x zero ≡ 1ᶜ
realPower-zero x =
  refl


realPower-suc :
  (x : ℝᶜ) →
  (n : ℕ) →
  realPower x (suc n) ≡ x ·ᶜ realPower x n
realPower-suc x n =
  refl


realGeometricPowerTerms :
  (x : ℝᶜ) →
  RealGeometricTerms x
realGeometricPowerTerms x =
  realPower x , refl


realGeometricFiniteIdentity :
  (x : ℝᶜ) →
  (n : ℕ) →
  (1ᶜ +ᶜ (-ᶜ x)) ·ᶜ partialSum (realPower x) n ≡
  1ᶜ +ᶜ (-ᶜ realPower x n)
realGeometricFiniteIdentity x zero =
  SolverHelpers.geometric-zero CauchyRealsCommRing x
realGeometricFiniteIdentity x (suc n) =
  cong
    ((1ᶜ +ᶜ (-ᶜ x)) ·ᶜ_)
    (partialSum-snoc (realPower x) n) ∙
  SolverHelpers.geometric-distrib CauchyRealsCommRing x S p ∙
  cong
    (λ q → q +ᶜ ((1ᶜ +ᶜ (-ᶜ x)) ·ᶜ p))
    (realGeometricFiniteIdentity x n) ∙
  SolverHelpers.geometric-step CauchyRealsCommRing x p
  where
  S : ℝᶜ
  S =
    partialSum (realPower x) n

  p : ℝᶜ
  p =
    realPower x n


RealGeometricPowerTailBound :
  (x : ℝᶜ) →
  (ℚ⁺ → ℕ) →
  Type₀
RealGeometricPowerTailBound x μ =
  SeriesTailBound (realPower x) μ


RealGeometricTailBound :
  (x : ℝᶜ) →
  RealGeometricTerms x →
  (ℚ⁺ → ℕ) →
  Type₀
RealGeometricTailBound x terms μ =
  SeriesTailBound (RealGeometricTerms.term {x = x} terms) μ


RealGeometricFiniteTailBound :
  (x : ℝᶜ) →
  RealGeometricTerms x →
  (ℚ⁺ → ℕ) →
  Type₀
RealGeometricFiniteTailBound x terms μ =
  TailBound (RealGeometricTerms.term {x = x} terms) μ


RealGeometricPowerMajorant :
  (x : ℝᶜ) →
  RealGeometricTerms x →
  RealGeometricBound x →
  Type₀
RealGeometricPowerMajorant x terms bound =
  SeriesMajorizedBy
    (RealGeometricTerms.term {x = x} terms)
    (positiveGeometricTerm (RealGeometricBound.ratioBound {x = x} bound))


module RealGeometricPowerMajorant where
  termsMajorized :
    {x : ℝᶜ} →
    {terms : RealGeometricTerms x} →
    {bound : RealGeometricBound x} →
    RealGeometricPowerMajorant x terms bound →
    SeriesMajorizedBy
      (RealGeometricTerms.term {x = x} terms)
      (positiveGeometricTerm (RealGeometricBound.ratioBound {x = x} bound))
  termsMajorized majorant =
    majorant


realGeometricTailBoundFromMajorant :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorant x terms bound →
  {μ : ℚ⁺ → ℕ} →
  PositiveGeometricFiniteTailBound
    (RealGeometricBound.ratioBound bound)
    μ →
  RealGeometricFiniteTailBound x terms μ
realGeometricTailBoundFromMajorant x terms bound majorant =
  comparisonTest
    (RealGeometricPowerMajorant.termsMajorized
      {x = x}
      {terms = terms}
      {bound = bound}
      majorant)


realGeometricSeriesTailBoundFromMajorant :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorant x terms bound →
  {μ : ℚ⁺ → ℕ} →
  PositiveGeometricFiniteTailBound
    (RealGeometricBound.ratioBound bound)
    μ →
  AntitoneNatModulus μ →
  RealGeometricTailBound x terms (λ ε → μ (half⁺ ε))
realGeometricSeriesTailBoundFromMajorant x terms bound majorant {μ = μ} majorTail μ-antitone =
  tailBound→SeriesTailBound
    {u = RealGeometricTerms.term {x = x} terms}
    {μ = μ}
    (realGeometricTailBoundFromMajorant x terms bound majorant majorTail)
    μ-antitone


realGeometricSeriesTailBoundFromPositiveData :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorant x terms bound →
  (tailData : PositiveGeometricTailData (RealGeometricBound.ratioBound bound)) →
  RealGeometricTailBound x terms
    (λ ε →
      PositiveGeometricTailData.modulus
        tailData
        (half⁺ ε))
realGeometricSeriesTailBoundFromPositiveData x terms bound majorant tailData =
  realGeometricSeriesTailBoundFromMajorant
    x
    terms
    bound
    majorant
    (PositiveGeometricTailData.finiteTailBound tailData)
    (PositiveGeometricTailData.modulusAntitone tailData)


realGeometricSeriesTailBoundFromRatio :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorant x terms bound →
  RealGeometricTailBound x terms
    (λ ε →
      positiveGeometricPowerModulus
        (RealGeometricBound.ratioBound bound)
        (RealGeometricBound.ratioBound<1 bound)
        (half⁺ ε))
realGeometricSeriesTailBoundFromRatio x terms bound majorant =
  realGeometricSeriesTailBoundFromPositiveData
    x
    terms
    bound
    majorant
    (positiveGeometricTailDataFromRatio ρ ρ<1)
  where
  ρ : ℚ⁺
  ρ =
    RealGeometricBound.ratioBound bound

  ρ<1 : radius ρ ℚOrder.< Rational.1ℚ
  ρ<1 =
    RealGeometricBound.ratioBound<1 bound


realGeometricTailBoundFromRatio :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorant x terms bound →
  RealGeometricFiniteTailBound
    x
    terms
    (positiveGeometricPowerModulus
      (RealGeometricBound.ratioBound bound)
      (RealGeometricBound.ratioBound<1 bound))
realGeometricTailBoundFromRatio x terms bound majorant =
  realGeometricTailBoundFromMajorant
    x
    terms
    bound
    majorant
    (positiveGeometricFiniteTailBoundFromRatio
      ρ
      ρ<1)
  where
  ρ : ℚ⁺
  ρ =
    RealGeometricBound.ratioBound bound

  ρ<1 : radius ρ ℚOrder.< Rational.1ℚ
  ρ<1 =
    RealGeometricBound.ratioBound<1 bound


realGeometricSumFromMajorant :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorant x terms bound →
  (μ : ℚ⁺ → ℕ) →
  PositiveGeometricFiniteTailBound
    (RealGeometricBound.ratioBound bound)
    μ →
  AntitoneNatModulus μ →
  ℝᶜ
realGeometricSumFromMajorant x terms bound majorant μ majorTail μ-antitone =
  seriesSumFromFiniteTailBound
    (RealGeometricTerms.term terms)
    μ
    (realGeometricTailBoundFromMajorant x terms bound majorant majorTail)
    μ-antitone


realGeometricSumFromPositiveData :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorant x terms bound →
  PositiveGeometricTailData (RealGeometricBound.ratioBound bound) →
  ℝᶜ
realGeometricSumFromPositiveData x terms bound majorant tailData =
  realGeometricSumFromMajorant
    x
    terms
    bound
    majorant
    (PositiveGeometricTailData.modulus tailData)
    (PositiveGeometricTailData.finiteTailBound tailData)
    (PositiveGeometricTailData.modulusAntitone tailData)


realGeometricSumFromRatio :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorant x terms bound →
  ℝᶜ
realGeometricSumFromRatio x terms bound majorant =
  realGeometricSumFromPositiveData
    x
    terms
    bound
    majorant
    (positiveGeometricTailDataFromRatio ρ ρ<1)
  where
  ρ : ℚ⁺
  ρ =
    RealGeometricBound.ratioBound bound

  ρ<1 : radius ρ ℚOrder.< Rational.1ℚ
  ρ<1 =
    RealGeometricBound.ratioBound<1 bound


realGeometricConvergesFromPositiveData :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  (majorant : RealGeometricPowerMajorant x terms bound) →
  (tailData : PositiveGeometricTailData
    (RealGeometricBound.ratioBound bound)) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromFiniteTailBound
      (RealGeometricTerms.term terms)
      (PositiveGeometricTailData.modulus tailData)
      (realGeometricTailBoundFromMajorant
        x
        terms
        bound
        majorant
        (PositiveGeometricTailData.finiteTailBound tailData))
      (PositiveGeometricTailData.modulusAntitone tailData))
    (realGeometricSumFromPositiveData x terms bound majorant tailData)
realGeometricConvergesFromPositiveData x terms bound majorant tailData =
  seriesSumFromFiniteTailBoundConverges
    (RealGeometricTerms.term terms)
    (PositiveGeometricTailData.modulus tailData)
    (realGeometricTailBoundFromMajorant
      x
      terms
      bound
      majorant
        (PositiveGeometricTailData.finiteTailBound tailData))
    (PositiveGeometricTailData.modulusAntitone tailData)


realGeometricConvergesFromRatio :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  (majorant : RealGeometricPowerMajorant x terms bound) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromFiniteTailBound
      (RealGeometricTerms.term terms)
      (positiveGeometricPowerModulus
        (RealGeometricBound.ratioBound bound)
        (RealGeometricBound.ratioBound<1 bound))
      (realGeometricTailBoundFromRatio x terms bound majorant)
      (positiveGeometricPowerModulus-antitone
        (RealGeometricBound.ratioBound bound)
        (RealGeometricBound.ratioBound<1 bound)))
    (realGeometricSumFromRatio x terms bound majorant)
realGeometricConvergesFromRatio x terms bound majorant =
  realGeometricConvergesFromPositiveData
    x
    terms
    bound
    majorant
    (positiveGeometricTailDataFromRatio ρ ρ<1)
  where
  ρ : ℚ⁺
  ρ =
    RealGeometricBound.ratioBound bound

  ρ<1 : radius ρ ℚOrder.< Rational.1ℚ
  ρ<1 =
    RealGeometricBound.ratioBound<1 bound


realGeometricTailBoundFromUpperData :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorant x terms bound →
  (upperData : PositiveGeometricTailUpperData
    (RealGeometricBound.ratioBound bound)) →
  RealGeometricFiniteTailBound x terms
    (PositiveGeometricTailUpperData.modulus upperData)
realGeometricTailBoundFromUpperData x terms bound majorant upperData =
  realGeometricTailBoundFromMajorant
    x
    terms
    bound
    majorant
    (positiveGeometricFiniteTailBoundFromUpper
      (RealGeometricBound.ratioBound bound)
      (PositiveGeometricTailUpperData.tailUpperBound upperData))


realGeometricSeriesTailBoundFromUpperData :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorant x terms bound →
  (upperData : PositiveGeometricTailUpperData
    (RealGeometricBound.ratioBound bound)) →
  RealGeometricTailBound x terms
    (λ ε →
      PositiveGeometricTailUpperData.modulus
        upperData
        (half⁺ ε))
realGeometricSeriesTailBoundFromUpperData x terms bound majorant upperData =
  realGeometricSeriesTailBoundFromPositiveData
    x
    terms
    bound
    majorant
    (positiveGeometricTailDataFromUpperData
      (RealGeometricBound.ratioBound bound)
      upperData)


realGeometricSumFromUpperData :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorant x terms bound →
  PositiveGeometricTailUpperData (RealGeometricBound.ratioBound bound) →
  ℝᶜ
realGeometricSumFromUpperData x terms bound majorant upperData =
  realGeometricSumFromPositiveData
    x
    terms
    bound
    majorant
    (positiveGeometricTailDataFromUpperData
      (RealGeometricBound.ratioBound bound)
      upperData)


RealGeometricPowerMajorized :
  (x : ℝᶜ) →
  RealGeometricBound x →
  Type₀
RealGeometricPowerMajorized x bound =
  RealGeometricPowerMajorant x (realGeometricPowerTerms x) bound


RealGeometricPowerBounds :
  (x : ℝᶜ) →
  RealGeometricBound x →
  Type₀
RealGeometricPowerBounds x bound =
  (n : ℕ) →
  BoundedByᶜ
    (positivePower (RealGeometricBound.ratioBound bound) n)
    (realPower x n)


module RealGeometricPowerBounds where
  powerBound :
    {x : ℝᶜ} →
    {bound : RealGeometricBound x} →
    RealGeometricPowerBounds x bound →
    (n : ℕ) →
    BoundedByᶜ
      (positivePower (RealGeometricBound.ratioBound bound) n)
      (realPower x n)
  powerBound powerBounds =
    powerBounds


realGeometricPowerMajorantFromBounds :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerBounds x bound →
  RealGeometricPowerMajorized x bound
realGeometricPowerMajorantFromBounds x bound powerBounds =
  termMajorized , majorantNonnegative
  where
  ρ : ℚ⁺
  ρ =
    RealGeometricBound.ratioBound bound

  termMajorized :
    (m n : ℕ) →
    absᶜ (drop m (realPower x) n) ≤ᶜ
    drop m (positiveGeometricTerm ρ) n
  termMajorized m n =
    subst2
      (λ u v → absᶜ u ≤ᶜ v)
      (sym (drop-index m (realPower x) n))
      (sym (drop-index m (positiveGeometricTerm ρ) n))
      (bounded-byᶜ-abs
        (RealGeometricPowerBounds.powerBound powerBounds (m Nat.+ n)))

  majorantNonnegative :
    (m n : ℕ) →
    0ᶜ ≤ᶜ drop m (positiveGeometricTerm ρ) n
  majorantNonnegative m n =
    subst
      (λ v → 0ᶜ ≤ᶜ v)
      (sym (drop-index m (positiveGeometricTerm ρ) n))
      (positiveGeometricTerm-nonnegative ρ (m Nat.+ n))


realGeometricPowerBound-one :
  (x : ℝᶜ) →
  BoundedByᶜ 1⁺ (realPower x zero)
realGeometricPowerBound-one x =
  rational-closed-bound→boundedᶜ
    1⁺
    Rational.1ℚ
    (rational-closed-boundᶜ
      (Rational.≤-refl Rational.1ℚ)
      (Rational.<→≤
        {p = Rational.-1ℚ}
        {q = Rational.1ℚ}
        (ℚOrder.isTrans<
          Rational.-1ℚ
          Rational.0ℚ
          Rational.1ℚ
          Rational.-1<0
          Rational.0<1)))


realGeometricPowerBoundsFromStep :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  ((n : ℕ) →
    BoundedByᶜ
      (positivePower (RealGeometricBound.ratioBound bound) n)
      (realPower x n) →
    BoundedByᶜ
      (positivePower (RealGeometricBound.ratioBound bound) (suc n))
      (realPower x (suc n))) →
  RealGeometricPowerBounds x bound
realGeometricPowerBoundsFromStep x bound step =
  powerBound
  where
  powerBound :
    (n : ℕ) →
    BoundedByᶜ
      (positivePower (RealGeometricBound.ratioBound bound) n)
      (realPower x n)
  powerBound zero =
    realGeometricPowerBound-one x
  powerBound (suc n) =
    step n (powerBound n)


realPowerBoundsFromBound :
  (ρ : ℚ⁺) →
  (x : ℝᶜ) →
  BoundedByᶜ ρ x →
  (n : ℕ) →
  BoundedByᶜ (positivePower ρ n) (realPower x n)
realPowerBoundsFromBound ρ x x-bound zero =
  realGeometricPowerBound-one x
realPowerBoundsFromBound ρ x x-bound (suc n) =
  bounded-byᶜ-mul
    ρ
    (positivePower ρ n)
    x
    (realPower x n)
    x-bound
    (realPowerBoundsFromBound ρ x x-bound n)


realGeometricPowerBoundsFromBound :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerBounds x bound
realGeometricPowerBoundsFromBound x bound =
  realPowerBoundsFromBound ρ x x-bound
  where
  ρ : ℚ⁺
  ρ =
    RealGeometricBound.ratioBound bound

  x-bound : BoundedByᶜ ρ x
  x-bound =
    RealGeometricBound.termBound bound


realGeometricPowerSeriesTailBoundFromPositiveData :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorized x bound →
  (tailData : PositiveGeometricTailData
    (RealGeometricBound.ratioBound bound)) →
  RealGeometricPowerTailBound x
    (λ ε → PositiveGeometricTailData.modulus tailData (half⁺ ε))
realGeometricPowerSeriesTailBoundFromPositiveData x bound majorant tailData =
  realGeometricSeriesTailBoundFromPositiveData
    x
    (realGeometricPowerTerms x)
    bound
    majorant
    tailData


realGeometricPowerSeriesTailBoundFromRatio :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorized x bound →
  RealGeometricPowerTailBound x
    (λ ε →
      positiveGeometricPowerModulus
        (RealGeometricBound.ratioBound bound)
        (RealGeometricBound.ratioBound<1 bound)
        (half⁺ ε))
realGeometricPowerSeriesTailBoundFromRatio x bound majorant =
  realGeometricSeriesTailBoundFromRatio
    x
    (realGeometricPowerTerms x)
    bound
    majorant


realGeometricPowerSumFromPositiveData :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorized x bound →
  PositiveGeometricTailData (RealGeometricBound.ratioBound bound) →
  ℝᶜ
realGeometricPowerSumFromPositiveData x bound majorant tailData =
  realGeometricSumFromPositiveData
    x
    (realGeometricPowerTerms x)
    bound
    majorant
    tailData


realGeometricPowerSumFromRatio :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorized x bound →
  ℝᶜ
realGeometricPowerSumFromRatio x bound majorant =
  realGeometricSumFromRatio
    x
    (realGeometricPowerTerms x)
    bound
    majorant


realGeometricPowerConvergesFromPositiveData :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  (majorant : RealGeometricPowerMajorized x bound) →
  (tailData : PositiveGeometricTailData
    (RealGeometricBound.ratioBound bound)) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromFiniteTailBound
      (realPower x)
      (PositiveGeometricTailData.modulus tailData)
      (realGeometricTailBoundFromMajorant
        x
        (realGeometricPowerTerms x)
        bound
        majorant
        (PositiveGeometricTailData.finiteTailBound tailData))
      (PositiveGeometricTailData.modulusAntitone tailData))
    (realGeometricPowerSumFromPositiveData x bound majorant tailData)
realGeometricPowerConvergesFromPositiveData x bound majorant tailData =
  realGeometricConvergesFromPositiveData
    x
    (realGeometricPowerTerms x)
    bound
    majorant
    tailData


realGeometricPowerConvergesFromRatio :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  (majorant : RealGeometricPowerMajorized x bound) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromFiniteTailBound
      (realPower x)
      (positiveGeometricPowerModulus
        (RealGeometricBound.ratioBound bound)
        (RealGeometricBound.ratioBound<1 bound))
      (realGeometricTailBoundFromRatio
        x
        (realGeometricPowerTerms x)
        bound
        majorant)
      (positiveGeometricPowerModulus-antitone
        (RealGeometricBound.ratioBound bound)
        (RealGeometricBound.ratioBound<1 bound)))
    (realGeometricPowerSumFromRatio x bound majorant)
realGeometricPowerConvergesFromRatio x bound majorant =
  realGeometricConvergesFromRatio
    x
    (realGeometricPowerTerms x)
    bound
    majorant


realGeometricPowerTailBoundFromPowerBounds :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerBounds x bound →
  RealGeometricFiniteTailBound
    x
    (realGeometricPowerTerms x)
    (positiveGeometricPowerModulus
      (RealGeometricBound.ratioBound bound)
      (RealGeometricBound.ratioBound<1 bound))
realGeometricPowerTailBoundFromPowerBounds x bound powerBounds =
  realGeometricTailBoundFromRatio
    x
    (realGeometricPowerTerms x)
    bound
    (realGeometricPowerMajorantFromBounds x bound powerBounds)


realGeometricPowerSeriesTailBoundFromPowerBounds :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerBounds x bound →
  RealGeometricPowerTailBound x
    (λ ε →
      positiveGeometricPowerModulus
        (RealGeometricBound.ratioBound bound)
        (RealGeometricBound.ratioBound<1 bound)
        (half⁺ ε))
realGeometricPowerSeriesTailBoundFromPowerBounds x bound powerBounds =
  realGeometricPowerSeriesTailBoundFromRatio
    x
    bound
    (realGeometricPowerMajorantFromBounds x bound powerBounds)


realGeometricPowerSumFromPowerBounds :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerBounds x bound →
  ℝᶜ
realGeometricPowerSumFromPowerBounds x bound powerBounds =
  realGeometricPowerSumFromRatio
    x
    bound
    (realGeometricPowerMajorantFromBounds x bound powerBounds)


realGeometricPowerConvergesFromPowerBounds :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  (powerBounds : RealGeometricPowerBounds x bound) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromFiniteTailBound
      (realPower x)
      (positiveGeometricPowerModulus
        (RealGeometricBound.ratioBound bound)
        (RealGeometricBound.ratioBound<1 bound))
      (realGeometricPowerTailBoundFromPowerBounds x bound powerBounds)
      (positiveGeometricPowerModulus-antitone
        (RealGeometricBound.ratioBound bound)
        (RealGeometricBound.ratioBound<1 bound)))
    (realGeometricPowerSumFromPowerBounds x bound powerBounds)
realGeometricPowerConvergesFromPowerBounds x bound powerBounds =
  realGeometricPowerConvergesFromRatio
    x
    bound
    (realGeometricPowerMajorantFromBounds x bound powerBounds)


realGeometricNeumannRightInverseFromPowerBounds :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  (powerBounds : RealGeometricPowerBounds x bound) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (1ᶜ +ᶜ (-ᶜ x)) →
  (1ᶜ +ᶜ (-ᶜ x)) ·ᶜ
    seriesSumFromFiniteTailBound
      (realPower x)
      (positiveGeometricPowerModulus
        (RealGeometricBound.ratioBound bound)
        (RealGeometricBound.ratioBound<1 bound))
      (realGeometricPowerTailBoundFromPowerBounds x bound powerBounds)
      (positiveGeometricPowerModulus-antitone
        (RealGeometricBound.ratioBound bound)
        (RealGeometricBound.ratioBound<1 bound))
  ≡ 1ᶜ
realGeometricNeumannRightInverseFromPowerBounds
  x
  bound
  powerBounds
  κ
  factorBound =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    product
    1ᶜ
    closeAt
  where
  ρ : ℚ⁺
  ρ =
    RealGeometricBound.ratioBound bound

  ρ<1 : radius ρ ℚOrder.< Rational.1ℚ
  ρ<1 =
    RealGeometricBound.ratioBound<1 bound

  μ : ℚ⁺ → ℕ
  μ =
    positiveGeometricPowerModulus ρ ρ<1

  μ-antitone : AntitoneNatModulus μ
  μ-antitone =
    positiveGeometricPowerModulus-antitone ρ ρ<1

  tailBound : TailBound (realPower x) μ
  tailBound =
    realGeometricPowerTailBoundFromPowerBounds x bound powerBounds

  factor : ℝᶜ
  factor =
    1ᶜ +ᶜ (-ᶜ x)

  product : ℝᶜ
  product =
    factor ·ᶜ
    seriesSumFromFiniteTailBound
      (realPower x)
      μ
      tailBound
      μ-antitone

  closeAt :
    (ε : ℚ⁺) →
    product ∼[ ε ] 1ᶜ
  closeAt ε =
    subst
      (λ precision → product ∼[ precision ] 1ᶜ)
      (half⁺+half⁺≡ ε)
      (MetricSpace.close-triangle
        CauchyRealsMetricSpace
        product∼partial
        partial∼one)
    where
    η : ℚ⁺
    η =
      half⁺ ε

    productPrecision : ℚ⁺
    productPrecision =
      quarter⁺
        (half⁺
          (fst (mulᶜ-continuous-right-with-bound κ factor factorBound) η))

    tailPrecision : ℚ⁺
    tailPrecision =
      half⁺ η

    productIndex : ℕ
    productIndex =
      μ productPrecision

    tailIndex : ℕ
    tailIndex =
      μ tailPrecision

    n : ℕ
    n =
      productIndex Nat.+ tailIndex

    productIndex≤n : NatOrder._≤_ productIndex n
    productIndex≤n =
      tailIndex , Nat.+-comm tailIndex productIndex

    tailIndex≤n : NatOrder._≤_ tailIndex n
    tailIndex≤n =
      productIndex , refl

    product∼partial :
      product ∼[ η ] factor ·ᶜ partialSum (realPower x) n
    product∼partial =
      seriesSumFromFiniteTailBound-mul-left-convergesAt
        factor
        κ
        factorBound
        (realPower x)
        μ
        tailBound
        μ-antitone
        η
        n
        productIndex≤n

    powerTailBound :
      BoundedByᶜ tailPrecision (tailSum (realPower x) n (suc zero))
    powerTailBound =
      tailBound tailPrecision n (suc zero) tailIndex≤n

    powerBound :
      BoundedByᶜ tailPrecision (realPower x n)
    powerBound =
      subst
        (BoundedByᶜ tailPrecision)
        (tailSum-one (realPower x) n)
        powerTailBound

    power∼zero :
      realPower x n ∼[ η ] 0ᶜ
    power∼zero =
      bounded-byᶜ-close-zero
        tailPrecision
        η
        (realPower x n)
        powerBound
        (half< η)

    negPower∼zero :
      (-ᶜ realPower x n) ∼[ η ] 0ᶜ
    negPower∼zero =
      subst
        (λ z → (-ᶜ realPower x n) ∼[ η ] z)
        neg-zeroᶜ
        (neg-close power∼zero)

    oneMinusPower∼one :
      (1ᶜ +ᶜ (-ᶜ realPower x n)) ∼[ η ] 1ᶜ
    oneMinusPower∼one =
      subst
        (λ z → (1ᶜ +ᶜ (-ᶜ realPower x n)) ∼[ η ] z)
        (add-zero-right 1ᶜ)
        (add-close-right 1ᶜ negPower∼zero)

    partial∼one :
      factor ·ᶜ partialSum (realPower x) n ∼[ η ] 1ᶜ
    partial∼one =
      subst
        (λ z → z ∼[ η ] 1ᶜ)
        (sym (realGeometricFiniteIdentity x n))
        oneMinusPower∼one


realGeometricPowerNeumannRightInverseFromPowerBounds :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  (powerBounds : RealGeometricPowerBounds x bound) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (1ᶜ +ᶜ (-ᶜ x)) →
  (1ᶜ +ᶜ (-ᶜ x)) ·ᶜ
  realGeometricPowerSumFromPowerBounds x bound powerBounds ≡ 1ᶜ
realGeometricPowerNeumannRightInverseFromPowerBounds
  x
  bound
  powerBounds
  κ
  factorBound =
  realGeometricNeumannRightInverseFromPowerBounds
    x
    bound
    powerBounds
    κ
    factorBound


realGeometricPowerNeumannHasRightInverseFromPowerBounds :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  (powerBounds : RealGeometricPowerBounds x bound) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ (1ᶜ +ᶜ (-ᶜ x)) →
  HasRightInverseᶜ (1ᶜ +ᶜ (-ᶜ x))
realGeometricPowerNeumannHasRightInverseFromPowerBounds
  x
  bound
  powerBounds
  κ
  factorBound =
  realGeometricPowerSumFromPowerBounds x bound powerBounds ,
  realGeometricPowerNeumannRightInverseFromPowerBounds
    x
    bound
    powerBounds
    κ
    factorBound


realGeometricPowerSeriesTailBoundFromUpperData :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorized x bound →
  (upperData : PositiveGeometricTailUpperData
    (RealGeometricBound.ratioBound bound)) →
  RealGeometricPowerTailBound x
    (λ ε → PositiveGeometricTailUpperData.modulus upperData (half⁺ ε))
realGeometricPowerSeriesTailBoundFromUpperData x bound majorant upperData =
  realGeometricSeriesTailBoundFromUpperData
    x
    (realGeometricPowerTerms x)
    bound
    majorant
    upperData


realGeometricPowerSumFromUpperData :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorized x bound →
  PositiveGeometricTailUpperData (RealGeometricBound.ratioBound bound) →
  ℝᶜ
realGeometricPowerSumFromUpperData x bound majorant upperData =
  realGeometricSumFromUpperData
    x
    (realGeometricPowerTerms x)
    bound
    majorant
    upperData


realGeometricPowerSeriesTailBoundFromSegmentData :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorized x bound →
  (segmentData : PositiveGeometricSegmentUpperData
    (RealGeometricBound.ratioBound bound)) →
  RealGeometricPowerTailBound x
    (λ ε → PositiveGeometricSegmentUpperData.modulus segmentData (half⁺ ε))
realGeometricPowerSeriesTailBoundFromSegmentData x bound majorant segmentData =
  realGeometricPowerSeriesTailBoundFromUpperData
    x
    bound
    majorant
    (positiveGeometricTailUpperDataFromSegmentData
      (RealGeometricBound.ratioBound bound)
      segmentData)


realGeometricPowerSumFromSegmentData :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorized x bound →
  PositiveGeometricSegmentUpperData (RealGeometricBound.ratioBound bound) →
  ℝᶜ
realGeometricPowerSumFromSegmentData x bound majorant segmentData =
  realGeometricPowerSumFromUpperData
    x
    bound
    majorant
    (positiveGeometricTailUpperDataFromSegmentData
      (RealGeometricBound.ratioBound bound)
      segmentData)


realGeometricPowerSeriesTailBoundFromPowerData :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorized x bound →
  (powerData : PositiveGeometricPowerScaledUpperData
    (RealGeometricBound.ratioBound bound)) →
  RealGeometricPowerTailBound x
    (λ ε → PositiveGeometricPowerScaledUpperData.modulus powerData (half⁺ ε))
realGeometricPowerSeriesTailBoundFromPowerData x bound majorant powerData =
  realGeometricPowerSeriesTailBoundFromPositiveData
    x
    bound
    majorant
    (positiveGeometricTailDataFromPowerData
      (RealGeometricBound.ratioBound bound)
      powerData)


realGeometricPowerSumFromPowerData :
  (x : ℝᶜ) →
  (bound : RealGeometricBound x) →
  RealGeometricPowerMajorized x bound →
  PositiveGeometricPowerScaledUpperData (RealGeometricBound.ratioBound bound) →
  ℝᶜ
realGeometricPowerSumFromPowerData x bound majorant powerData =
  realGeometricPowerSumFromPositiveData
    x
    bound
    majorant
    (positiveGeometricTailDataFromPowerData
      (RealGeometricBound.ratioBound bound)
      powerData)


realGeometricCauchyApproximation :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (μ : ℚ⁺ → ℕ) →
  RealGeometricTailBound x terms μ →
  MetricCauchy.CauchyApproximation CauchyRealsMetricSpace
realGeometricCauchyApproximation x terms μ tailBound =
  seriesCauchyApproximationFromTailBound
    (RealGeometricTerms.term terms)
    μ
    tailBound


realGeometricSum :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (μ : ℚ⁺ → ℕ) →
  RealGeometricTailBound x terms μ →
  ℝᶜ
realGeometricSum x terms μ tailBound =
  seriesSum (RealGeometricTerms.term terms) μ tailBound


realGeometricConverges :
  (x : ℝᶜ) →
  (terms : RealGeometricTerms x) →
  (μ : ℚ⁺ → ℕ) →
  (tailBound : RealGeometricTailBound x terms μ) →
  MetricCauchy.ConvergesTo
    (realGeometricCauchyApproximation x terms μ tailBound)
    (realGeometricSum x terms μ tailBound)
realGeometricConverges x terms μ tailBound =
  seriesSumConverges (RealGeometricTerms.term terms) μ tailBound


RealGeometricConvergesWith :
  (x : ℝᶜ) →
  RealGeometricTerms x →
  Type₀
RealGeometricConvergesWith x terms =
  Σ[ μ ∈ (ℚ⁺ → ℕ) ] RealGeometricTailBound x terms μ
