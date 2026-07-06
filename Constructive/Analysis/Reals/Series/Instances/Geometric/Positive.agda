{-

Positive rational majorants for geometric series

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Series.Instances.Geometric.Positive where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax)
import Cubical.Data.Sum as Sum
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Metric.Instances.CauchyReals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.Series
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open import Constructive.Analysis.Reals.Series.Instances.Geometric.Algebra
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Rational

positivePower :
  ℚ⁺ →
  ℕ →
  ℚ⁺
positivePower ρ zero =
  1⁺
positivePower ρ (suc n) =
  ρ *⁺ positivePower ρ n


positivePower-radius :
  (ρ : ℚ⁺) →
  (n : ℕ) →
  radius (positivePower ρ n) ≡ rationalPower (radius ρ) n
positivePower-radius ρ zero =
  refl
positivePower-radius ρ (suc n) =
  cong (radius ρ ℚ.·_) (positivePower-radius ρ n)


positiveGeometricTerm :
  ℚ⁺ →
  ℕ →
  ℝᶜ
positiveGeometricTerm ρ n =
  rational (radius (positivePower ρ n))


positiveGeometricTerm-rational :
  (ρ : ℚ⁺) →
  (n : ℕ) →
  positiveGeometricTerm ρ n ≡ rationalGeometricTerm (radius ρ) n
positiveGeometricTerm-rational ρ n =
  cong rational (positivePower-radius ρ n)


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


PositiveGeometricFiniteTailBound :
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type₀
PositiveGeometricFiniteTailBound ρ μ =
  TailBound (positiveGeometricTerm ρ) μ


PositiveGeometricTailBound :
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type₀
PositiveGeometricTailBound ρ μ =
  SeriesTailBound (positiveGeometricTerm ρ) μ


PositiveGeometricTailUpperBound :
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type₀
PositiveGeometricTailUpperBound ρ μ =
  (ε : ℚ⁺) →
  (m k : ℕ) →
  NatOrder._≤_ (μ ε) m →
  tailSum (positiveGeometricTerm ρ) m k ≤ᶜ rational (radius ε)


PositiveGeometricSegmentUpperBound :
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type₀
PositiveGeometricSegmentUpperBound ρ μ =
  (ε : ℚ⁺) →
  (m k : ℕ) →
  NatOrder._≤_ (μ ε) m →
  rationalGeometricSegmentSumℚ (radius ρ) m k ℚOrder.≤ radius ε


positiveGeometricGap :
  ℚ⁺ →
  ℚ
positiveGeometricGap ρ =
  Rational.1ℚ ℚ.- radius ρ


positiveGeometricGap-positive :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  Rational.0ℚ ℚOrder.< positiveGeometricGap ρ
positiveGeometricGap-positive ρ ρ<1 =
  Rational.diff-positive {p = radius ρ} {q = Rational.1ℚ} ρ<1


positiveRationalPower-nonnegative :
  (ρ : ℚ⁺) →
  (n : ℕ) →
  Rational.0ℚ ℚOrder.≤ rationalPower (radius ρ) n
positiveRationalPower-nonnegative ρ n =
  Rational.<→≤
    {p = Rational.0ℚ}
    {q = rationalPower (radius ρ) n}
    (subst
      (λ q → Rational.0ℚ ℚOrder.< q)
      (positivePower-radius ρ n)
      (positivePower ρ n .snd))


positiveGeometricLinearFactor-positive :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (n : ℕ) →
  Rational.0ℚ ℚOrder.<
  Rational.1ℚ ℚ.+ Rational.natMul n (positiveGeometricGap ρ)
positiveGeometricLinearFactor-positive ρ ρ<1 n =
  subst
    (λ q → Rational.0ℚ ℚOrder.< q)
    (ℚ.+Comm (Rational.natMul n gap) Rational.1ℚ)
    (Rational.nonnegative-positive-sum
      {p = Rational.natMul n gap}
      {q = Rational.1ℚ}
      (Rational.natMul-nonnegative n gap>0)
      Rational.0<1)
  where
  gap : ℚ
  gap =
    positiveGeometricGap ρ

  gap>0 : Rational.0ℚ ℚOrder.< gap
  gap>0 =
    positiveGeometricGap-positive ρ ρ<1


positiveGeometricLinearFactor-step≤ :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (n : ℕ) →
  radius ρ ℚ.·
    ((Rational.1ℚ ℚ.+ Rational.natMul n (positiveGeometricGap ρ))
      ℚ.+ positiveGeometricGap ρ)
  ℚOrder.≤
  Rational.1ℚ ℚ.+ Rational.natMul n (positiveGeometricGap ρ)
positiveGeometricLinearFactor-step≤ ρ ρ<1 n =
  subst
    (λ x → x ℚOrder.≤ B)
    (sym factor-path)
    (Rational.diff≤right nonnegative-gap-term)
  where
  q : ℚ
  q =
    radius ρ

  gap : ℚ
  gap =
    positiveGeometricGap ρ

  N : ℚ
  N =
    Rational.natMul n gap

  B : ℚ
  B =
    Rational.1ℚ ℚ.+ N

  gap>0 : Rational.0ℚ ℚOrder.< gap
  gap>0 =
    positiveGeometricGap-positive ρ ρ<1

  N+gap>0 : Rational.0ℚ ℚOrder.< N ℚ.+ gap
  N+gap>0 =
    Rational.nonnegative-positive-sum
      {p = N}
      {q = gap}
      (Rational.natMul-nonnegative n gap>0)
      gap>0

  nonnegative-gap-term :
    Rational.0ℚ ℚOrder.≤ gap ℚ.· (N ℚ.+ gap)
  nonnegative-gap-term =
    Rational.mul-nonnegative
      {a = gap}
      {b = N ℚ.+ gap}
      (Rational.<→≤ {p = Rational.0ℚ} {q = gap} gap>0)
      (Rational.<→≤ {p = Rational.0ℚ} {q = N ℚ.+ gap} N+gap>0)

  factor-path :
    q ℚ.· (B ℚ.+ gap) ≡
    B ℚ.- (gap ℚ.· (N ℚ.+ gap))
  factor-path =
    SolverHelpers.linear-factor-step ℚCommRing q N


positiveGeometricPower-linear-bound :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (n : ℕ) →
  rationalPower (radius ρ) n ℚ.·
    (Rational.1ℚ ℚ.+ Rational.natMul n (positiveGeometricGap ρ))
  ℚOrder.≤
  Rational.1ℚ
positiveGeometricPower-linear-bound ρ ρ<1 zero =
  subst
    (λ q → q ℚOrder.≤ Rational.1ℚ)
    (sym zero-path)
    (Rational.≤-refl Rational.1ℚ)
  where
  zero-path :
    rationalPower (radius ρ) zero ℚ.·
      (Rational.1ℚ ℚ.+ Rational.natMul zero (positiveGeometricGap ρ))
    ≡
    Rational.1ℚ
  zero-path =
    cong
      (λ q → Rational.1ℚ ℚ.· (Rational.1ℚ ℚ.+ q))
      (Rational.natMul-zero (positiveGeometricGap ρ)) ∙
    SolverHelpers.linear-zero ℚCommRing
positiveGeometricPower-linear-bound ρ ρ<1 (suc n) =
  subst
    (λ q → q ℚOrder.≤ Rational.1ℚ)
    (sym step-path)
    (Rational.≤-trans
      (Rational.mul-left-nonnegative-≤
        (positiveRationalPower-nonnegative ρ n)
        (positiveGeometricLinearFactor-step≤ ρ ρ<1 n))
      (positiveGeometricPower-linear-bound ρ ρ<1 n))
  where
  q : ℚ
  q =
    radius ρ

  gap : ℚ
  gap =
    positiveGeometricGap ρ

  p : ℚ
  p =
    rationalPower q n

  N : ℚ
  N =
    Rational.natMul n gap

  step-path :
    rationalPower q (suc n) ℚ.·
      (Rational.1ℚ ℚ.+ Rational.natMul (suc n) gap)
    ≡
    p ℚ.· (q ℚ.· ((Rational.1ℚ ℚ.+ N) ℚ.+ gap))
  step-path =
    cong
      (λ v → (q ℚ.· p) ℚ.· (Rational.1ℚ ℚ.+ v))
      (Rational.natMul-suc n gap) ∙
    SolverHelpers.power-linear-step ℚCommRing q p N gap


positiveGeometricPowerStep :
  (ρ : ℚ⁺) →
  ℚ⁺ →
  ℚ
positiveGeometricPowerStep ρ ε =
  (radius ε ℚ.· positiveGeometricGap ρ) ℚ.· positiveGeometricGap ρ


positiveGeometricPowerStep-positive :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (ε : ℚ⁺) →
  Rational.0ℚ ℚOrder.< positiveGeometricPowerStep ρ ε
positiveGeometricPowerStep-positive ρ ρ<1 ε =
  Rational.mul-positive
    {a = radius ε ℚ.· gap}
    {b = gap}
    (Rational.mul-positive {a = radius ε} {b = gap} (ε .snd) gap>0)
    gap>0
  where
  gap : ℚ
  gap =
    positiveGeometricGap ρ

  gap>0 : Rational.0ℚ ℚOrder.< gap
  gap>0 =
    positiveGeometricGap-positive ρ ρ<1


positiveGeometricPowerModulus :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  ℚ⁺ →
  ℕ
positiveGeometricPowerModulus ρ ρ<1 ε =
  Rational.archimedean
    Rational.1ℚ
    (positiveGeometricPowerStep ρ ε)
    (positiveGeometricPowerStep-positive ρ ρ<1 ε)
    .fst


PositiveGeometricPowerScaledUpperBound :
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type₀
PositiveGeometricPowerScaledUpperBound ρ μ =
  (ε : ℚ⁺) →
  (m : ℕ) →
  NatOrder._≤_ (μ ε) m →
  rationalPower (radius ρ) m
  ℚOrder.≤
  radius ε ℚ.· positiveGeometricGap ρ


positiveGeometricPowerScaledUpperBoundFromRatio :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PositiveGeometricPowerScaledUpperBound
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
positiveGeometricPowerScaledUpperBoundFromRatio ρ ρ<1 ε m μ≤m =
  Rational.<→≤
    {p = rationalPower q m}
    {q = target}
    (ℚOrder.<-·o-cancel
      (rationalPower q m)
      target
      B
      B>0
      powerB<targetB)
  where
  q : ℚ
  q =
    radius ρ

  gap : ℚ
  gap =
    positiveGeometricGap ρ

  target : ℚ
  target =
    radius ε ℚ.· gap

  step : ℚ
  step =
    positiveGeometricPowerStep ρ ε

  N : ℚ
  N =
    Rational.natMul m gap

  B : ℚ
  B =
    Rational.1ℚ ℚ.+ N

  gap>0 : Rational.0ℚ ℚOrder.< gap
  gap>0 =
    positiveGeometricGap-positive ρ ρ<1

  target>0 : Rational.0ℚ ℚOrder.< target
  target>0 =
    Rational.mul-positive {a = radius ε} {b = gap} (ε .snd) gap>0

  step>0 : Rational.0ℚ ℚOrder.< step
  step>0 =
    positiveGeometricPowerStep-positive ρ ρ<1 ε

  B>0 : Rational.0ℚ ℚOrder.< B
  B>0 =
    positiveGeometricLinearFactor-positive ρ ρ<1 m

  μ : ℕ
  μ =
    positiveGeometricPowerModulus ρ ρ<1 ε

  one<μstep : Rational.1ℚ ℚOrder.< Rational.natMul μ step
  one<μstep =
    Rational.archimedean
      Rational.1ℚ
      step
      step>0
      .snd

  one<mstep : Rational.1ℚ ℚOrder.< Rational.natMul m step
  one<mstep =
    Rational.<≤-trans
      {p = Rational.1ℚ}
      {q = Rational.natMul μ step}
      {r = Rational.natMul m step}
      one<μstep
      (Rational.natMul-mono-≤ μ m step>0 μ≤m)

  one<targetN : Rational.1ℚ ℚOrder.< target ℚ.· N
  one<targetN =
    subst
      (λ x → Rational.1ℚ ℚOrder.< x)
      (Rational.natMul-mul-left m target gap)
      one<mstep

  N≤B : N ℚOrder.≤ B
  N≤B =
    subst
      (λ x → N ℚOrder.≤ x)
      (ℚ.+Comm N Rational.1ℚ)
      (Rational.<→≤
        {p = N}
        {q = N ℚ.+ Rational.1ℚ}
        (Rational.q<q+positive N Rational.1ℚ Rational.0<1))

  targetN≤targetB : target ℚ.· N ℚOrder.≤ target ℚ.· B
  targetN≤targetB =
    Rational.mul-left-nonnegative-≤
      (Rational.<→≤ {p = Rational.0ℚ} {q = target} target>0)
      N≤B

  one<targetB : Rational.1ℚ ℚOrder.< target ℚ.· B
  one<targetB =
    Rational.<≤-trans
      {p = Rational.1ℚ}
      {q = target ℚ.· N}
      {r = target ℚ.· B}
      one<targetN
      targetN≤targetB

  powerB≤1 :
    rationalPower q m ℚ.· B ℚOrder.≤ Rational.1ℚ
  powerB≤1 =
    positiveGeometricPower-linear-bound ρ ρ<1 m

  powerB<targetB :
    rationalPower q m ℚ.· B ℚOrder.< target ℚ.· B
  powerB<targetB =
    Rational.≤<-trans
      {p = rationalPower q m ℚ.· B}
      {q = Rational.1ℚ}
      {r = target ℚ.· B}
      powerB≤1
      one<targetB


positiveGeometricScaledSegment≤power :
  (ρ : ℚ⁺) →
  (m k : ℕ) →
  rationalGeometricSegmentSumℚ (radius ρ) m k
    ℚ.· positiveGeometricGap ρ
  ℚOrder.≤
  rationalPower (radius ρ) m
positiveGeometricScaledSegment≤power ρ m k =
  subst
    (λ x → x ℚOrder.≤ rationalPower q m)
    (sym segment-gap≡power-diff)
    (Rational.sub-nonnegative-right≤
      (positiveRationalPower-nonnegative ρ (m Nat.+ k)))
  where
  q : ℚ
  q =
    radius ρ

  segment-gap≡power-diff :
    rationalGeometricSegmentSumℚ q m k ℚ.· positiveGeometricGap ρ ≡
    rationalPower q m ℚ.- rationalPower q (m Nat.+ k)
  segment-gap≡power-diff =
    ℚ.·Comm
      (rationalGeometricSegmentSumℚ q m k)
      (positiveGeometricGap ρ) ∙
    rationalGeometricSegmentFiniteIdentity q m k


PositiveGeometricScaledSegmentUpperBound :
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type₀
PositiveGeometricScaledSegmentUpperBound ρ μ =
  (ε : ℚ⁺) →
  (m k : ℕ) →
  NatOrder._≤_ (μ ε) m →
  rationalGeometricSegmentSumℚ (radius ρ) m k
    ℚ.· positiveGeometricGap ρ
  ℚOrder.≤
  radius ε ℚ.· positiveGeometricGap ρ


positiveGeometricScaledSegmentUpperBoundFromPower :
  (ρ : ℚ⁺) →
  {μ : ℚ⁺ → ℕ} →
  PositiveGeometricPowerScaledUpperBound ρ μ →
  PositiveGeometricScaledSegmentUpperBound ρ μ
positiveGeometricScaledSegmentUpperBoundFromPower ρ powerUpper ε m k μ≤m =
  Rational.≤-trans
    {p = rationalGeometricSegmentSumℚ (radius ρ) m k
      ℚ.· positiveGeometricGap ρ}
    {q = rationalPower (radius ρ) m}
    {r = radius ε ℚ.· positiveGeometricGap ρ}
    (positiveGeometricScaledSegment≤power ρ m k)
    (powerUpper ε m μ≤m)


positiveGeometricSegmentUpperBoundFromScaled :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  {μ : ℚ⁺ → ℕ} →
  PositiveGeometricScaledSegmentUpperBound ρ μ →
  PositiveGeometricSegmentUpperBound ρ μ
positiveGeometricSegmentUpperBoundFromScaled ρ ρ<1 scaledUpper ε m k μ≤m =
  Rational.mul-right-cancel-positive-≤
    (positiveGeometricGap-positive ρ ρ<1)
    (scaledUpper ε m k μ≤m)


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


positiveGeometricTailUpperBoundFromSegment :
  (ρ : ℚ⁺) →
  {μ : ℚ⁺ → ℕ} →
  PositiveGeometricSegmentUpperBound ρ μ →
  PositiveGeometricTailUpperBound ρ μ
positiveGeometricTailUpperBoundFromSegment ρ segmentUpper ε m k μ≤m =
  subst
    (λ x → x ≤ᶜ rational (radius ε))
    (sym (positiveGeometricTailSum-segment ρ m k))
    (≤ℚ→rational≤ᶜ (segmentUpper ε m k μ≤m))


positiveGeometricFiniteTailBoundFromUpper :
  (ρ : ℚ⁺) →
  {μ : ℚ⁺ → ℕ} →
  PositiveGeometricTailUpperBound ρ μ →
  PositiveGeometricFiniteTailBound ρ μ
positiveGeometricFiniteTailBoundFromUpper ρ upper =
  nonnegative-tail-upper→TailBound
    (positiveGeometricTerm-nonnegative ρ)
    upper


positiveGeometricScaledSegmentUpperBoundFromRatio :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PositiveGeometricScaledSegmentUpperBound
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
positiveGeometricScaledSegmentUpperBoundFromRatio ρ ρ<1 =
  positiveGeometricScaledSegmentUpperBoundFromPower
    ρ
    (positiveGeometricPowerScaledUpperBoundFromRatio ρ ρ<1)


positiveGeometricSegmentUpperBoundFromRatio :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PositiveGeometricSegmentUpperBound
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
positiveGeometricSegmentUpperBoundFromRatio ρ ρ<1 =
  positiveGeometricSegmentUpperBoundFromScaled
    ρ
    ρ<1
    (positiveGeometricScaledSegmentUpperBoundFromRatio ρ ρ<1)


positiveGeometricTailUpperBoundFromRatio :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PositiveGeometricTailUpperBound
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
positiveGeometricTailUpperBoundFromRatio ρ ρ<1 =
  positiveGeometricTailUpperBoundFromSegment
    ρ
    (positiveGeometricSegmentUpperBoundFromRatio ρ ρ<1)


positiveGeometricFiniteTailBoundFromRatio :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PositiveGeometricFiniteTailBound
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
positiveGeometricFiniteTailBoundFromRatio ρ ρ<1 =
  positiveGeometricFiniteTailBoundFromUpper
    ρ
    (positiveGeometricTailUpperBoundFromRatio ρ ρ<1)


record PositiveGeometricTailData (ρ : ℚ⁺) : Type₀ where
  no-eta-equality

  field
    ratioBound<1 : radius ρ ℚOrder.< Rational.1ℚ
    modulus : ℚ⁺ → ℕ
    finiteTailBound : PositiveGeometricFiniteTailBound ρ modulus
    modulusAntitone : AntitoneTailModulus modulus


record PositiveGeometricTailUpperData (ρ : ℚ⁺) : Type₀ where
  no-eta-equality

  field
    ratioBound<1 : radius ρ ℚOrder.< Rational.1ℚ
    modulus : ℚ⁺ → ℕ
    tailUpperBound : PositiveGeometricTailUpperBound ρ modulus
    modulusAntitone : AntitoneTailModulus modulus


record PositiveGeometricSegmentUpperData (ρ : ℚ⁺) : Type₀ where
  no-eta-equality

  field
    ratioBound<1 : radius ρ ℚOrder.< Rational.1ℚ
    modulus : ℚ⁺ → ℕ
    segmentUpperBound : PositiveGeometricSegmentUpperBound ρ modulus
    modulusAntitone : AntitoneTailModulus modulus


record PositiveGeometricScaledSegmentUpperData (ρ : ℚ⁺) : Type₀ where
  no-eta-equality

  field
    ratioBound<1 : radius ρ ℚOrder.< Rational.1ℚ
    modulus : ℚ⁺ → ℕ
    scaledSegmentUpperBound : PositiveGeometricScaledSegmentUpperBound ρ modulus
    modulusAntitone : AntitoneTailModulus modulus


record PositiveGeometricPowerScaledUpperData (ρ : ℚ⁺) : Type₀ where
  no-eta-equality

  field
    ratioBound<1 : radius ρ ℚOrder.< Rational.1ℚ
    modulus : ℚ⁺ → ℕ
    powerScaledUpperBound : PositiveGeometricPowerScaledUpperBound ρ modulus
    modulusAntitone : AntitoneTailModulus modulus


positiveGeometricScaledSegmentUpperDataFromPowerData :
  (ρ : ℚ⁺) →
  PositiveGeometricPowerScaledUpperData ρ →
  PositiveGeometricScaledSegmentUpperData ρ
positiveGeometricScaledSegmentUpperDataFromPowerData ρ powerData =
  record
    { ratioBound<1 =
        PositiveGeometricPowerScaledUpperData.ratioBound<1 powerData
    ; modulus =
        PositiveGeometricPowerScaledUpperData.modulus powerData
    ; scaledSegmentUpperBound =
        positiveGeometricScaledSegmentUpperBoundFromPower
          ρ
          (PositiveGeometricPowerScaledUpperData.powerScaledUpperBound powerData)
    ; modulusAntitone =
        PositiveGeometricPowerScaledUpperData.modulusAntitone powerData
    }


positiveGeometricSegmentUpperDataFromScaledData :
  (ρ : ℚ⁺) →
  PositiveGeometricScaledSegmentUpperData ρ →
  PositiveGeometricSegmentUpperData ρ
positiveGeometricSegmentUpperDataFromScaledData ρ scaledData =
  record
    { ratioBound<1 =
        PositiveGeometricScaledSegmentUpperData.ratioBound<1 scaledData
    ; modulus =
        PositiveGeometricScaledSegmentUpperData.modulus scaledData
    ; segmentUpperBound =
        positiveGeometricSegmentUpperBoundFromScaled
          ρ
          (PositiveGeometricScaledSegmentUpperData.ratioBound<1 scaledData)
          (PositiveGeometricScaledSegmentUpperData.scaledSegmentUpperBound scaledData)
    ; modulusAntitone =
        PositiveGeometricScaledSegmentUpperData.modulusAntitone scaledData
    }


positiveGeometricTailUpperDataFromSegmentData :
  (ρ : ℚ⁺) →
  PositiveGeometricSegmentUpperData ρ →
  PositiveGeometricTailUpperData ρ
positiveGeometricTailUpperDataFromSegmentData ρ segmentData =
  record
    { ratioBound<1 =
        PositiveGeometricSegmentUpperData.ratioBound<1 segmentData
    ; modulus =
        PositiveGeometricSegmentUpperData.modulus segmentData
    ; tailUpperBound =
        positiveGeometricTailUpperBoundFromSegment
          ρ
          (PositiveGeometricSegmentUpperData.segmentUpperBound segmentData)
    ; modulusAntitone =
        PositiveGeometricSegmentUpperData.modulusAntitone segmentData
    }


positiveGeometricTailDataFromUpperData :
  (ρ : ℚ⁺) →
  PositiveGeometricTailUpperData ρ →
  PositiveGeometricTailData ρ
positiveGeometricTailDataFromUpperData ρ upperData =
  record
    { ratioBound<1 =
        PositiveGeometricTailUpperData.ratioBound<1 upperData
    ; modulus =
        PositiveGeometricTailUpperData.modulus upperData
    ; finiteTailBound =
        positiveGeometricFiniteTailBoundFromUpper
          ρ
          (PositiveGeometricTailUpperData.tailUpperBound upperData)
    ; modulusAntitone =
        PositiveGeometricTailUpperData.modulusAntitone upperData
    }


positiveGeometricTailDataFromSegmentData :
  (ρ : ℚ⁺) →
  PositiveGeometricSegmentUpperData ρ →
  PositiveGeometricTailData ρ
positiveGeometricTailDataFromSegmentData ρ segmentData =
  positiveGeometricTailDataFromUpperData
    ρ
    (positiveGeometricTailUpperDataFromSegmentData ρ segmentData)


positiveGeometricSegmentUpperDataFromPowerData :
  (ρ : ℚ⁺) →
  PositiveGeometricPowerScaledUpperData ρ →
  PositiveGeometricSegmentUpperData ρ
positiveGeometricSegmentUpperDataFromPowerData ρ powerData =
  positiveGeometricSegmentUpperDataFromScaledData
    ρ
    (positiveGeometricScaledSegmentUpperDataFromPowerData ρ powerData)


positiveGeometricTailDataFromPowerData :
  (ρ : ℚ⁺) →
  PositiveGeometricPowerScaledUpperData ρ →
  PositiveGeometricTailData ρ
positiveGeometricTailDataFromPowerData ρ powerData =
  positiveGeometricTailDataFromSegmentData
    ρ
    (positiveGeometricSegmentUpperDataFromPowerData ρ powerData)


positiveGeometricSeriesTailBound :
  (ρ : ℚ⁺) →
  (tailData : PositiveGeometricTailData ρ) →
  PositiveGeometricTailBound ρ
    (λ ε → PositiveGeometricTailData.modulus tailData (half⁺ ε))
positiveGeometricSeriesTailBound ρ tailData =
  tailBound→SeriesTailBound
    (PositiveGeometricTailData.finiteTailBound tailData)
    (PositiveGeometricTailData.modulusAntitone tailData)


positiveGeometricSum :
  (ρ : ℚ⁺) →
  PositiveGeometricTailData ρ →
  ℝᶜ
positiveGeometricSum ρ tailData =
  seriesSumFromFiniteTailBound
    (positiveGeometricTerm ρ)
    (PositiveGeometricTailData.modulus tailData)
    (PositiveGeometricTailData.finiteTailBound tailData)
    (PositiveGeometricTailData.modulusAntitone tailData)


positiveGeometricConverges :
  (ρ : ℚ⁺) →
  (tailData : PositiveGeometricTailData ρ) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromFiniteTailBound
      (positiveGeometricTerm ρ)
      (PositiveGeometricTailData.modulus tailData)
      (PositiveGeometricTailData.finiteTailBound tailData)
      (PositiveGeometricTailData.modulusAntitone tailData))
    (positiveGeometricSum ρ tailData)
positiveGeometricConverges ρ tailData =
  seriesSumFromFiniteTailBoundConverges
    (positiveGeometricTerm ρ)
    (PositiveGeometricTailData.modulus tailData)
    (PositiveGeometricTailData.finiteTailBound tailData)
    (PositiveGeometricTailData.modulusAntitone tailData)


positiveGeometricSeriesTailBoundFromUpperData :
  (ρ : ℚ⁺) →
  (upperData : PositiveGeometricTailUpperData ρ) →
  PositiveGeometricTailBound ρ
    (λ ε → PositiveGeometricTailUpperData.modulus upperData (half⁺ ε))
positiveGeometricSeriesTailBoundFromUpperData ρ upperData =
  positiveGeometricSeriesTailBound
    ρ
    (positiveGeometricTailDataFromUpperData ρ upperData)


positiveGeometricSumFromUpperData :
  (ρ : ℚ⁺) →
  PositiveGeometricTailUpperData ρ →
  ℝᶜ
positiveGeometricSumFromUpperData ρ upperData =
  positiveGeometricSum
    ρ
    (positiveGeometricTailDataFromUpperData ρ upperData)


positiveGeometricConvergesFromUpperData :
  (ρ : ℚ⁺) →
  (upperData : PositiveGeometricTailUpperData ρ) →
  MetricCauchy.ConvergesTo
    (seriesCauchyApproximationFromFiniteTailBound
      (positiveGeometricTerm ρ)
      (PositiveGeometricTailUpperData.modulus upperData)
      (positiveGeometricFiniteTailBoundFromUpper
        ρ
        (PositiveGeometricTailUpperData.tailUpperBound upperData))
      (PositiveGeometricTailUpperData.modulusAntitone upperData))
    (positiveGeometricSumFromUpperData ρ upperData)
positiveGeometricConvergesFromUpperData ρ upperData =
  positiveGeometricConverges
    ρ
    (positiveGeometricTailDataFromUpperData ρ upperData)


positiveGeometricSeriesTailBoundFromSegmentData :
  (ρ : ℚ⁺) →
  (segmentData : PositiveGeometricSegmentUpperData ρ) →
  PositiveGeometricTailBound ρ
    (λ ε → PositiveGeometricSegmentUpperData.modulus segmentData (half⁺ ε))
positiveGeometricSeriesTailBoundFromSegmentData ρ segmentData =
  positiveGeometricSeriesTailBound
    ρ
    (positiveGeometricTailDataFromSegmentData ρ segmentData)


positiveGeometricSumFromSegmentData :
  (ρ : ℚ⁺) →
  PositiveGeometricSegmentUpperData ρ →
  ℝᶜ
positiveGeometricSumFromSegmentData ρ segmentData =
  positiveGeometricSum
    ρ
    (positiveGeometricTailDataFromSegmentData ρ segmentData)


positiveGeometricSeriesTailBoundFromPowerData :
  (ρ : ℚ⁺) →
  (powerData : PositiveGeometricPowerScaledUpperData ρ) →
  PositiveGeometricTailBound ρ
    (λ ε → PositiveGeometricPowerScaledUpperData.modulus powerData (half⁺ ε))
positiveGeometricSeriesTailBoundFromPowerData ρ powerData =
  positiveGeometricSeriesTailBound
    ρ
    (positiveGeometricTailDataFromPowerData ρ powerData)


positiveGeometricSumFromPowerData :
  (ρ : ℚ⁺) →
  PositiveGeometricPowerScaledUpperData ρ →
  ℝᶜ
positiveGeometricSumFromPowerData ρ powerData =
  positiveGeometricSum
    ρ
    (positiveGeometricTailDataFromPowerData ρ powerData)
