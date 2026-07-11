{-

Positive-rational geometric decay rates

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.GeometricDecay.Rate where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.GeometricDecay.Algebra
open import Constructive.Analysis.GeometricDecay.Modulus
open import Constructive.Analysis.GeometricDecay.Rational
open import Constructive.Analysis.Modulus
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


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


ratioPowerTimesPositivePower :
  (ρ σ : ℚ⁺) →
  (n : ℕ) →
  rationalPower (radius (ratio⁺ ρ σ)) n ℚ.·
    radius (positivePower σ n)
  ≡
  radius (positivePower ρ n)
ratioPowerTimesPositivePower ρ σ n =
  cong
    (rationalPower (radius (ratio⁺ ρ σ)) n ℚ.·_)
    (positivePower-radius σ n) ∙
  rationalRatioPowerTimesPower
    (radius ρ)
    (radius σ)
    (σ .snd)
    n ∙
  sym (positivePower-radius ρ n)


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


positiveGeometricPowerScaledUpperBound :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (ε : ℚ⁺) →
  (m : ℕ) →
  NatOrder._≤_ (positiveGeometricPowerModulus ρ ρ<1 ε) m →
  rationalPower (radius ρ) m ℚOrder.≤
  radius ε ℚ.· positiveGeometricGap ρ
positiveGeometricPowerScaledUpperBound ρ ρ<1 ε m μ≤m =
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
    positiveGeometricPowerModulus-large ρ ρ<1 ε

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


positiveGeometricSegmentUpperBoundFromRatio :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (ε : ℚ⁺) →
  (m k : ℕ) →
  NatOrder._≤_ (positiveGeometricPowerModulus ρ ρ<1 ε) m →
  rationalGeometricSegmentSumℚ (radius ρ) m k ℚOrder.≤ radius ε
positiveGeometricSegmentUpperBoundFromRatio ρ ρ<1 ε m k μ≤m =
  Rational.mul-right-cancel-positive-≤
    (positiveGeometricGap-positive ρ ρ<1)
    (Rational.≤-trans
      {p = rationalGeometricSegmentSumℚ (radius ρ) m k
        ℚ.· positiveGeometricGap ρ}
      {q = rationalPower (radius ρ) m}
      {r = radius ε ℚ.· positiveGeometricGap ρ}
      (positiveGeometricScaledSegment≤power ρ m k)
      (positiveGeometricPowerScaledUpperBound ρ ρ<1 ε m μ≤m))


scaledGeometricSegmentModulus :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  ℚ⁺ →
  NatModulus
scaledGeometricSegmentModulus ρ ρ<1 η ε =
  positiveGeometricPowerModulus ρ ρ<1 (posInv⁺ η *⁺ ε)


scaledGeometricSegmentModulus-antitone :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (η : ℚ⁺) →
  AntitoneNatModulus (scaledGeometricSegmentModulus ρ ρ<1 η)
scaledGeometricSegmentModulus-antitone ρ ρ<1 η {ε = ε} {δ = δ} ε≤δ =
  positiveGeometricPowerModulus-antitone ρ ρ<1 scaled≤
  where
  scaled≤ :
    radius (posInv⁺ η *⁺ ε) ℚOrder.≤
    radius (posInv⁺ η *⁺ δ)
  scaled≤ =
    subst2
      ℚOrder._≤_
      (ℚ.·Comm (radius ε) (radius (posInv⁺ η)))
      (ℚ.·Comm (radius δ) (radius (posInv⁺ η)))
      (ℚOrder.≤-·o
        (radius ε)
        (radius δ)
        (radius (posInv⁺ η))
        (Rational.<→≤
          {p = Rational.0ℚ}
          {q = radius (posInv⁺ η)}
          (posInv⁺ η .snd))
        ε≤δ)


scaled-target-cancel :
  (η ε : ℚ⁺) →
  (posInv⁺ η *⁺ ε) *⁺ η ≡ ε
scaled-target-cancel η ε =
  *⁺-assoc (posInv⁺ η) ε η ∙
  cong (posInv⁺ η *⁺_) (*⁺-comm ε η) ∙
  sym (*⁺-assoc (posInv⁺ η) η ε) ∙
  cong (_*⁺ ε) (*⁺-posInv-left η) ∙
  *⁺-identity-left ε


scaledGeometricSegmentUpperBound :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (η : ℚ⁺) →
  (ε : ℚ⁺) →
  (m k : ℕ) →
  NatOrder._≤_ (scaledGeometricSegmentModulus ρ ρ<1 η ε) m →
  rationalGeometricSegmentSumℚ (radius ρ) m k ℚ.· radius η
  ℚOrder.≤
  radius ε
scaledGeometricSegmentUpperBound ρ ρ<1 η ε m k μ≤m =
  subst2
    ℚOrder._≤_
    refl
    (cong radius (scaled-target-cancel η ε))
    scaled≤
  where
  α : ℚ⁺
  α =
    posInv⁺ η *⁺ ε

  segment≤α :
    rationalGeometricSegmentSumℚ (radius ρ) m k
    ℚOrder.≤
    radius α
  segment≤α =
    positiveGeometricSegmentUpperBoundFromRatio ρ ρ<1 α m k μ≤m

  scaled≤ :
    rationalGeometricSegmentSumℚ (radius ρ) m k ℚ.· radius η
    ℚOrder.≤
    radius α ℚ.· radius η
  scaled≤ =
    ℚOrder.≤-·o
      (rationalGeometricSegmentSumℚ (radius ρ) m k)
      (radius α)
      (radius η)
      (Rational.<→≤ {p = Rational.0ℚ} {q = radius η} (η .snd))
      segment≤α


scaledGeometricSegment :
  (ρ η : ℚ⁺) →
  ℕ →
  ℕ →
  ℚ⁺
scaledGeometricSegment ρ η m zero =
  positivePower ρ m *⁺ η
scaledGeometricSegment ρ η m (suc k) =
  (positivePower ρ m *⁺ η) +⁺ scaledGeometricSegment ρ η (suc m) k


scaledGeometricSegment-radius :
  (ρ η : ℚ⁺) →
  (m k : ℕ) →
  radius (scaledGeometricSegment ρ η m k) ≡
  rationalGeometricSegmentSumℚ (radius ρ) m (suc k) ℚ.· radius η
scaledGeometricSegment-radius ρ η m zero =
  cong (λ q → q ℚ.· radius η) (positivePower-radius ρ m) ∙
  sym (ℚ.+IdR (rationalPower (radius ρ) m ℚ.· radius η)) ∙
  cong
    ((rationalPower (radius ρ) m ℚ.· radius η) ℚ.+_)
    (sym (ℚ.·AnnihilL (radius η))) ∙
  sym (ℚ.·DistR+ (rationalPower (radius ρ) m) Rational.0ℚ (radius η)) ∙
  refl
scaledGeometricSegment-radius ρ η m (suc k) =
  cong₂
    ℚ._+_
    (cong (λ q → q ℚ.· radius η) (positivePower-radius ρ m))
    (scaledGeometricSegment-radius ρ η (suc m) k) ∙
  sym
    (ℚ.·DistR+
      (rationalPower (radius ρ) m)
      (rationalGeometricSegmentSumℚ (radius ρ) (suc m) (suc k))
      (radius η))


scaledGeometricSegmentUpperBound⁺ :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (η : ℚ⁺) →
  (ε : ℚ⁺) →
  (m k : ℕ) →
  NatOrder._≤_ (scaledGeometricSegmentModulus ρ ρ<1 η ε) m →
  radius (scaledGeometricSegment ρ η m k) ℚOrder.≤ radius ε
scaledGeometricSegmentUpperBound⁺ ρ ρ<1 η ε m k μ≤m =
  subst
    (λ q → q ℚOrder.≤ radius ε)
    (sym (scaledGeometricSegment-radius ρ η m k))
    (scaledGeometricSegmentUpperBound ρ ρ<1 η ε m (suc k) μ≤m)
