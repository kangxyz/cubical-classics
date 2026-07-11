{-

Majorant bounds for strict-subball re-centering.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Recenter.Bounds where

open import Cubical.Foundations.Prelude

import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (fst ; snd)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
  using (add-interchange ; plus-minus-cancel-right)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
  using
    ( _·ᶜ_
    ; mulᶜ-assoc
    ; mulᶜ-comm
    ; mulᶜ-rational-left
    ; mulᶜ-rational-rational
    ; mulᶜ-rational-right
    )
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
  using (-ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using (scalarMulᶜ-nonnegative ; scalarMulᶜ-pres≤ᶜ-scalar)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
  using (scalarMulᶜ ; scalarMulᶜ-assoc ; scalarMulᶜ-one)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_ ; ≤ᶜ-refl ; ≤ᶜ-trans)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  using
    ( BoundedByᶜ
    ; bounded-byᶜ
    ; bounded-byᶜ-add
    ; bounded-byᶜ-monotone
    ; upperᶜ
    )
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using (absᶜ ; absᶜ-triangle ; absᶜ-zero ; ≤ᶜabsᶜ-left ; ≤ᶜabsᶜ-right)
open import Constructive.Analysis.Reals.CauchyReals.Order.Properties
  using (addᶜ-reflect≤ᶜ-left)
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
  using (≤ℚ→rational≤ᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
  using (≤ᶜ-add)
open import Constructive.Analysis.Reals.Series
  using
    ( SeriesMajorizedBy
    ; partialSum-append
    ; partialSum-comparison
    ; partialSum-mulLeft
    ; partialSum-nonnegative
    ; partialSum
    ; tailSum
    ; tailSum-nonnegative
    ; tailSum-suc-start
    )
open import Constructive.Analysis.Reals.Series.Rearrangement
  using (triangularRowsSumᶜ)
open import Constructive.Analysis.Reals.Series.Comparison
  using (seriesMajorizedByTerms ; tailSum-comparison)
open import Constructive.Analysis.Reals.Sequences.Algebra
  using (addConvergesTo ; negConvergesTo)
open import Constructive.Analysis.Reals.Sequences.Convergence
  using (ConvergesTo ; constantConvergesTo)
open import Constructive.Analysis.Reals.Sequences.Subsequence
  using (shiftConvergesWithModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Quantitative
  using
    ( absᶜ-mul≤product
    ; absᶜ-rational-nonnegative
    ; absᶜ-scalarMul≤
    ; bounded-byᶜ-abs≤rational
    ; mulᶜ-nonnegative
    ; tripleScalarProductPath
    )
open import Constructive.Analysis.GeometricDecay
  using (positivePower)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Power
  using (realPower ; realPowerBoundsFromBound)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Bounds
  using
    ( positiveRationalSelfBounded
    ; powerSeriesCoefficientFromRationalProbe
    ; realPower-rational-positive
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using (PowerSeriesMajorizedOnBall)
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Coefficients
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Binomial
  using (binomialᶜ ; binomialᶜ-natural ; binomialℕ)
open import Constructive.Analysis.Reals.PowerSeries.Recenter.FiniteSums
  using (powerSeriesPartialSum-recenterTriangle-shifted)
open import Constructive.Analysis.Reals.PowerSeries.Recenter.OuterConvergence
  using
    ( boundedByClosedFromConvergentApproximants
    ; recenterOuterTailApprox
    ; recenterOuterTailApproxConvergesToTail
    )
open import Constructive.Data.PositiveRationals
  using (ℚ⁺ ; radius ; _+⁺_ ; _*⁺_ ; posInv⁺)
import Constructive.Data.Rationals as Rational


recenterShiftedDisplacementBound :
  {δ τ σ : ℚ⁺} →
  {d h : ℝᶜ} →
  BoundedByᶜ δ d →
  BoundedByᶜ τ h →
  radius (δ +⁺ τ) ℚOrder.< radius σ →
  BoundedByᶜ σ (d +ᶜ h)
recenterShiftedDisplacementBound {δ = δ} {τ = τ} {σ = σ}
    {d = d} {h = h} d-bound h-bound margin =
  bounded-byᶜ-monotone
    (ℚOrder.<Weaken≤ (radius (δ +⁺ τ)) (radius σ) margin)
    (bounded-byᶜ-add δ τ d h d-bound h-bound)


normalizedMajorantPowerSeries :
  ℚ⁺ →
  (ℕ → ℝᶜ) →
  PowerSeries
normalizedMajorantPowerSeries ρ v n =
  scalarMulᶜ
    (radius (posInv⁺ (positivePower ρ n)))
    (v n)


private
  abs≤bounded-byᶜ :
    {ε : ℚ⁺} →
    {x : ℝᶜ} →
    absᶜ x ≤ᶜ rational (radius ε) →
    BoundedByᶜ ε x
  abs≤bounded-byᶜ {ε = ε} {x = x} abs≤ε =
    bounded-byᶜ
      (≤ᶜ-trans
        {x = x}
        {y = absᶜ x}
        {z = rational (radius ε)}
        (≤ᶜabsᶜ-left x)
        abs≤ε)
      (≤ᶜ-trans
        {x = -ᶜ x}
        {y = absᶜ x}
        {z = rational (radius ε)}
        (≤ᶜabsᶜ-right x)
        abs≤ε)

  partialSum≤longer :
    (u : ℕ → ℝᶜ) →
    ((n : ℕ) → 0ᶜ ≤ᶜ u n) →
    (m n : ℕ) →
    NatOrder._≤_ m n →
    partialSum u m ≤ᶜ partialSum u n
  partialSum≤longer u 0≤u m n (k , k+m≡n) =
    subst
      (λ x → partialSum u m ≤ᶜ x)
      (sym sum-path)
      partial≤partial+tail
    where
    m+k≡n : m Nat.+ k ≡ n
    m+k≡n =
      Nat.+-comm m k ∙ k+m≡n

    sum-path : partialSum u n ≡ partialSum u m +ᶜ tailSum u m k
    sum-path =
      sym (cong (partialSum u) m+k≡n) ∙
      partialSum-append u m k

    tail-nonnegative : 0ᶜ ≤ᶜ tailSum u m k
    tail-nonnegative =
      tailSum-nonnegative u 0≤u m k

    partial≤partial+tail :
      partialSum u m ≤ᶜ partialSum u m +ᶜ tailSum u m k
    partial≤partial+tail =
      subst
        (λ x → x ≤ᶜ partialSum u m +ᶜ tailSum u m k)
        (add-zero-right (partialSum u m))
        (≤ᶜ-add
          {a = partialSum u m}
          {b = partialSum u m}
          {c = 0ᶜ}
          {d = tailSum u m k}
          (≤ᶜ-refl (partialSum u m))
          tail-nonnegative)

  shiftedRowsTriangle :
    (ℕ → ℕ → ℝᶜ) →
    ℕ →
    ℕ →
    ℝᶜ
  shiftedRowsTriangle u m zero =
    0ᶜ
  shiftedRowsTriangle u m (suc L) =
    partialSum (u m) (suc L) +ᶜ
    shiftedRowsTriangle u (suc m) L

  shiftedRowsTriangle-suc-path :
    (u : ℕ → ℕ → ℝᶜ) →
    (m L : ℕ) →
    shiftedRowsTriangle u (suc m) L ≡
    shiftedRowsTriangle (λ n k → u (suc n) k) m L
  shiftedRowsTriangle-suc-path u m zero =
    refl
  shiftedRowsTriangle-suc-path u m (suc L) =
    cong
      (partialSum (u (suc m)) (suc L) +ᶜ_)
      (shiftedRowsTriangle-suc-path u (suc m) L)

  shiftedRowsTriangle-zero-path :
    (u : ℕ → ℕ → ℝᶜ) →
    (L : ℕ) →
    shiftedRowsTriangle u zero L ≡
    triangularRowsSumᶜ u L
  shiftedRowsTriangle-zero-path u zero =
    refl
  shiftedRowsTriangle-zero-path u (suc L) =
    cong
      (partialSum (u zero) (suc L) +ᶜ_)
      (shiftedRowsTriangle-suc-path u zero L ∙
       shiftedRowsTriangle-zero-path (λ n k → u (suc n) k) L)

  shiftedRowsTriangleNonnegative :
    (u : ℕ → ℕ → ℝᶜ) →
    ((n k : ℕ) → 0ᶜ ≤ᶜ u n k) →
    (m L : ℕ) →
    0ᶜ ≤ᶜ shiftedRowsTriangle u m L
  shiftedRowsTriangleNonnegative u 0≤u m zero =
    ≤ᶜ-refl 0ᶜ
  shiftedRowsTriangleNonnegative u 0≤u m (suc L) =
    ≤ᶜ-add
      {a = 0ᶜ}
      {b = partialSum (u m) (suc L)}
      {c = 0ᶜ}
      {d = shiftedRowsTriangle u (suc m) L}
      (partialSum-nonnegative (u m) (0≤u m) (suc L))
      (shiftedRowsTriangleNonnegative u 0≤u (suc m) L)

  trianglePrefixPlusShift≤Triangle :
    (u : ℕ → ℕ → ℝᶜ) →
    ((n k : ℕ) → 0ᶜ ≤ᶜ u n k) →
    (m L : ℕ) →
    triangularRowsSumᶜ u m +ᶜ shiftedRowsTriangle u m L ≤ᶜ
    triangularRowsSumᶜ u (m Nat.+ L)
  trianglePrefixPlusShift≤Triangle u 0≤u zero L =
    subst2
      _≤ᶜ_
      (sym
        (add-zero-left (shiftedRowsTriangle u zero L) ∙
         shiftedRowsTriangle-zero-path u L))
      refl
      (≤ᶜ-refl (triangularRowsSumᶜ u L))
  trianglePrefixPlusShift≤Triangle u 0≤u (suc m) L =
    subst2
      _≤ᶜ_
      (sym left-path)
      refl
      (≤ᶜ-add row≤longer rest≤triangle)
    where
    shifted : ℕ → ℕ → ℝᶜ
    shifted n k =
      u (suc n) k

    rowSmall : ℝᶜ
    rowSmall =
      partialSum (u zero) (suc m)

    rowBig : ℝᶜ
    rowBig =
      partialSum (u zero) (suc (m Nat.+ L))

    smallRest : ℝᶜ
    smallRest =
      triangularRowsSumᶜ shifted m

    shiftRest : ℝᶜ
    shiftRest =
      shiftedRowsTriangle u (suc m) L

    shiftedRest : ℝᶜ
    shiftedRest =
      shiftedRowsTriangle shifted m L

    left-path :
      (rowSmall +ᶜ smallRest) +ᶜ shiftRest ≡
      rowSmall +ᶜ (smallRest +ᶜ shiftedRest)
    left-path =
      sym (add-assoc rowSmall smallRest shiftRest) ∙
      cong
        (rowSmall +ᶜ_)
        (cong
          (smallRest +ᶜ_)
          (shiftedRowsTriangle-suc-path u m L))

    suc-m≤suc-m+L : NatOrder._≤_ (suc m) (suc (m Nat.+ L))
    suc-m≤suc-m+L =
      L ,
      (Nat.+-suc L m ∙
       cong suc (Nat.+-comm L m))

    row≤longer : rowSmall ≤ᶜ rowBig
    row≤longer =
      partialSum≤longer
        (u zero)
        (0≤u zero)
        (suc m)
        (suc (m Nat.+ L))
        suc-m≤suc-m+L

    rest≤triangle :
      smallRest +ᶜ shiftedRest ≤ᶜ
      triangularRowsSumᶜ shifted (m Nat.+ L)
    rest≤triangle =
      trianglePrefixPlusShift≤Triangle shifted (λ n k → 0≤u (suc n) k) m L

  prefixRemainderRows :
    (ℕ → ℕ → ℝᶜ) →
    ℕ →
    ℕ →
    ℕ →
    ℝᶜ
  prefixRemainderRows u m zero N =
    0ᶜ
  prefixRemainderRows u m (suc k) N =
    tailSum (u m) (suc k) N +ᶜ
    prefixRemainderRows u (suc m) k (suc N)

  prefixRemainderRowsNonnegative :
    (u : ℕ → ℕ → ℝᶜ) →
    ((n k : ℕ) → 0ᶜ ≤ᶜ u n k) →
    (m k N : ℕ) →
    0ᶜ ≤ᶜ prefixRemainderRows u m k N
  prefixRemainderRowsNonnegative u 0≤u m zero N =
    ≤ᶜ-refl 0ᶜ
  prefixRemainderRowsNonnegative u 0≤u m (suc k) N =
    ≤ᶜ-add
      {a = 0ᶜ}
      {b = tailSum (u m) (suc k) N}
      {c = 0ᶜ}
      {d = prefixRemainderRows u (suc m) k (suc N)}
      (tailSum-nonnegative (u m) (0≤u m) (suc k) N)
      (prefixRemainderRowsNonnegative u 0≤u (suc m) k (suc N))

  coefficientProbeBoundAt :
    {a : PowerSeries} →
    {ρ σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    BoundedByᶜ σ (rational (radius ρ)) →
    PowerSeriesMajorizedOnBall a σ v ν →
    (m : ℕ) →
    absᶜ (a m) ≤ᶜ
    scalarMulᶜ
      (radius (posInv⁺ (positivePower ρ m)))
      (v m)
  coefficientProbeBoundAt {a = a} {ρ = ρ} {σ = σ} {v = v} {ν = ν}
      probe-bound majorized m =
    subst
      (λ x →
        absᶜ x ≤ᶜ
        scalarMulᶜ
          (radius (posInv⁺ (positivePower ρ m)))
          (v m))
      (powerSeriesCoefficientFromRationalProbe ρ a m)
      (absᶜ-scalarMul≤
        invρm
        invρm-nonnegative
        v-nonnegative
        probe≤v)
    where
    invρm : ℚ
    invρm =
      radius (posInv⁺ (positivePower ρ m))

    invρm-nonnegative : Rational.0ℚ ℚOrder.≤ invρm
    invρm-nonnegative =
      Rational.<→≤
        {p = Rational.0ℚ}
        {q = invρm}
        (posInv⁺ (positivePower ρ m) .snd)

    v-nonnegative : 0ᶜ ≤ᶜ v m
    v-nonnegative =
      PowerSeriesMajorizedOnBall.majorantNonnegative
        {a = a}
        {ρ = σ}
        {v = v}
        {μ = ν}
        majorized
        m

    probe≤v :
      absᶜ (powerSeriesTerm a (rational (radius ρ)) m) ≤ᶜ v m
    probe≤v =
      SeriesMajorizedBy.termMajorized
        (PowerSeriesMajorizedOnBall.termMajorized
          {a = a}
          {ρ = σ}
          {v = v}
          {μ = ν}
          majorized
          (rational (radius ρ))
          probe-bound)
        zero
        m

  normalizedMajorantTermNonnegative :
    {a : PowerSeries} →
    {ρ σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    PowerSeriesMajorizedOnBall a σ v ν →
    (n : ℕ) →
    0ᶜ ≤ᶜ normalizedMajorantPowerSeries ρ v n
  normalizedMajorantTermNonnegative {a = a} {ρ = ρ} {σ = σ} {v = v} {ν = ν}
      majorized n =
    scalarMulᶜ-nonnegative
      invρn
      invρn-nonnegative
      {x = v n}
      (PowerSeriesMajorizedOnBall.majorantNonnegative
        {a = a}
        {ρ = σ}
        {v = v}
        {μ = ν}
        majorized
        n)
    where
    invρn : ℚ
    invρn =
      radius (posInv⁺ (positivePower ρ n))

    invρn-nonnegative : Rational.0ℚ ℚOrder.≤ invρn
    invρn-nonnegative =
      Rational.<→≤
        {p = Rational.0ℚ}
        {q = invρn}
        (posInv⁺ (positivePower ρ n) .snd)

  normalizedMajorantProbeTerm :
    (ρ : ℚ⁺) →
    (v : ℕ → ℝᶜ) →
    (n : ℕ) →
    powerSeriesTerm
      (normalizedMajorantPowerSeries ρ v)
      (rational (radius ρ))
      n
    ≡
    v n
  normalizedMajorantProbeTerm ρ v n =
    cong
      (normalizedMajorantPowerSeries ρ v n ·ᶜ_)
      (realPower-rational-positive ρ n) ∙
    mulᶜ-rational-right
      (normalizedMajorantPowerSeries ρ v n)
      ρⁿ ∙
    scalarMulᶜ-assoc ρⁿ invρⁿ (v n) ∙
    cong (λ q → scalarMulᶜ q (v n)) ρⁿ*invρⁿ≡1 ∙
    scalarMulᶜ-one (v n)
    where
    ρⁿ : ℚ
    ρⁿ =
      radius (positivePower ρ n)

    invρⁿ : ℚ
    invρⁿ =
      radius (posInv⁺ (positivePower ρ n))

    ρⁿ*invρⁿ≡1 : ρⁿ ℚ.· invρⁿ ≡ Rational.1ℚ
    ρⁿ*invρⁿ≡1 =
      Rational.posInv-right ρⁿ (positivePower ρ n .snd)

  normalizedRecenterMajorantProduct :
    (ρ δ τ : ℚ⁺) →
    (v : ℕ → ℝᶜ) →
    (n k : ℕ) →
    ℝᶜ
  normalizedRecenterMajorantProduct ρ δ τ v n k =
    (rational B ·ᶜ
      (scalarMulᶜ invρl (v l) ·ᶜ rational δpow)) ·ᶜ
    rational τpow
    where
    l : ℕ
    l =
      n Nat.+ k

    B : ℚ
    B =
      Rational.natMul (binomialℕ l n) Rational.1ℚ

    invρl : ℚ
    invρl =
      radius (posInv⁺ (positivePower ρ l))

    δpow : ℚ
    δpow =
      radius (positivePower δ k)

    τpow : ℚ
    τpow =
      radius (positivePower τ n)

  normalizedRecenterProductPath :
    (ρ δ τ : ℚ⁺) →
    (v : ℕ → ℝᶜ) →
    (n k : ℕ) →
    recenterCoefficientTerm
      (normalizedMajorantPowerSeries ρ v)
      (rational (radius δ))
      n
      k ·ᶜ
    realPower (rational (radius τ)) n
    ≡
    normalizedRecenterMajorantProduct ρ δ τ v n k
  normalizedRecenterProductPath ρ δ τ v n k =
    cong₂
      _·ᶜ_
      (recenterCoefficientTerm-full b (rational δR) n k ∙
       cong
        (λ p → binomialᶜ l n ·ᶜ b l ·ᶜ p)
        (realPower-rational-positive δ k))
      (realPower-rational-positive τ n) ∙
    cong
      (λ x → (x ·ᶜ b l ·ᶜ rational δpow) ·ᶜ rational τpow)
      (binomialᶜ-natural l n) ∙
    cong
      (_·ᶜ rational τpow)
      (sym
        (mulᶜ-assoc
          (rational B)
          coefficientMajorant
          (rational δpow)))
    where
    b : PowerSeries
    b =
      normalizedMajorantPowerSeries ρ v

    l : ℕ
    l =
      n Nat.+ k

    B : ℚ
    B =
      Rational.natMul (binomialℕ l n) Rational.1ℚ

    invρl : ℚ
    invρl =
      radius (posInv⁺ (positivePower ρ l))

    δR : ℚ
    δR =
      radius δ

    δpow : ℚ
    δpow =
      radius (positivePower δ k)

    τpow : ℚ
    τpow =
      radius (positivePower τ n)

    coefficientMajorant : ℝᶜ
    coefficientMajorant =
      scalarMulᶜ invρl (v l)

  normalizedRecenterTermNonnegative :
    {a : PowerSeries} →
    {ρ σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    (δ τ : ℚ⁺) →
    PowerSeriesMajorizedOnBall a σ v ν →
    (n k : ℕ) →
    0ᶜ ≤ᶜ
    recenterCoefficientTerm
      (normalizedMajorantPowerSeries ρ v)
      (rational (radius δ))
      n
      k ·ᶜ
    realPower (rational (radius τ)) n
  normalizedRecenterTermNonnegative
      {a = a}
      {ρ = ρ}
      {σ = σ}
      {v = v}
      {ν = ν}
      δ
      τ
      majorized
      n
      k =
    subst
      (λ x → 0ᶜ ≤ᶜ x)
      (sym (normalizedRecenterProductPath ρ δ τ v n k))
      product-nonnegative
    where
    l : ℕ
    l =
      n Nat.+ k

    B : ℚ
    B =
      Rational.natMul (binomialℕ l n) Rational.1ℚ

    invρl : ℚ
    invρl =
      radius (posInv⁺ (positivePower ρ l))

    δpow : ℚ
    δpow =
      radius (positivePower δ k)

    τpow : ℚ
    τpow =
      radius (positivePower τ n)

    coefficientMajorant : ℝᶜ
    coefficientMajorant =
      scalarMulᶜ invρl (v l)

    binomial-nonnegative : Rational.0ℚ ℚOrder.≤ B
    binomial-nonnegative =
      Rational.natMul-nonnegative (binomialℕ l n) Rational.0<1

    invρl-nonnegative : Rational.0ℚ ℚOrder.≤ invρl
    invρl-nonnegative =
      Rational.<→≤
        {p = Rational.0ℚ}
        {q = invρl}
        (posInv⁺ (positivePower ρ l) .snd)

    δpow-nonnegative : Rational.0ℚ ℚOrder.≤ δpow
    δpow-nonnegative =
      Rational.<→≤
        {p = Rational.0ℚ}
        {q = δpow}
        (positivePower δ k .snd)

    τpow-nonnegative : Rational.0ℚ ℚOrder.≤ τpow
    τpow-nonnegative =
      Rational.<→≤
        {p = Rational.0ℚ}
        {q = τpow}
        (positivePower τ n .snd)

    v-nonnegative : 0ᶜ ≤ᶜ v l
    v-nonnegative =
      PowerSeriesMajorizedOnBall.majorantNonnegative
        {a = a}
        {ρ = σ}
        {v = v}
        {μ = ν}
        majorized
        l

    coefficientMajorant-nonnegative : 0ᶜ ≤ᶜ coefficientMajorant
    coefficientMajorant-nonnegative =
      scalarMulᶜ-nonnegative invρl invρl-nonnegative v-nonnegative

    δpow-real-nonnegative : 0ᶜ ≤ᶜ rational δpow
    δpow-real-nonnegative =
      ≤ℚ→rational≤ᶜ
        {q = Rational.0ℚ}
        {r = δpow}
        δpow-nonnegative

    τpow-real-nonnegative : 0ᶜ ≤ᶜ rational τpow
    τpow-real-nonnegative =
      ≤ℚ→rational≤ᶜ
        {q = Rational.0ℚ}
        {r = τpow}
        τpow-nonnegative

    binomial-real-nonnegative : 0ᶜ ≤ᶜ rational B
    binomial-real-nonnegative =
      ≤ℚ→rational≤ᶜ
        {q = Rational.0ℚ}
        {r = B}
        binomial-nonnegative

    coefficientTimesD-nonnegative :
      0ᶜ ≤ᶜ coefficientMajorant ·ᶜ rational δpow
    coefficientTimesD-nonnegative =
      mulᶜ-nonnegative
        coefficientMajorant
        (rational δpow)
        coefficientMajorant-nonnegative
        δpow-real-nonnegative

    binomialProduct-nonnegative :
      0ᶜ ≤ᶜ rational B ·ᶜ (coefficientMajorant ·ᶜ rational δpow)
    binomialProduct-nonnegative =
      mulᶜ-nonnegative
        (rational B)
        (coefficientMajorant ·ᶜ rational δpow)
        binomial-real-nonnegative
        coefficientTimesD-nonnegative

    product-nonnegative :
      0ᶜ ≤ᶜ normalizedRecenterMajorantProduct ρ δ τ v n k
    product-nonnegative =
      mulᶜ-nonnegative
        (rational B ·ᶜ (coefficientMajorant ·ᶜ rational δpow))
        (rational τpow)
        binomialProduct-nonnegative
        τpow-real-nonnegative

  recenterTerm≤normalizedMajorantTerm :
    {a : PowerSeries} →
    {δ τ σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    {d h : ℝᶜ} →
    BoundedByᶜ δ d →
    BoundedByᶜ τ h →
    BoundedByᶜ σ (rational (radius (δ +⁺ τ))) →
    PowerSeriesMajorizedOnBall a σ v ν →
    (n k : ℕ) →
    absᶜ
      (recenterCoefficientTerm a d n k ·ᶜ realPower h n)
    ≤ᶜ
    recenterCoefficientTerm
      (normalizedMajorantPowerSeries (δ +⁺ τ) v)
      (rational (radius δ))
      n
      k ·ᶜ
    realPower (rational (radius τ)) n
  recenterTerm≤normalizedMajorantTerm
      {a = a}
      {δ = δ}
      {τ = τ}
      {σ = σ}
      {v = v}
      {ν = ν}
      {d = d}
      {h = h}
      d-bound
      h-bound
      probe-bound
      majorized
      n
      k =
    ≤ᶜ-trans
      {x = absᶜ (recenterCoefficientTerm a d n k ·ᶜ hpow)}
      {y = productMajorant}
      {z =
        recenterCoefficientTerm b (rational δR) n k ·ᶜ
        realPower (rational τR) n}
      term≤product
      product≤normalized
    where
    ρ : ℚ⁺
    ρ =
      δ +⁺ τ

    b : PowerSeries
    b =
      normalizedMajorantPowerSeries ρ v

    l : ℕ
    l =
      n Nat.+ k

    B : ℚ
    B =
      Rational.natMul (binomialℕ l n) Rational.1ℚ

    invρl : ℚ
    invρl =
      radius (posInv⁺ (positivePower ρ l))

    δR : ℚ
    δR =
      radius δ

    τR : ℚ
    τR =
      radius τ

    δpow : ℚ
    δpow =
      radius (positivePower δ k)

    τpow : ℚ
    τpow =
      radius (positivePower τ n)

    dpow : ℝᶜ
    dpow =
      realPower d k

    hpow : ℝᶜ
    hpow =
      realPower h n

    coefficientMajorant : ℝᶜ
    coefficientMajorant =
      scalarMulᶜ invρl (v l)

    coefficientTimesD : ℝᶜ
    coefficientTimesD =
      coefficientMajorant ·ᶜ rational δpow

    binomialProductMajorant : ℝᶜ
    binomialProductMajorant =
      rational B ·ᶜ coefficientTimesD

    productMajorant : ℝᶜ
    productMajorant =
      binomialProductMajorant ·ᶜ rational τpow

    binomial-nonnegative : Rational.0ℚ ℚOrder.≤ B
    binomial-nonnegative =
      Rational.natMul-nonnegative (binomialℕ l n) Rational.0<1

    invρl-nonnegative : Rational.0ℚ ℚOrder.≤ invρl
    invρl-nonnegative =
      Rational.<→≤
        {p = Rational.0ℚ}
        {q = invρl}
        (posInv⁺ (positivePower ρ l) .snd)

    δpow-nonnegative : Rational.0ℚ ℚOrder.≤ δpow
    δpow-nonnegative =
      Rational.<→≤
        {p = Rational.0ℚ}
        {q = δpow}
        (positivePower δ k .snd)

    τpow-nonnegative : Rational.0ℚ ℚOrder.≤ τpow
    τpow-nonnegative =
      Rational.<→≤
        {p = Rational.0ℚ}
        {q = τpow}
        (positivePower τ n .snd)

    v-nonnegative : 0ᶜ ≤ᶜ v l
    v-nonnegative =
      PowerSeriesMajorizedOnBall.majorantNonnegative
        {a = a}
        {ρ = σ}
        {v = v}
        {μ = ν}
        majorized
        l

    coefficientMajorant-nonnegative : 0ᶜ ≤ᶜ coefficientMajorant
    coefficientMajorant-nonnegative =
      scalarMulᶜ-nonnegative invρl invρl-nonnegative v-nonnegative

    δpow-real-nonnegative : 0ᶜ ≤ᶜ rational δpow
    δpow-real-nonnegative =
      ≤ℚ→rational≤ᶜ
        {q = Rational.0ℚ}
        {r = δpow}
        δpow-nonnegative

    τpow-real-nonnegative : 0ᶜ ≤ᶜ rational τpow
    τpow-real-nonnegative =
      ≤ℚ→rational≤ᶜ
        {q = Rational.0ℚ}
        {r = τpow}
        τpow-nonnegative

    coefficientTimesD-nonnegative : 0ᶜ ≤ᶜ coefficientTimesD
    coefficientTimesD-nonnegative =
      mulᶜ-nonnegative
        coefficientMajorant
        (rational δpow)
        coefficientMajorant-nonnegative
        δpow-real-nonnegative

    binomial-real-nonnegative : 0ᶜ ≤ᶜ rational B
    binomial-real-nonnegative =
      ≤ℚ→rational≤ᶜ
        {q = Rational.0ℚ}
        {r = B}
        binomial-nonnegative

    binomialProductMajorant-nonnegative : 0ᶜ ≤ᶜ binomialProductMajorant
    binomialProductMajorant-nonnegative =
      mulᶜ-nonnegative
        (rational B)
        coefficientTimesD
        binomial-real-nonnegative
        coefficientTimesD-nonnegative

    binomial≤majorant :
      absᶜ (binomialᶜ l n) ≤ᶜ rational B
    binomial≤majorant =
      subst
        (λ x → absᶜ x ≤ᶜ rational B)
        (sym (binomialᶜ-natural l n))
        (absᶜ-rational-nonnegative B binomial-nonnegative)

    coefficient≤majorant :
      absᶜ (a l) ≤ᶜ coefficientMajorant
    coefficient≤majorant =
      coefficientProbeBoundAt
        {a = a}
        {ρ = ρ}
        {σ = σ}
        {v = v}
        {ν = ν}
        probe-bound
        majorized
        l

    d-power≤majorant :
      absᶜ dpow ≤ᶜ rational δpow
    d-power≤majorant =
      bounded-byᶜ-abs≤rational
        (realPowerBoundsFromBound δ d d-bound k)

    h-power≤majorant :
      absᶜ hpow ≤ᶜ rational τpow
    h-power≤majorant =
      bounded-byᶜ-abs≤rational
        (realPowerBoundsFromBound τ h h-bound n)

    coefficient-power≤majorant :
      absᶜ (a l ·ᶜ dpow) ≤ᶜ coefficientTimesD
    coefficient-power≤majorant =
      absᶜ-mul≤product
        (a l)
        dpow
        coefficientMajorant
        (rational δpow)
        coefficientMajorant-nonnegative
        δpow-real-nonnegative
        coefficient≤majorant
        d-power≤majorant

    factored≤majorant :
      absᶜ (binomialᶜ l n ·ᶜ (a l ·ᶜ dpow)) ≤ᶜ
      binomialProductMajorant
    factored≤majorant =
      absᶜ-mul≤product
        (binomialᶜ l n)
        (a l ·ᶜ dpow)
        (rational B)
        coefficientTimesD
        binomial-real-nonnegative
        coefficientTimesD-nonnegative
        binomial≤majorant
        coefficient-power≤majorant

    coefficientTerm≤majorant :
      absᶜ (recenterCoefficientTerm a d n k) ≤ᶜ
      binomialProductMajorant
    coefficientTerm≤majorant =
      subst
        (λ x → absᶜ x ≤ᶜ binomialProductMajorant)
        (sym
          (recenterCoefficientTerm-full a d n k ∙
           sym (mulᶜ-assoc (binomialᶜ l n) (a l) dpow)))
        factored≤majorant

    term≤product :
      absᶜ (recenterCoefficientTerm a d n k ·ᶜ hpow) ≤ᶜ
      productMajorant
    term≤product =
      absᶜ-mul≤product
        (recenterCoefficientTerm a d n k)
        hpow
        binomialProductMajorant
        (rational τpow)
        binomialProductMajorant-nonnegative
        τpow-real-nonnegative
        coefficientTerm≤majorant
        h-power≤majorant

    normalized-product-path :
      recenterCoefficientTerm b (rational δR) n k ·ᶜ
      realPower (rational τR) n
      ≡
      productMajorant
    normalized-product-path =
      cong₂
        _·ᶜ_
        (recenterCoefficientTerm-full b (rational δR) n k ∙
         cong
          (λ p → binomialᶜ l n ·ᶜ b l ·ᶜ p)
          (realPower-rational-positive δ k))
        (realPower-rational-positive τ n) ∙
      cong
        (λ x → (x ·ᶜ b l ·ᶜ rational δpow) ·ᶜ rational τpow)
        (binomialᶜ-natural l n) ∙
      cong
        (_·ᶜ rational τpow)
        (sym
          (mulᶜ-assoc
            (rational B)
            coefficientMajorant
            (rational δpow)))

    product≤normalized :
      productMajorant ≤ᶜ
      recenterCoefficientTerm b (rational δR) n k ·ᶜ
      realPower (rational τR) n
    product≤normalized =
      subst
        (λ x → productMajorant ≤ᶜ x)
        (sym normalized-product-path)
        (≤ᶜ-refl productMajorant)

  rowRightMulPartialSum :
    (u : ℕ → ℝᶜ) →
    (x : ℝᶜ) →
    (N : ℕ) →
    partialSum u N ·ᶜ x ≡
    partialSum (λ k → u k ·ᶜ x) N
  rowRightMulPartialSum u x N =
    mulᶜ-comm (partialSum u N) x ∙
    sym (partialSum-mulLeft x u N) ∙
    cong
      (λ w → partialSum w N)
      (funExt λ k → mulᶜ-comm x (u k))

  recenterOuterTailApprox-prefixRemainder :
    (a : PowerSeries) →
    (d h : ℝᶜ) →
    (m k N : ℕ) →
    recenterOuterTailApprox a d h m k (k Nat.+ N) ≡
    shiftedRowsTriangle
      (λ n j →
        recenterCoefficientTerm a d n j ·ᶜ
        realPower h n)
      m
      k
    +ᶜ
    prefixRemainderRows
      (λ n j →
        recenterCoefficientTerm a d n j ·ᶜ
        realPower h n)
      m
      k
      N
  recenterOuterTailApprox-prefixRemainder a d h m zero N =
    sym (add-zero-left 0ᶜ)
  recenterOuterTailApprox-prefixRemainder a d h m (suc k) N =
    cong₂
      _+ᶜ_
      (rowRightMulPartialSum
        (recenterCoefficientTerm a d m)
        (realPower h m)
        (suc k Nat.+ N) ∙
       partialSum-append rowTerm (suc k) N)
      rest-path ∙
    add-interchange
      rowTriangle
      rowRemainder
      restTriangle
      restRemainder
    where
    rowTerm : ℕ → ℝᶜ
    rowTerm j =
      recenterCoefficientTerm a d m j ·ᶜ
      realPower h m

    shiftedTerm : ℕ → ℕ → ℝᶜ
    shiftedTerm n j =
      recenterCoefficientTerm a d (suc m Nat.+ n) j ·ᶜ
      realPower h (suc m Nat.+ n)

    rowTriangle : ℝᶜ
    rowTriangle =
      partialSum rowTerm (suc k)

    rowRemainder : ℝᶜ
    rowRemainder =
      tailSum rowTerm (suc k) N

    restTriangle : ℝᶜ
    restTriangle =
      shiftedRowsTriangle
        (λ n j →
          recenterCoefficientTerm a d n j ·ᶜ
          realPower h n)
        (suc m)
        k

    restRemainder : ℝᶜ
    restRemainder =
      prefixRemainderRows
        (λ n j →
          recenterCoefficientTerm a d n j ·ᶜ
          realPower h n)
        (suc m)
        k
        (suc N)

    rest-index-path : suc k Nat.+ N ≡ k Nat.+ suc N
    rest-index-path =
      sym (Nat.+-suc k N)

    rest-path :
      recenterOuterTailApprox a d h (suc m) k (suc k Nat.+ N) ≡
      restTriangle +ᶜ restRemainder
    rest-path =
      subst
        (λ L →
          recenterOuterTailApprox a d h (suc m) k L ≡
          restTriangle +ᶜ restRemainder)
        (sym rest-index-path)
        (recenterOuterTailApprox-prefixRemainder
          a
          d
          h
          (suc m)
          k
          (suc N))

  normalizedShiftedTriangle :
    (ρ δ τ : ℚ⁺) →
    (v : ℕ → ℝᶜ) →
    (m L : ℕ) →
    ℝᶜ
  normalizedShiftedTriangle ρ δ τ v m L =
    shiftedRowsTriangle
      (λ n k →
        recenterCoefficientTerm
          (normalizedMajorantPowerSeries ρ v)
          (rational (radius δ))
          n
          k ·ᶜ
        realPower (rational (radius τ)) n)
      m
      L

  normalizedShiftedTriangleNonnegative :
    {a : PowerSeries} →
    {ρ σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    (δ τ : ℚ⁺) →
    PowerSeriesMajorizedOnBall a σ v ν →
    (m L : ℕ) →
    0ᶜ ≤ᶜ normalizedShiftedTriangle ρ δ τ v m L
  normalizedShiftedTriangleNonnegative δ τ majorized m zero =
    ≤ᶜ-refl 0ᶜ
  normalizedShiftedTriangleNonnegative
      {a = a}
      {ρ = ρ}
      {σ = σ}
      {v = v}
      {ν = ν}
      δ
      τ
      majorized
      m
      (suc L) =
    ≤ᶜ-add
      {a = 0ᶜ}
      {b = row}
      {c = 0ᶜ}
      {d = rest}
      row-nonnegative
      rest-nonnegative
    where
    b : PowerSeries
    b =
      normalizedMajorantPowerSeries ρ v

    row : ℝᶜ
    row =
      partialSum
        (λ k →
          recenterCoefficientTerm b (rational (radius δ)) m k ·ᶜ
          realPower (rational (radius τ)) m)
        (suc L)

    rest : ℝᶜ
    rest =
      normalizedShiftedTriangle ρ δ τ v (suc m) L

    row-nonnegative : 0ᶜ ≤ᶜ row
    row-nonnegative =
      partialSum-nonnegative
        (λ k →
          recenterCoefficientTerm b (rational (radius δ)) m k ·ᶜ
          realPower (rational (radius τ)) m)
        (normalizedRecenterTermNonnegative
          {a = a}
          {ρ = ρ}
          {σ = σ}
          {v = v}
          {ν = ν}
          δ
          τ
          majorized
          m)
        (suc L)

    rest-nonnegative : 0ᶜ ≤ᶜ rest
    rest-nonnegative =
      normalizedShiftedTriangleNonnegative
        {a = a}
        {ρ = ρ}
        {σ = σ}
        {v = v}
        {ν = ν}
        δ
        τ
        majorized
        (suc m)
        L

  normalizedRectangle≤shiftedTriangle :
    {a : PowerSeries} →
    {ρ σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    (δ τ : ℚ⁺) →
    PowerSeriesMajorizedOnBall a σ v ν →
    (m k N : ℕ) →
    recenterOuterTailApprox
      (normalizedMajorantPowerSeries ρ v)
      (rational (radius δ))
      (rational (radius τ))
      m
      k
      N
    ≤ᶜ
    normalizedShiftedTriangle ρ δ τ v m (k Nat.+ N)
  normalizedRectangle≤shiftedTriangle δ τ majorized m zero N =
    normalizedShiftedTriangleNonnegative δ τ majorized m N
  normalizedRectangle≤shiftedTriangle
      {a = a}
      {ρ = ρ}
      {σ = σ}
      {v = v}
      {ν = ν}
      δ
      τ
      majorized
      m
      (suc k)
      N =
    ≤ᶜ-add
      {a = rowRectangle}
      {b = rowTriangle}
      {c = restRectangle}
      {d = restTriangle}
      row≤triangle
      rest≤triangle
    where
    b : PowerSeries
    b =
      normalizedMajorantPowerSeries ρ v

    rowTerm : ℕ → ℝᶜ
    rowTerm j =
      recenterCoefficientTerm b (rational (radius δ)) m j ·ᶜ
      realPower (rational (radius τ)) m

    rowRectangle : ℝᶜ
    rowRectangle =
      partialSum (recenterCoefficientTerm b (rational (radius δ)) m) N ·ᶜ
      realPower (rational (radius τ)) m

    rowTriangle : ℝᶜ
    rowTriangle =
      partialSum rowTerm (suc (k Nat.+ N))

    restRectangle : ℝᶜ
    restRectangle =
      recenterOuterTailApprox
        b
        (rational (radius δ))
        (rational (radius τ))
        (suc m)
        k
        N

    restTriangle : ℝᶜ
    restTriangle =
      normalizedShiftedTriangle ρ δ τ v (suc m) (k Nat.+ N)

    N≤suc-k+N : NatOrder._≤_ N (suc (k Nat.+ N))
    N≤suc-k+N =
      suc k , refl

    row≤triangle :
      rowRectangle ≤ᶜ rowTriangle
    row≤triangle =
      subst
        (λ x → x ≤ᶜ rowTriangle)
        (sym
          (rowRightMulPartialSum
          (recenterCoefficientTerm b (rational (radius δ)) m)
          (realPower (rational (radius τ)) m)
          N))
        (partialSum≤longer
          rowTerm
          (normalizedRecenterTermNonnegative
            {a = a}
            {ρ = ρ}
            {σ = σ}
            {v = v}
            {ν = ν}
            δ
            τ
            majorized
            m)
          N
          (suc (k Nat.+ N))
          N≤suc-k+N)

    rest≤triangle :
      restRectangle ≤ᶜ restTriangle
    rest≤triangle =
      normalizedRectangle≤shiftedTriangle
        {a = a}
        {ρ = ρ}
        {σ = σ}
        {v = v}
        {ν = ν}
        δ
        τ
        majorized
        (suc m)
        k
        N

  recenterOuterTailApprox≤normalizedMajorantApprox :
    {a : PowerSeries} →
    {δ τ σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    {d h : ℝᶜ} →
    BoundedByᶜ δ d →
    BoundedByᶜ τ h →
    BoundedByᶜ σ (rational (radius (δ +⁺ τ))) →
    PowerSeriesMajorizedOnBall a σ v ν →
    (m k N : ℕ) →
    absᶜ (recenterOuterTailApprox a d h m k N) ≤ᶜ
    recenterOuterTailApprox
      (normalizedMajorantPowerSeries (δ +⁺ τ) v)
      (rational (radius δ))
      (rational (radius τ))
      m
      k
      N
  recenterOuterTailApprox≤normalizedMajorantApprox
      d-bound h-bound probe-bound majorized m zero N =
    subst
      (λ x → x ≤ᶜ 0ᶜ)
      (sym absᶜ-zero)
      (≤ᶜ-refl 0ᶜ)
  recenterOuterTailApprox≤normalizedMajorantApprox
      {a = a}
      {δ = δ}
      {τ = τ}
      {σ = σ}
      {v = v}
      {ν = ν}
      {d = d}
      {h = h}
      d-bound
      h-bound
      probe-bound
      majorized
      m
      (suc k)
      N =
    ≤ᶜ-trans
      {x = absᶜ (row +ᶜ rest)}
      {y = absᶜ row +ᶜ absᶜ rest}
      {z = rowMajor +ᶜ restMajor}
      (absᶜ-triangle row rest)
      (≤ᶜ-add row≤major rest≤major)
    where
    ρ : ℚ⁺
    ρ =
      δ +⁺ τ

    b : PowerSeries
    b =
      normalizedMajorantPowerSeries ρ v

    row : ℝᶜ
    row =
      partialSum (recenterCoefficientTerm a d m) N ·ᶜ
      realPower h m

    rest : ℝᶜ
    rest =
      recenterOuterTailApprox a d h (suc m) k N

    rowMajor : ℝᶜ
    rowMajor =
      partialSum (recenterCoefficientTerm b (rational (radius δ)) m) N ·ᶜ
      realPower (rational (radius τ)) m

    restMajor : ℝᶜ
    restMajor =
      recenterOuterTailApprox
        b
        (rational (radius δ))
        (rational (radius τ))
        (suc m)
        k
        N

    row≤major :
      absᶜ row ≤ᶜ rowMajor
    row≤major =
      subst2
        _≤ᶜ_
        (sym
          (cong absᶜ
            (rowRightMulPartialSum
              (recenterCoefficientTerm a d m)
              (realPower h m)
              N)))
        (sym
          (rowRightMulPartialSum
            (recenterCoefficientTerm b (rational (radius δ)) m)
            (realPower (rational (radius τ)) m)
            N))
        (partialSum-comparison
          (λ j →
            recenterCoefficientTerm a d m j ·ᶜ
            realPower h m)
          (λ j →
            recenterCoefficientTerm b (rational (radius δ)) m j ·ᶜ
            realPower (rational (radius τ)) m)
          (recenterTerm≤normalizedMajorantTerm
            d-bound
            h-bound
            probe-bound
            majorized
            m)
          N)

    rest≤major :
      absᶜ rest ≤ᶜ restMajor
    rest≤major =
      recenterOuterTailApprox≤normalizedMajorantApprox
        d-bound
        h-bound
        probe-bound
        majorized
        (suc m)
        k
        N

  prefixRemainderRows≤normalizedMajorant :
    {a : PowerSeries} →
    {δ τ σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    {d h : ℝᶜ} →
    BoundedByᶜ δ d →
    BoundedByᶜ τ h →
    BoundedByᶜ σ (rational (radius (δ +⁺ τ))) →
    PowerSeriesMajorizedOnBall a σ v ν →
    (m k N : ℕ) →
    absᶜ
      (prefixRemainderRows
        (λ n j →
          recenterCoefficientTerm a d n j ·ᶜ
          realPower h n)
        m
        k
        N)
    ≤ᶜ
    prefixRemainderRows
      (λ n j →
        recenterCoefficientTerm
          (normalizedMajorantPowerSeries (δ +⁺ τ) v)
          (rational (radius δ))
          n
          j ·ᶜ
        realPower (rational (radius τ)) n)
      m
      k
      N
  prefixRemainderRows≤normalizedMajorant
      d-bound h-bound probe-bound majorized m zero N =
    subst
      (λ x → x ≤ᶜ 0ᶜ)
      (sym absᶜ-zero)
      (≤ᶜ-refl 0ᶜ)
  prefixRemainderRows≤normalizedMajorant
      {a = a}
      {δ = δ}
      {τ = τ}
      {σ = σ}
      {v = v}
      {ν = ν}
      {d = d}
      {h = h}
      d-bound
      h-bound
      probe-bound
      majorized
      m
      (suc k)
      N =
    ≤ᶜ-trans
      {x = absᶜ (row +ᶜ rest)}
      {y = absᶜ row +ᶜ absᶜ rest}
      {z = rowMajor +ᶜ restMajor}
      (absᶜ-triangle row rest)
      (≤ᶜ-add row≤major rest≤major)
    where
    ρ : ℚ⁺
    ρ =
      δ +⁺ τ

    b : PowerSeries
    b =
      normalizedMajorantPowerSeries ρ v

    row : ℝᶜ
    row =
      tailSum
        (λ j →
          recenterCoefficientTerm a d m j ·ᶜ
          realPower h m)
        (suc k)
        N

    rest : ℝᶜ
    rest =
      prefixRemainderRows
        (λ n j →
          recenterCoefficientTerm a d n j ·ᶜ
          realPower h n)
        (suc m)
        k
        (suc N)

    rowMajorTerm : ℕ → ℝᶜ
    rowMajorTerm j =
      recenterCoefficientTerm b (rational (radius δ)) m j ·ᶜ
      realPower (rational (radius τ)) m

    rowMajor : ℝᶜ
    rowMajor =
      tailSum rowMajorTerm (suc k) N

    restMajor : ℝᶜ
    restMajor =
      prefixRemainderRows
        (λ n j →
          recenterCoefficientTerm b (rational (radius δ)) n j ·ᶜ
          realPower (rational (radius τ)) n)
        (suc m)
        k
        (suc N)

    row≤major :
      absᶜ row ≤ᶜ rowMajor
    row≤major =
      tailSum-comparison
        (seriesMajorizedByTerms
          (recenterTerm≤normalizedMajorantTerm
            d-bound
            h-bound
            probe-bound
            majorized
            m)
          (normalizedRecenterTermNonnegative
            {a = a}
            {ρ = ρ}
            {σ = σ}
            {v = v}
            {ν = ν}
            δ
            τ
            majorized
            m))
        (suc k)
        N

    rest≤major :
      absᶜ rest ≤ᶜ restMajor
    rest≤major =
      prefixRemainderRows≤normalizedMajorant
        d-bound
        h-bound
        probe-bound
        majorized
        (suc m)
        k
        (suc N)

  normalizedTriangleAtProbe :
    (δ τ : ℚ⁺) →
    (v : ℕ → ℝᶜ) →
    (N : ℕ) →
    partialSum v N ≡
    triangularRowsSumᶜ
      (λ n k →
        recenterCoefficientTerm
          (normalizedMajorantPowerSeries (δ +⁺ τ) v)
          (rational (radius δ))
          n
          k ·ᶜ
        realPower (rational (radius τ)) n)
      N
  normalizedTriangleAtProbe δ τ v N =
    cong
      (λ u → partialSum u N)
      (funExt λ n → sym (normalizedMajorantProbeTerm ρ v n)) ∙
    powerSeriesPartialSum-cong
      {a = b}
      {b = b}
      {h = rational (radius ρ)}
      {k = rational δR +ᶜ rational τR}
      (λ _ → refl)
      point-path
      N ∙
    powerSeriesPartialSum-recenterTriangle-shifted
      b
      (rational δR)
      (rational τR)
      N
    where
    ρ : ℚ⁺
    ρ =
      δ +⁺ τ

    b : PowerSeries
    b =
      normalizedMajorantPowerSeries ρ v

    δR : ℚ
    δR =
      radius δ

    τR : ℚ
    τR =
      radius τ

    point-path :
      rational (radius ρ) ≡ rational δR +ᶜ rational τR
    point-path =
      sym (add-rational δR τR)

  normalizedShiftedTriangle≤MajorantTail :
    {a : PowerSeries} →
    {σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    (δ τ : ℚ⁺) →
    PowerSeriesMajorizedOnBall a σ v ν →
    (m L : ℕ) →
    normalizedShiftedTriangle (δ +⁺ τ) δ τ v m L ≤ᶜ
    tailSum v m L
  normalizedShiftedTriangle≤MajorantTail
      {a = a}
      {σ = σ}
      {v = v}
      {ν = ν}
      δ
      τ
      majorized
      m
      L =
    addᶜ-reflect≤ᶜ-left
      (partialSum v m)
      prefixShift≤prefixTail
    where
    ρ : ℚ⁺
    ρ =
      δ +⁺ τ

    b : PowerSeries
    b =
      normalizedMajorantPowerSeries ρ v

    u : ℕ → ℕ → ℝᶜ
    u n k =
      recenterCoefficientTerm b (rational (radius δ)) n k ·ᶜ
      realPower (rational (radius τ)) n

    shift : ℝᶜ
    shift =
      normalizedShiftedTriangle ρ δ τ v m L

    triangle≤triangle :
      triangularRowsSumᶜ u m +ᶜ shift ≤ᶜ
      triangularRowsSumᶜ u (m Nat.+ L)
    triangle≤triangle =
      trianglePrefixPlusShift≤Triangle
        u
        (normalizedRecenterTermNonnegative
          {a = a}
          {ρ = ρ}
          {σ = σ}
          {v = v}
          {ν = ν}
          δ
          τ
          majorized)
        m
        L

    triangle≤partial :
      partialSum v m +ᶜ shift ≤ᶜ
      partialSum v (m Nat.+ L)
    triangle≤partial =
      subst2
        _≤ᶜ_
        (cong
          (_+ᶜ shift)
          (sym (normalizedTriangleAtProbe δ τ v m)))
        (sym (normalizedTriangleAtProbe δ τ v (m Nat.+ L)))
        triangle≤triangle

    prefixShift≤prefixTail :
      partialSum v m +ᶜ shift ≤ᶜ
      partialSum v m +ᶜ tailSum v m L
    prefixShift≤prefixTail =
      subst
        (λ x → partialSum v m +ᶜ shift ≤ᶜ x)
        (partialSum-append v m L)
        triangle≤partial

  normalizedPrefixRemainder≤MajorantTail :
    {a : PowerSeries} →
    {σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    (δ τ : ℚ⁺) →
    PowerSeriesMajorizedOnBall a σ v ν →
    (m N : ℕ) →
    prefixRemainderRows
      (λ n j →
        recenterCoefficientTerm
          (normalizedMajorantPowerSeries (δ +⁺ τ) v)
          (rational (radius δ))
          n
          j ·ᶜ
        realPower (rational (radius τ)) n)
      zero
      m
      N
    ≤ᶜ
    tailSum v m (m Nat.+ N)
  normalizedPrefixRemainder≤MajorantTail
      {a = a}
      {σ = σ}
      {v = v}
      {ν = ν}
      δ
      τ
      majorized
      m
      N =
    addᶜ-reflect≤ᶜ-left
      (partialSum v m)
      prefix≤prefixTail
    where
    ρ : ℚ⁺
    ρ =
      δ +⁺ τ

    b : PowerSeries
    b =
      normalizedMajorantPowerSeries ρ v

    u : ℕ → ℕ → ℝᶜ
    u n j =
      recenterCoefficientTerm b (rational (radius δ)) n j ·ᶜ
      realPower (rational (radius τ)) n

    prefix : ℝᶜ
    prefix =
      prefixRemainderRows u zero m N

    rectangle : ℝᶜ
    rectangle =
      recenterOuterTailApprox
        b
        (rational (radius δ))
        (rational (radius τ))
        zero
        m
        (m Nat.+ N)

    target : ℝᶜ
    target =
      normalizedShiftedTriangle ρ δ τ v zero (m Nat.+ (m Nat.+ N))

    rectangle-path :
      rectangle ≡ shiftedRowsTriangle u zero m +ᶜ prefix
    rectangle-path =
      recenterOuterTailApprox-prefixRemainder
        b
        (rational (radius δ))
        (rational (radius τ))
        zero
        m
        N

    rectangle≤target :
      rectangle ≤ᶜ target
    rectangle≤target =
      normalizedRectangle≤shiftedTriangle
        {a = a}
        {ρ = ρ}
        {σ = σ}
        {v = v}
        {ν = ν}
        δ
        τ
        majorized
        zero
        m
        (m Nat.+ N)

    trianglePrefix≤triangle :
      shiftedRowsTriangle u zero m +ᶜ prefix ≤ᶜ
      shiftedRowsTriangle u zero (m Nat.+ (m Nat.+ N))
    trianglePrefix≤triangle =
      subst2
        _≤ᶜ_
        rectangle-path
        refl
        rectangle≤target

    partialPrefix≤partial :
      partialSum v m +ᶜ prefix ≤ᶜ
      partialSum v (m Nat.+ (m Nat.+ N))
    partialPrefix≤partial =
      subst2
        _≤ᶜ_
        (cong
          (_+ᶜ prefix)
          (shiftedRowsTriangle-zero-path u m ∙
           sym (normalizedTriangleAtProbe δ τ v m)))
        (shiftedRowsTriangle-zero-path
          u
          (m Nat.+ (m Nat.+ N)) ∙
         sym
          (normalizedTriangleAtProbe
            δ
            τ
            v
            (m Nat.+ (m Nat.+ N))))
        trianglePrefix≤triangle

    prefix≤prefixTail :
      partialSum v m +ᶜ prefix ≤ᶜ
      partialSum v m +ᶜ tailSum v m (m Nat.+ N)
    prefix≤prefixTail =
      subst
        (λ x → partialSum v m +ᶜ prefix ≤ᶜ x)
        (partialSum-append v m (m Nat.+ N))
        partialPrefix≤partial


recenterOuterTailApproxBoundFromMajorizedOnStrictSubball :
  {a : PowerSeries} →
  {δ τ σ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {ν : ℚ⁺ → ℕ} →
  {d h : ℝᶜ} →
  BoundedByᶜ δ d →
  BoundedByᶜ τ h →
  BoundedByᶜ σ (rational (radius (δ +⁺ τ))) →
  PowerSeriesMajorizedOnBall a σ v ν →
  (ε : ℚ⁺) →
  (m k N : ℕ) →
  NatOrder._≤_ (ν ε) m →
  BoundedByᶜ ε (recenterOuterTailApprox a d h m k N)
recenterOuterTailApproxBoundFromMajorizedOnStrictSubball
    {a = a}
    {δ = δ}
    {τ = τ}
    {σ = σ}
    {v = v}
    {ν = ν}
    {d = d}
    {h = h}
    d-bound
    h-bound
    probe-bound
    majorized
    ε
    m
    k
    N
    ν≤m =
  abs≤bounded-byᶜ absApprox≤ε
  where
  ρ : ℚ⁺
  ρ =
    δ +⁺ τ

  b : PowerSeries
  b =
    normalizedMajorantPowerSeries ρ v

  normalizedApprox : ℝᶜ
  normalizedApprox =
    recenterOuterTailApprox
      b
      (rational (radius δ))
      (rational (radius τ))
      m
      k
      N

  L : ℕ
  L =
    k Nat.+ N

  absApprox≤normalized :
    absᶜ (recenterOuterTailApprox a d h m k N) ≤ᶜ
    normalizedApprox
  absApprox≤normalized =
    recenterOuterTailApprox≤normalizedMajorantApprox
      d-bound
      h-bound
      probe-bound
      majorized
      m
      k
      N

  normalized≤shift :
    normalizedApprox ≤ᶜ
    normalizedShiftedTriangle ρ δ τ v m L
  normalized≤shift =
    normalizedRectangle≤shiftedTriangle
      {a = a}
      {ρ = ρ}
      {σ = σ}
      {v = v}
      {ν = ν}
      δ
      τ
      majorized
      m
      k
      N

  shift≤tail :
    normalizedShiftedTriangle ρ δ τ v m L ≤ᶜ
    tailSum v m L
  shift≤tail =
    normalizedShiftedTriangle≤MajorantTail
      {a = a}
      {σ = σ}
      {v = v}
      {ν = ν}
      δ
      τ
      majorized
      m
      L

  tail-bound : BoundedByᶜ ε (tailSum v m L)
  tail-bound =
    PowerSeriesMajorizedOnBall.majorTail
      {a = a}
      {ρ = σ}
      {v = v}
      {μ = ν}
      majorized
      ε
      m
      L
      ν≤m

  absApprox≤ε :
    absᶜ (recenterOuterTailApprox a d h m k N) ≤ᶜ
    rational (radius ε)
  absApprox≤ε =
    ≤ᶜ-trans
      {x = absᶜ (recenterOuterTailApprox a d h m k N)}
      {y = normalizedApprox}
      {z = rational (radius ε)}
      absApprox≤normalized
      (≤ᶜ-trans
        {x = normalizedApprox}
        {y = normalizedShiftedTriangle ρ δ τ v m L}
        {z = rational (radius ε)}
        normalized≤shift
        (≤ᶜ-trans
          {x = normalizedShiftedTriangle ρ δ τ v m L}
          {y = tailSum v m L}
          {z = rational (radius ε)}
          shift≤tail
          (upperᶜ tail-bound)))


recenterPrefixTriangleDifferenceBoundFromMajorizedOnStrictSubball :
  {a : PowerSeries} →
  {δ τ σ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {ν : ℚ⁺ → ℕ} →
  {d h : ℝᶜ} →
  BoundedByᶜ δ d →
  BoundedByᶜ τ h →
  BoundedByᶜ σ (rational (radius (δ +⁺ τ))) →
  PowerSeriesMajorizedOnBall a σ v ν →
  (ε : ℚ⁺) →
  (m N : ℕ) →
  NatOrder._≤_ (ν ε) m →
  BoundedByᶜ ε
    (recenterOuterTailApprox a d h zero m (m Nat.+ N) +ᶜ
     (-ᶜ
      triangularRowsSumᶜ
        (λ n k →
          recenterCoefficientTerm a d n k ·ᶜ
          realPower h n)
        m))
recenterPrefixTriangleDifferenceBoundFromMajorizedOnStrictSubball
    {a = a}
    {δ = δ}
    {τ = τ}
    {σ = σ}
    {v = v}
    {ν = ν}
    {d = d}
    {h = h}
    d-bound
    h-bound
    probe-bound
    majorized
    ε
    m
    N
    ν≤m =
  subst
    (BoundedByᶜ ε)
    (sym diff-path)
    (abs≤bounded-byᶜ absPrefix≤ε)
  where
  ρ : ℚ⁺
  ρ =
    δ +⁺ τ

  b : PowerSeries
  b =
    normalizedMajorantPowerSeries ρ v

  u : ℕ → ℕ → ℝᶜ
  u n k =
    recenterCoefficientTerm a d n k ·ᶜ
    realPower h n

  uMajor : ℕ → ℕ → ℝᶜ
  uMajor n k =
    recenterCoefficientTerm b (rational (radius δ)) n k ·ᶜ
    realPower (rational (radius τ)) n

  triangle : ℝᶜ
  triangle =
    triangularRowsSumᶜ u m

  prefix : ℝᶜ
  prefix =
    prefixRemainderRows u zero m N

  prefixMajor : ℝᶜ
  prefixMajor =
    prefixRemainderRows uMajor zero m N

  rectangle-path :
    recenterOuterTailApprox a d h zero m (m Nat.+ N) ≡
    shiftedRowsTriangle u zero m +ᶜ prefix
  rectangle-path =
    recenterOuterTailApprox-prefixRemainder
      a
      d
      h
      zero
      m
      N

  triangle-path :
    shiftedRowsTriangle u zero m ≡ triangle
  triangle-path =
    shiftedRowsTriangle-zero-path u m

  diff-path :
    recenterOuterTailApprox a d h zero m (m Nat.+ N) +ᶜ
    (-ᶜ triangle)
    ≡
    prefix
  diff-path =
    cong
      (_+ᶜ (-ᶜ triangle))
      rectangle-path ∙
    cong
      (λ x → (x +ᶜ prefix) +ᶜ (-ᶜ triangle))
      triangle-path ∙
    cong
      (_+ᶜ (-ᶜ triangle))
      (add-comm triangle prefix) ∙
    plus-minus-cancel-right prefix triangle

  absPrefix≤major :
    absᶜ prefix ≤ᶜ prefixMajor
  absPrefix≤major =
    prefixRemainderRows≤normalizedMajorant
      d-bound
      h-bound
      probe-bound
      majorized
      zero
      m
      N

  major≤tail :
    prefixMajor ≤ᶜ tailSum v m (m Nat.+ N)
  major≤tail =
    normalizedPrefixRemainder≤MajorantTail
      {a = a}
      {σ = σ}
      {v = v}
      {ν = ν}
      δ
      τ
      majorized
      m
      N

  tail-bound : BoundedByᶜ ε (tailSum v m (m Nat.+ N))
  tail-bound =
    PowerSeriesMajorizedOnBall.majorTail
      {a = a}
      {ρ = σ}
      {v = v}
      {μ = ν}
      majorized
      ε
      m
      (m Nat.+ N)
      ν≤m

  absPrefix≤ε :
    absᶜ prefix ≤ᶜ rational (radius ε)
  absPrefix≤ε =
    ≤ᶜ-trans
      {x = absᶜ prefix}
      {y = prefixMajor}
      {z = rational (radius ε)}
      absPrefix≤major
      (≤ᶜ-trans
        {x = prefixMajor}
        {y = tailSum v m (m Nat.+ N)}
        {z = rational (radius ε)}
        major≤tail
        (upperᶜ tail-bound))


recenterPrefixTriangleDifferenceBoundFromMajorizedOnStrictSubballLimit :
  {a : PowerSeries} →
  {δ τ σ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {ν : ℚ⁺ → ℕ} →
  {d h : ℝᶜ} →
  (recenterData : RecenterPowerSeriesData a d) →
  BoundedByᶜ δ d →
  BoundedByᶜ τ h →
  BoundedByᶜ σ (rational (radius (δ +⁺ τ))) →
  PowerSeriesMajorizedOnBall a σ v ν →
  (ε : ℚ⁺) →
  (m : ℕ) →
  NatOrder._≤_ (ν ε) m →
  BoundedByᶜ ε
    (powerSeriesPartialSum
      (recenterPowerSeriesWith a d recenterData)
      h
      m
     +ᶜ
     (-ᶜ
      triangularRowsSumᶜ
        (λ n k →
          recenterCoefficientTerm a d n k ·ᶜ
          realPower h n)
        m))
recenterPrefixTriangleDifferenceBoundFromMajorizedOnStrictSubballLimit
    {a = a}
    {δ = δ}
    {τ = τ}
    {σ = σ}
    {v = v}
    {ν = ν}
    {d = d}
    {h = h}
    recenterData
    d-bound
    h-bound
    probe-bound
    majorized
    ε
    m
    ν≤m =
  boundedByClosedFromConvergentApproximants
    ε
    difference-converges
    (λ N →
      recenterPrefixTriangleDifferenceBoundFromMajorizedOnStrictSubball
        d-bound
        h-bound
        probe-bound
        majorized
        ε
        m
        N
        ν≤m)
  where
  terms : ℕ → ℝᶜ
  terms =
    powerSeriesTerm (recenterPowerSeriesWith a d recenterData) h

  triangle : ℝᶜ
  triangle =
    triangularRowsSumᶜ
      (λ n k →
        recenterCoefficientTerm a d n k ·ᶜ
        realPower h n)
      m

  shifted-outer-converges :
    ConvergesTo
      (λ N → recenterOuterTailApprox a d h zero m (m Nat.+ N))
      (tailSum terms zero m)
  shifted-outer-converges =
    fst (recenterOuterTailApproxConvergesToTail recenterData h-bound zero m) ,
    shiftConvergesWithModulus
      m
      (snd (recenterOuterTailApproxConvergesToTail recenterData h-bound zero m))

  difference-converges :
    ConvergesTo
      (λ N →
        recenterOuterTailApprox a d h zero m (m Nat.+ N) +ᶜ
        (-ᶜ triangle))
      (powerSeriesPartialSum
        (recenterPowerSeriesWith a d recenterData)
        h
        m
       +ᶜ
       (-ᶜ triangle))
  difference-converges =
    addConvergesTo
      shifted-outer-converges
      (negConvergesTo (constantConvergesTo triangle))
