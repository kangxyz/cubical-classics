{-

Coefficient convergence for strict-subball re-centering.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Recenter.CoefficientConvergence where

open import Cubical.Foundations.Prelude

import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Modulus using (AntitoneNatModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
  using (0ᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
  using (_·ᶜ_ ; mulᶜ-assoc ; mulᶜ-rational-left)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (scalarMulᶜ-nonnegative ; scalarMulᶜ-pres≤ᶜ-scalar)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
  using (scalarMulᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_ ; ≤ᶜ-trans)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using (absᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
  using (≤ℚ→rational≤ᶜ)
open import Constructive.Analysis.Reals.Series
  using
    ( SeriesMajorizedBy
    ; TailBound
    ; drop
    ; drop-index
    ; seriesMajorizedByTerms
    ; tailBound-drop
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Majorant
  using (bounded-byᶜ-abs)
open import Constructive.Analysis.GeometricDecay
  using (positivePower)
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower ; realPowerBoundsFromBound)
open import Constructive.Analysis.Reals.PowerSeries.Algebra.Pointwise
  using
    ( rationalScaleModulus
    ; rationalScaleModulus-antitone
    ; rationalScaleTailBound
    )
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Bounds
  using
    ( positiveRationalSelfBounded
    ; powerSeriesCoefficientFromRationalProbe
    )
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.Estimates
  using
    ( absᶜ-mul≤product
    ; absᶜ-rational-nonnegative
    ; absᶜ-scalarMul≤
    ; derivativeStrictSubballRatio
    ; derivativeStrictSubballRatio<1
    ; mulᶜ-nonnegative
    ; tripleScalarProductPath
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using (PowerSeriesMajorizedOnBall)
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Base
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Binomial
  using (binomialᶜ ; binomialᶜ-natural ; binomialℕ)
open import Constructive.Analysis.Reals.PowerSeries.Recenter.BinomialGeometric
  using (binomialGeometricBoundScale ; binomialGeometricBoundScale≥1)
open import Constructive.Analysis.Reals.PowerSeries.Recenter.CoefficientBounds
  using
    ( recenterCoefficientScale
    ; recenterCoefficientWeight≤Scale
    )
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Majorant
open import Constructive.Data.PositiveRationals
  using (ℚ⁺ ; radius ; posInv⁺)
import Constructive.Data.Rationals as Rational


private
  coefficientProbeBound :
    {a : PowerSeries} →
    {σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    PowerSeriesMajorizedOnBall a σ v ν →
    (m : ℕ) →
    absᶜ (a m) ≤ᶜ
    scalarMulᶜ
      (radius (posInv⁺ (positivePower σ m)))
      (v m)
  coefficientProbeBound {a = a} {σ = σ} {v = v} {ν = ν}
      majorized m =
    subst
      (λ x →
        absᶜ x ≤ᶜ
        scalarMulᶜ
          (radius (posInv⁺ (positivePower σ m)))
          (v m))
      (powerSeriesCoefficientFromRationalProbe σ a m)
      (absᶜ-scalarMul≤
        invσm
        invσm-nonnegative
        v-nonnegative
        probe≤v)
    where
    invσm : ℚ
    invσm =
      radius (posInv⁺ (positivePower σ m))

    invσm-nonnegative : Rational.0ℚ ℚOrder.≤ invσm
    invσm-nonnegative =
      Rational.<→≤
        {p = Rational.0ℚ}
        {q = invσm}
        (posInv⁺ (positivePower σ m) .snd)

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
      absᶜ (powerSeriesTerm a (rational (radius σ)) m) ≤ᶜ v m
    probe≤v =
      SeriesMajorizedBy.termMajorized
        (PowerSeriesMajorizedOnBall.termMajorized
          {a = a}
          {ρ = σ}
          {v = v}
          {μ = ν}
          majorized
          (rational (radius σ))
          (positiveRationalSelfBounded σ))
        zero
        m

  recenterCoefficientMajorant :
    {v : ℕ → ℝᶜ} →
    (δ σ : ℚ⁺) →
    radius δ ℚOrder.< radius σ →
    ℕ →
    ℕ →
    ℝᶜ
  recenterCoefficientMajorant {v = v} δ σ δ<σ n k =
    scalarMulᶜ
      (radius (recenterCoefficientScale δ σ δ<σ n))
      (v (n Nat.+ k))

  recenterCoefficientMajorantNonnegative :
    {a : PowerSeries} →
    {δ σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    (δ<σ : radius δ ℚOrder.< radius σ) →
    PowerSeriesMajorizedOnBall a σ v ν →
    (n k : ℕ) →
    0ᶜ ≤ᶜ recenterCoefficientMajorant {v = v} δ σ δ<σ n k
  recenterCoefficientMajorantNonnegative
      {a = a}
      {δ = δ}
      {σ = σ}
      {v = v}
      {ν = ν}
      δ<σ
      majorized
      n
      k =
    scalarMulᶜ-nonnegative
      scale
      scale-nonnegative
      {x = v (n Nat.+ k)}
      (PowerSeriesMajorizedOnBall.majorantNonnegative
        {a = a}
        {ρ = σ}
        {v = v}
        {μ = ν}
        majorized
        (n Nat.+ k))
    where
    scale : ℚ
    scale =
      radius (recenterCoefficientScale δ σ δ<σ n)

    scale-nonnegative : Rational.0ℚ ℚOrder.≤ scale
    scale-nonnegative =
      Rational.<→≤
        {p = Rational.0ℚ}
        {q = scale}
        (recenterCoefficientScale δ σ δ<σ n .snd)

  coefficientTerm-zero≤majorant :
    {a : PowerSeries} →
    {δ σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    (δ<σ : radius δ ℚOrder.< radius σ) →
    PowerSeriesMajorizedOnBall a σ v ν →
    (n : ℕ) →
    absᶜ (a n) ≤ᶜ
    recenterCoefficientMajorant {v = v} δ σ δ<σ n zero
  coefficientTerm-zero≤majorant
      {a = a}
      {δ = δ}
      {σ = σ}
      {v = v}
      {ν = ν}
      δ<σ
      majorized
      n =
    ≤ᶜ-trans
      {x = absᶜ (a n)}
      {y = scalarMulᶜ invσn (v n)}
      {z = recenterCoefficientMajorant {v = v} δ σ δ<σ n zero}
      (coefficientProbeBound
        {a = a}
        {σ = σ}
        {v = v}
        {ν = ν}
        majorized
        n)
      scaledCoefficient≤majorant
    where
    invσn : ℚ
    invσn =
      radius (posInv⁺ (positivePower σ n))

    scale : ℚ
    scale =
      radius (recenterCoefficientScale δ σ δ<σ n)

    C : ℚ
    C =
      radius
        (binomialGeometricBoundScale
          (derivativeStrictSubballRatio δ σ)
          (derivativeStrictSubballRatio<1 {ρ = δ} {σ = σ} δ<σ)
          n)

    invσn-nonnegative : Rational.0ℚ ℚOrder.≤ invσn
    invσn-nonnegative =
      Rational.<→≤
        {p = Rational.0ℚ}
        {q = invσn}
        (posInv⁺ (positivePower σ n) .snd)

    C≥1 : Rational.1ℚ ℚOrder.≤ C
    C≥1 =
      binomialGeometricBoundScale≥1
        (derivativeStrictSubballRatio δ σ)
        (derivativeStrictSubballRatio<1 {ρ = δ} {σ = σ} δ<σ)
        n

    invTimesOne≤scale :
      invσn ℚ.· Rational.1ℚ ℚOrder.≤ scale
    invTimesOne≤scale =
      Rational.mul-left-nonnegative-≤
        {a = invσn}
        {b = Rational.1ℚ}
        {c = C}
        invσn-nonnegative
        C≥1

    invσn≤scale : invσn ℚOrder.≤ scale
    invσn≤scale =
      subst
        (λ x → x ℚOrder.≤ scale)
        (ℚ.·IdR invσn)
        invTimesOne≤scale

    scaledCoefficient≤majorant :
      scalarMulᶜ invσn (v n) ≤ᶜ
      recenterCoefficientMajorant {v = v} δ σ δ<σ n zero
    scaledCoefficient≤majorant =
      subst
        (λ x → scalarMulᶜ invσn (v n) ≤ᶜ x)
        (sym
          (cong
            (λ m → scalarMulᶜ scale (v m))
            (Nat.+-zero n)))
        (scalarMulᶜ-pres≤ᶜ-scalar
          {a = invσn}
          {b = scale}
          invσn≤scale
          {x = v n}
          (PowerSeriesMajorizedOnBall.majorantNonnegative
            {a = a}
            {ρ = σ}
            {v = v}
            {μ = ν}
            majorized
            n))

  coefficientTerm-suc≤majorant :
    {a : PowerSeries} →
    {δ σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    (d : ℝᶜ) →
    BoundedByᶜ δ d →
    (δ<σ : radius δ ℚOrder.< radius σ) →
    PowerSeriesMajorizedOnBall a σ v ν →
    (n k : ℕ) →
    absᶜ (recenterCoefficientTerm a d n (suc k)) ≤ᶜ
    recenterCoefficientMajorant {v = v} δ σ δ<σ n (suc k)
  coefficientTerm-suc≤majorant
      {a = a}
      {δ = δ}
      {σ = σ}
      {v = v}
      {ν = ν}
      d
      d-bound
      δ<σ
      majorized
      n
      k =
    ≤ᶜ-trans
      {x = absᶜ (recenterCoefficientTerm a d n (suc k))}
      {y = scalarMulᶜ coeff (v m)}
      {z = scalarMulᶜ scale (v m)}
      term≤coefficientScale
      (scalarMulᶜ-pres≤ᶜ-scalar
        {a = coeff}
        {b = scale}
        coeff≤scale
        {x = v m}
        v-nonnegative)
    where
    m : ℕ
    m =
      n Nat.+ suc k

    B : ℚ
    B =
      Rational.natMul (binomialℕ m n) Rational.1ℚ

    invσm : ℚ
    invσm =
      radius (posInv⁺ (positivePower σ m))

    δpow : ℚ
    δpow =
      radius (positivePower δ (suc k))

    coeff : ℚ
    coeff =
      (B ℚ.· invσm) ℚ.· δpow

    scale : ℚ
    scale =
      radius (recenterCoefficientScale δ σ δ<σ n)

    binomial-nonnegative : Rational.0ℚ ℚOrder.≤ B
    binomial-nonnegative =
      Rational.natMul-nonnegative (binomialℕ m n) Rational.0<1

    invσm-nonnegative : Rational.0ℚ ℚOrder.≤ invσm
    invσm-nonnegative =
      Rational.<→≤
        {p = Rational.0ℚ}
        {q = invσm}
        (posInv⁺ (positivePower σ m) .snd)

    δpow-nonnegative : Rational.0ℚ ℚOrder.≤ δpow
    δpow-nonnegative =
      Rational.<→≤
        {p = Rational.0ℚ}
        {q = δpow}
        (positivePower δ (suc k) .snd)

    v-nonnegative : 0ᶜ ≤ᶜ v m
    v-nonnegative =
      PowerSeriesMajorizedOnBall.majorantNonnegative
        {a = a}
        {ρ = σ}
        {v = v}
        {μ = ν}
        majorized
        m

    coefficient-majorant-nonnegative :
      0ᶜ ≤ᶜ scalarMulᶜ invσm (v m)
    coefficient-majorant-nonnegative =
      scalarMulᶜ-nonnegative
        invσm
        invσm-nonnegative
        {x = v m}
        v-nonnegative

    d-power-majorant-nonnegative :
      0ᶜ ≤ᶜ rational δpow
    d-power-majorant-nonnegative =
      ≤ℚ→rational≤ᶜ
        {q = Rational.0ℚ}
        {r = δpow}
        δpow-nonnegative

    coefficient-times-power-nonnegative :
      0ᶜ ≤ᶜ scalarMulᶜ invσm (v m) ·ᶜ rational δpow
    coefficient-times-power-nonnegative =
      mulᶜ-nonnegative
        (scalarMulᶜ invσm (v m))
        (rational δpow)
        coefficient-majorant-nonnegative
        d-power-majorant-nonnegative

    binomial≤majorant :
      absᶜ (binomialᶜ m n) ≤ᶜ rational B
    binomial≤majorant =
      subst
        (λ x → absᶜ x ≤ᶜ rational B)
        (sym (binomialᶜ-natural m n))
        (absᶜ-rational-nonnegative B binomial-nonnegative)

    coefficient≤majorant :
      absᶜ (a m) ≤ᶜ scalarMulᶜ invσm (v m)
    coefficient≤majorant =
      coefficientProbeBound
        {a = a}
        {σ = σ}
        {v = v}
        {ν = ν}
        majorized
        m

    d-power≤majorant :
      absᶜ (realPower d (suc k)) ≤ᶜ rational δpow
    d-power≤majorant =
      bounded-byᶜ-abs
        (realPowerBoundsFromBound δ d d-bound (suc k))

    coefficient-power≤majorant :
      absᶜ (a m ·ᶜ realPower d (suc k)) ≤ᶜ
      scalarMulᶜ invσm (v m) ·ᶜ rational δpow
    coefficient-power≤majorant =
      absᶜ-mul≤product
        (a m)
        (realPower d (suc k))
        (scalarMulᶜ invσm (v m))
        (rational δpow)
        coefficient-majorant-nonnegative
        d-power-majorant-nonnegative
        coefficient≤majorant
        d-power≤majorant

    factored≤majorant :
      absᶜ (binomialᶜ m n ·ᶜ (a m ·ᶜ realPower d (suc k))) ≤ᶜ
      rational B ·ᶜ (scalarMulᶜ invσm (v m) ·ᶜ rational δpow)
    factored≤majorant =
      absᶜ-mul≤product
        (binomialᶜ m n)
        (a m ·ᶜ realPower d (suc k))
        (rational B)
        (scalarMulᶜ invσm (v m) ·ᶜ rational δpow)
        (≤ℚ→rational≤ᶜ
          {q = Rational.0ℚ}
          {r = B}
          binomial-nonnegative)
        coefficient-times-power-nonnegative
        binomial≤majorant
        coefficient-power≤majorant

    term≤product :
      absᶜ (recenterCoefficientTerm a d n (suc k)) ≤ᶜ
      rational B ·ᶜ (scalarMulᶜ invσm (v m) ·ᶜ rational δpow)
    term≤product =
      subst
        (λ x →
          absᶜ x ≤ᶜ
          rational B ·ᶜ
            (scalarMulᶜ invσm (v m) ·ᶜ rational δpow))
        (mulᶜ-assoc
          (binomialᶜ m n)
          (a m)
          (realPower d (suc k)))
        factored≤majorant

    term≤coefficientScale :
      absᶜ (recenterCoefficientTerm a d n (suc k)) ≤ᶜ
      scalarMulᶜ coeff (v m)
    term≤coefficientScale =
      subst
        (λ x →
          absᶜ (recenterCoefficientTerm a d n (suc k)) ≤ᶜ x)
        (tripleScalarProductPath B invσm δpow (v m))
        term≤product

    coeff≤scale : coeff ℚOrder.≤ scale
    coeff≤scale =
      recenterCoefficientWeight≤Scale δ σ δ<σ n (suc k)

  coefficientTerm≤majorant :
    {a : PowerSeries} →
    {δ σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    (d : ℝᶜ) →
    BoundedByᶜ δ d →
    (δ<σ : radius δ ℚOrder.< radius σ) →
    PowerSeriesMajorizedOnBall a σ v ν →
    (n k : ℕ) →
    absᶜ (recenterCoefficientTerm a d n k) ≤ᶜ
    recenterCoefficientMajorant {v = v} δ σ δ<σ n k
  coefficientTerm≤majorant d d-bound δ<σ majorized n zero =
    coefficientTerm-zero≤majorant δ<σ majorized n
  coefficientTerm≤majorant d d-bound δ<σ majorized n (suc k) =
    coefficientTerm-suc≤majorant d d-bound δ<σ majorized n k

  strictSubballCoefficientMajorTail :
    {a : PowerSeries} →
    {δ σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    (δ<σ : radius δ ℚOrder.< radius σ) →
    PowerSeriesMajorizedOnBall a σ v ν →
    (n : ℕ) →
    TailBound
      (recenterCoefficientMajorant {v = v} δ σ δ<σ n)
      (rationalScaleModulus
        (radius (recenterCoefficientScale δ σ δ<σ n))
        ν)
  strictSubballCoefficientMajorTail {a = a} {δ = δ} {σ = σ} {v = v} {ν = ν}
      δ<σ majorized n =
    subst
      (λ u →
        TailBound
          u
          (rationalScaleModulus
            (radius (recenterCoefficientScale δ σ δ<σ n))
            ν))
      scaled-majorant-path
      scaled-drop-tail
    where
    scale : ℚ
    scale =
      radius (recenterCoefficientScale δ σ δ<σ n)

    scaled-drop-tail :
      TailBound
        (λ k → rational scale ·ᶜ drop n v k)
        (rationalScaleModulus scale ν)
    scaled-drop-tail =
      rationalScaleTailBound
        scale
        {u = drop n v}
        {μ = ν}
        (tailBound-drop
          {u = v}
          {μ = ν}
          (PowerSeriesMajorizedOnBall.majorTail
            {a = a}
            {ρ = σ}
            {v = v}
            {μ = ν}
            majorized)
          n)

    scaled-majorant-path :
      (λ k → rational scale ·ᶜ drop n v k) ≡
      recenterCoefficientMajorant {v = v} δ σ δ<σ n
    scaled-majorant-path =
      funExt
        (λ k →
          cong
            (rational scale ·ᶜ_)
            (drop-index n v k) ∙
          mulᶜ-rational-left
            scale
            (v (n Nat.+ k)))

  strictSubballCoefficientMajorAntitone :
    {a : PowerSeries} →
    {δ σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    (δ<σ : radius δ ℚOrder.< radius σ) →
    PowerSeriesMajorizedOnBall a σ v ν →
    (n : ℕ) →
    AntitoneNatModulus
      (rationalScaleModulus
        (radius (recenterCoefficientScale δ σ δ<σ n))
        ν)
  strictSubballCoefficientMajorAntitone {a = a} {δ = δ} {σ = σ} {v = v} {ν = ν}
      δ<σ majorized n =
    rationalScaleModulus-antitone
      (radius (recenterCoefficientScale δ σ δ<σ n))
      (PowerSeriesMajorizedOnBall.majorAntitone
        {a = a}
        {ρ = σ}
        {v = v}
        {μ = ν}
        majorized)


recenterCoefficientMajorantDataFromMajorizedOnStrictSubball :
  {a : PowerSeries} →
  {δ σ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {ν : ℚ⁺ → ℕ} →
  (d : ℝᶜ) →
  BoundedByᶜ δ d →
  radius δ ℚOrder.< radius σ →
  PowerSeriesMajorizedOnBall a σ v ν →
  (n : ℕ) →
  RecenterCoefficientMajorantData a d n
recenterCoefficientMajorantDataFromMajorizedOnStrictSubball
  {δ = δ}
  {σ = σ}
  {v = v}
  {ν = ν}
  d
  d-bound
  δ<σ
  majorized
  n =
  recenterCoefficientMajorant {v = v} δ σ δ<σ n ,
  rationalScaleModulus
    (radius (recenterCoefficientScale δ σ δ<σ n))
    ν ,
  seriesMajorizedByTerms
    (coefficientTerm≤majorant d d-bound δ<σ majorized n)
    (recenterCoefficientMajorantNonnegative δ<σ majorized n) ,
  strictSubballCoefficientMajorTail δ<σ majorized n ,
  strictSubballCoefficientMajorAntitone δ<σ majorized n


recenterPowerSeriesDataFromMajorizedOnStrictSubballδ<σ :
  {a : PowerSeries} →
  {δ σ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {ν : ℚ⁺ → ℕ} →
  (d : ℝᶜ) →
  BoundedByᶜ δ d →
  radius δ ℚOrder.< radius σ →
  PowerSeriesMajorizedOnBall a σ v ν →
  RecenterPowerSeriesData a d
recenterPowerSeriesDataFromMajorizedOnStrictSubballδ<σ
    {a = a}
    {δ = δ}
    {σ = σ}
    {v = v}
    {ν = ν}
    d
    d-bound
    δ<σ
    majorized =
  recenterPowerSeriesDataFromCoefficientMajorants
    (recenterCoefficientMajorantDataFromMajorizedOnStrictSubball
      {a = a}
      {δ = δ}
      {σ = σ}
      {v = v}
      {ν = ν}
      d
      d-bound
      δ<σ
      majorized)
