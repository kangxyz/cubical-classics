{-

Convergence transport for formal derivative coefficients

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Differentiation.StrictSubball where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Modulus using (AntitoneNatModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
  using (0ᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
  using
    ( _·ᶜ_
    ; mulᶜ-comm
    ; mulᶜ-zero-left
    ; mulᶜ-rational-left
    ; mulᶜ-rational-left-assoc
    ; mulᶜ-rational-rational
    ; mulᶜ-rational-right
    ; mulᶜ-rational-right-assoc
    ; mulᶜ-comm-rational-right
    )
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
  using (-ᶜ_ ; neg-rational)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarOrder
  using (scalarMulᶜ-pres≤ᶜ-nonnegative)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using
    ( bounded-byᶜ-mul
    ; mulᶜ-pres≤ᶜ-right
    ; mulᶜ≤abs-product
    ; neg-mulᶜ≤abs-product
    ; scalarMulᶜ-nonnegative
    )
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
  using
    ( scalarMulᶜ
    ; scalarMulᶜ-assoc
    ; scalarMulᶜ-neg-real
    ; scalarMulᶜ-one
    )
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_ ; ≤ᶜ-refl ; ≤ᶜ-trans)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  using
    ( BoundedByᶜ
    ; rational-bound→boundedᶜ
    ; rational-closed-boundᶜ
    ; rational-closed-bound→boundedᶜ
    ; scalar-bound-rational-boundᶜ
    )
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using
    ( absᶜ
    ; absᶜ-least
    ; absᶜ-nonnegative
    ; ≤ᶜabsᶜ-left
    ; ≤ᶜabsᶜ-right
    )
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
  using (≤ℚ→rational≤ᶜ)
open import Constructive.Analysis.Reals.Series
  using
    ( SeriesMajorizedBy
    ; TailBound
    ; shift
    ; tailBound-shift
    )
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
  using
    ( positiveGeometricGap
    ; positiveGeometricPower-linear-bound
    ; positivePower
    ; positivePower-radius
    ; positiveRationalPower-nonnegative
    )
open import Constructive.Analysis.GeometricDecay.Rational
  using (rationalPower)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Power
  using (realPower ; realPowerBoundsFromBound)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
open import Constructive.Analysis.Reals.PowerSeries.Bounds
  using
    ( positiveRationalSelfBounded
    ; powerSeriesCoefficientFromRationalProbe
    )
open import Constructive.Analysis.Reals.PowerSeries.FormalDerivative
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using
    ( PowerSeriesMajorizedOnBall
    ; majorizedOnBall→hasPowerSeriesOnBallWith
    ; powerSeriesMajorizedOnBallFromTermBounds
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.Bounds
  using
    ( derivativeStrictSubballCoefficient≤Scale
    ; derivativeStrictSubballModulus
    ; derivativeStrictSubballScale
    )


derivativePowerSeriesStrictSubballMajorant :
  {ρ σ : ℚ⁺} →
  radius ρ ℚOrder.< radius σ →
  (ℕ → ℝᶜ) →
  ℕ →
  ℝᶜ
derivativePowerSeriesStrictSubballMajorant
  {ρ = ρ}
  {σ = σ}
  ρ<σ
  v
  n =
  scalarMulᶜ
    (radius (derivativeStrictSubballScale ρ σ ρ<σ))
    (v (suc n))


private
  derivativeStrictSubballMajorant :
    {ρ σ : ℚ⁺} →
    radius ρ ℚOrder.< radius σ →
    (ℕ → ℝᶜ) →
    ℕ →
    ℝᶜ
  derivativeStrictSubballMajorant {ρ = ρ} {σ = σ} ρ<σ v n =
    derivativePowerSeriesStrictSubballMajorant
      {ρ = ρ}
      {σ = σ}
      ρ<σ
      v
      n

  derivativeStrictSubballMajorantNonnegative :
    {a : PowerSeries} →
    {ρ σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    (ρ<σ : radius ρ ℚOrder.< radius σ) →
    PowerSeriesMajorizedOnBall a σ v ν →
    (n : ℕ) →
    0ᶜ ≤ᶜ
      derivativeStrictSubballMajorant {ρ = ρ} {σ = σ} ρ<σ v n
  derivativeStrictSubballMajorantNonnegative
      {a = a}
      {ρ = ρ}
      {σ = σ}
      {v = v}
      {ν = ν}
      ρ<σ
      majorized
      n =
    PowerSeriesMajorizedOnBall.shiftedPositiveScalarScaleMajorantNonnegative
      {a = a}
      {ρ = σ}
      {v = v}
      {μ = ν}
      (radius (derivativeStrictSubballScale ρ σ ρ<σ))
      (derivativeStrictSubballScale ρ σ ρ<σ .snd)
      majorized
      n

  derivativeStrictSubballMajorTail :
    {a : PowerSeries} →
    {ρ σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    (ρ<σ : radius ρ ℚOrder.< radius σ) →
    PowerSeriesMajorizedOnBall a σ v ν →
    TailBound
      (derivativeStrictSubballMajorant {ρ = ρ} {σ = σ} ρ<σ v)
      (derivativeStrictSubballModulus {ρ = ρ} {σ = σ} ρ<σ ν)
  derivativeStrictSubballMajorTail
      {a = a}
      {ρ = ρ}
      {σ = σ}
      {v = v}
      {ν = ν}
      ρ<σ
      majorized =
    subst
      (λ u →
        TailBound
          u
          (derivativeStrictSubballModulus {ρ = ρ} {σ = σ} ρ<σ ν))
      scaled-majorant-path
      scaled-shift-tail
    where
    scale : ℚ
    scale =
      radius (derivativeStrictSubballScale ρ σ ρ<σ)

    scaled-shift-tail :
      TailBound
        (λ n → rational scale ·ᶜ shift (suc zero) v n)
        (derivativeStrictSubballModulus {ρ = ρ} {σ = σ} ρ<σ ν)
    scaled-shift-tail =
      rationalScaleTailBound
        scale
        {u = shift (suc zero) v}
        {μ = ν}
        (tailBound-shift
          {u = v}
          {μ = ν}
          (PowerSeriesMajorizedOnBall.majorTail
            {a = a}
            {ρ = σ}
            {v = v}
            {μ = ν}
            majorized)
          (suc zero))

    scaled-majorant-path :
      (λ n → rational scale ·ᶜ shift (suc zero) v n) ≡
      derivativeStrictSubballMajorant {ρ = ρ} {σ = σ} ρ<σ v
    scaled-majorant-path =
      funExt
        (λ n →
          mulᶜ-rational-left
            (radius (derivativeStrictSubballScale ρ σ ρ<σ))
            (v (suc n)))

  derivativeStrictSubballMajorAntitone :
    {a : PowerSeries} →
    {ρ σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    (ρ<σ : radius ρ ℚOrder.< radius σ) →
    PowerSeriesMajorizedOnBall a σ v ν →
    AntitoneNatModulus
      (derivativeStrictSubballModulus {ρ = ρ} {σ = σ} ρ<σ ν)
  derivativeStrictSubballMajorAntitone
      {a = a}
      {ρ = ρ}
      {σ = σ}
      {v = v}
      {ν = ν}
      ρ<σ
      majorized =
    rationalScaleModulus-antitone
      (radius (derivativeStrictSubballScale ρ σ ρ<σ))
      (PowerSeriesMajorizedOnBall.majorAntitone
        {a = a}
        {ρ = σ}
        {v = v}
        {μ = ν}
        majorized)

  derivativeStrictSubballTermMajorized :
    {a : PowerSeries} →
    {ρ σ : ℚ⁺} →
    {v : ℕ → ℝᶜ} →
    {ν : ℚ⁺ → ℕ} →
    (ρ<σ : radius ρ ℚOrder.< radius σ) →
    PowerSeriesMajorizedOnBall a σ v ν →
    (h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    absᶜ (powerSeriesTerm (derivativePowerSeries a) h n) ≤ᶜ
    derivativeStrictSubballMajorant {ρ = ρ} {σ = σ} ρ<σ v n
  derivativeStrictSubballTermMajorized
      {a = a}
      {ρ = ρ}
      {σ = σ}
      {v = v}
      {ν = ν}
      ρ<σ
      majorized
      h
      h-bound
      n =
    subst
      (λ term →
        absᶜ term ≤ᶜ
        derivativeStrictSubballMajorant {ρ = ρ} {σ = σ} ρ<σ v n)
      (sym (derivativePowerSeriesTerm a h n))
      derivative-term≤majorant
    where
    natural : ℚ
    natural =
      Rational.natMul (suc n) Rational.1ℚ

    invσsuc : ℚ
    invσsuc =
      radius (posInv⁺ (positivePower σ (suc n)))

    ρpow : ℚ
    ρpow =
      radius (positivePower ρ n)

    coeff : ℚ
    coeff =
      (natural ℚ.· invσsuc) ℚ.· ρpow

    scale : ℚ
    scale =
      radius (derivativeStrictSubballScale ρ σ ρ<σ)

    probe : ℝᶜ
    probe =
      powerSeriesTerm a (rational (radius σ)) (suc n)

    shifted-term : ℝᶜ
    shifted-term =
      powerSeriesTerm (λ k → a (suc k)) h n

    v-nonnegative : 0ᶜ ≤ᶜ v (suc n)
    v-nonnegative =
      PowerSeriesMajorizedOnBall.majorantNonnegative
        {a = a}
        {ρ = σ}
        {v = v}
        {μ = ν}
        majorized
        (suc n)

    invσsuc-nonnegative : Rational.0ℚ ℚOrder.≤ invσsuc
    invσsuc-nonnegative =
      Rational.<→≤
        {p = Rational.0ℚ}
        {q = invσsuc}
        (posInv⁺ (positivePower σ (suc n)) .snd)

    ρpow-nonnegative : Rational.0ℚ ℚOrder.≤ ρpow
    ρpow-nonnegative =
      Rational.<→≤
        {p = Rational.0ℚ}
        {q = ρpow}
        (positivePower ρ n .snd)

    natural-nonnegative : Rational.0ℚ ℚOrder.≤ natural
    natural-nonnegative =
      Rational.natMul-nonnegative (suc n) Rational.0<1

    coefficient-majorant-nonnegative :
      0ᶜ ≤ᶜ scalarMulᶜ invσsuc (v (suc n))
    coefficient-majorant-nonnegative =
      PowerSeriesMajorizedOnBall.shiftedPositiveScalarScaleMajorantNonnegative
        {a = a}
        {ρ = σ}
        {v = v}
        {μ = ν}
        invσsuc
        (posInv⁺ (positivePower σ (suc n)) .snd)
        majorized
        n

    h-power-majorant-nonnegative :
      0ᶜ ≤ᶜ rational ρpow
    h-power-majorant-nonnegative =
      ≤ℚ→rational≤ᶜ
        {q = Rational.0ℚ}
        {r = ρpow}
        ρpow-nonnegative

    shifted-majorant-nonnegative :
      0ᶜ ≤ᶜ scalarMulᶜ invσsuc (v (suc n)) ·ᶜ rational ρpow
    shifted-majorant-nonnegative =
      mulᶜ-nonnegative
        (scalarMulᶜ invσsuc (v (suc n)))
        (rational ρpow)
        coefficient-majorant-nonnegative
        h-power-majorant-nonnegative

    probe-majorized :
      SeriesMajorizedBy
        (powerSeriesTerm a (rational (radius σ)))
        v
    probe-majorized =
      PowerSeriesMajorizedOnBall.termMajorized
        {a = a}
        {ρ = σ}
        {v = v}
        {μ = ν}
        majorized
        (rational (radius σ))
        (positiveRationalSelfBounded σ)

    probe≤v :
      absᶜ probe ≤ᶜ v (suc n)
    probe≤v =
      SeriesMajorizedBy.termMajorized probe-majorized zero (suc n)

    coefficient≤majorant :
      absᶜ (a (suc n)) ≤ᶜ scalarMulᶜ invσsuc (v (suc n))
    coefficient≤majorant =
      subst
        (λ x → absᶜ x ≤ᶜ scalarMulᶜ invσsuc (v (suc n)))
        (powerSeriesCoefficientFromRationalProbe σ a (suc n))
        (absᶜ-scalarMul≤
          invσsuc
          invσsuc-nonnegative
          v-nonnegative
          probe≤v)

    h-power≤majorant :
      absᶜ (realPower h n) ≤ᶜ rational ρpow
    h-power≤majorant =
      bounded-byᶜ-abs≤rational
        (realPowerBoundsFromBound ρ h h-bound n)

    shifted≤majorant :
      absᶜ shifted-term ≤ᶜ
      scalarMulᶜ invσsuc (v (suc n)) ·ᶜ rational ρpow
    shifted≤majorant =
      absᶜ-mul≤product
        (a (suc n))
        (realPower h n)
        (scalarMulᶜ invσsuc (v (suc n)))
        (rational ρpow)
        coefficient-majorant-nonnegative
        h-power-majorant-nonnegative
        coefficient≤majorant
        h-power≤majorant

    natural-term≤product :
      absᶜ (naturalReal (suc n) ·ᶜ shifted-term) ≤ᶜ
      rational natural ·ᶜ
        (scalarMulᶜ invσsuc (v (suc n)) ·ᶜ rational ρpow)
    natural-term≤product =
      absᶜ-mul≤product
        (naturalReal (suc n))
        shifted-term
        (rational natural)
        (scalarMulᶜ invσsuc (v (suc n)) ·ᶜ rational ρpow)
        (≤ℚ→rational≤ᶜ
          {q = Rational.0ℚ}
          {r = natural}
          natural-nonnegative)
        shifted-majorant-nonnegative
        (absᶜ-rational-nonnegative natural natural-nonnegative)
        shifted≤majorant

    product≤majorant :
      rational natural ·ᶜ
        (scalarMulᶜ invσsuc (v (suc n)) ·ᶜ rational ρpow)
      ≤ᶜ
      scalarMulᶜ scale (v (suc n))
    product≤majorant =
      subst
        (λ x → x ≤ᶜ scalarMulᶜ scale (v (suc n)))
        (sym (tripleScalarProductPath natural invσsuc ρpow (v (suc n))))
        (PowerSeriesMajorizedOnBall.shiftedScalarScaleMajorant≤
          {a = a}
          {ρ = σ}
          {v = v}
          {μ = ν}
          coeff
          scale
          (derivativeStrictSubballCoefficient≤Scale
            {ρ = ρ}
            {σ = σ}
            ρ<σ
            n)
          majorized
          n)

    derivative-term≤majorant :
      absᶜ (naturalReal (suc n) ·ᶜ shifted-term) ≤ᶜ
      derivativeStrictSubballMajorant {ρ = ρ} {σ = σ} ρ<σ v n
    derivative-term≤majorant =
      ≤ᶜ-trans
        {x = absᶜ (naturalReal (suc n) ·ᶜ shifted-term)}
        {y =
          rational natural ·ᶜ
            (scalarMulᶜ invσsuc (v (suc n)) ·ᶜ rational ρpow)}
        {z = derivativeStrictSubballMajorant {ρ = ρ} {σ = σ} ρ<σ v n}
        natural-term≤product
        product≤majorant


derivativePowerSeriesOnStrictSubballWithFromMajorizedOnBall :
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {ν : ℚ⁺ → ℕ} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  PowerSeriesMajorizedOnBall a σ v ν →
  HasPowerSeriesOnBallWith
    (derivativePowerSeries a)
    ρ
    (derivativeStrictSubballModulus {ρ = ρ} {σ = σ} ρ<σ ν)
derivativePowerSeriesOnStrictSubballWithFromMajorizedOnBall
    {a = a}
    {ρ = ρ}
    {σ = σ}
    {v = v}
    {ν = ν}
    ρ<σ
    majorized =
  majorizedOnBall→hasPowerSeriesOnBallWith
    (powerSeriesMajorizedOnBallFromTermBounds
      {a = derivativePowerSeries a}
      {ρ = ρ}
      {v = derivativeStrictSubballMajorant {ρ = ρ} {σ = σ} ρ<σ v}
      {μ = derivativeStrictSubballModulus {ρ = ρ} {σ = σ} ρ<σ ν}
      (derivativeStrictSubballTermMajorized
        {a = a} {ρ = ρ} {σ = σ} {v = v} {ν = ν}
        ρ<σ majorized)
      (derivativeStrictSubballMajorantNonnegative
        {a = a} {ρ = ρ} {σ = σ} {v = v} {ν = ν}
        ρ<σ majorized)
      (derivativeStrictSubballMajorTail
        {a = a} {ρ = ρ} {σ = σ} {v = v} {ν = ν}
        ρ<σ majorized)
      (derivativeStrictSubballMajorAntitone
        {a = a} {ρ = ρ} {σ = σ} {v = v} {ν = ν}
        ρ<σ majorized))


derivativePowerSeriesMajorizedOnStrictSubballFromMajorizedOnBall :
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {ν : ℚ⁺ → ℕ} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  PowerSeriesMajorizedOnBall a σ v ν →
  PowerSeriesMajorizedOnBall
    (derivativePowerSeries a)
    ρ
    (derivativePowerSeriesStrictSubballMajorant
      {ρ = ρ}
      {σ = σ}
      ρ<σ
      v)
    (derivativeStrictSubballModulus {ρ = ρ} {σ = σ} ρ<σ ν)
derivativePowerSeriesMajorizedOnStrictSubballFromMajorizedOnBall
  {a = a}
  {ρ = ρ}
  {σ = σ}
  {v = v}
  {ν = ν}
  ρ<σ
  majorized =
  powerSeriesMajorizedOnBallFromTermBounds
    (derivativeStrictSubballTermMajorized
      {a = a} {ρ = ρ} {σ = σ} {v = v} {ν = ν}
      ρ<σ majorized)
    (derivativeStrictSubballMajorantNonnegative
      {a = a} {ρ = ρ} {σ = σ} {v = v} {ν = ν}
      ρ<σ majorized)
    (derivativeStrictSubballMajorTail
      {a = a} {ρ = ρ} {σ = σ} {v = v} {ν = ν}
      ρ<σ majorized)
    (derivativeStrictSubballMajorAntitone
      {a = a} {ρ = ρ} {σ = σ} {v = v} {ν = ν}
      ρ<σ majorized)


derivativePowerSeriesOnStrictSubballFromMajorizedOnBall :
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {ν : ℚ⁺ → ℕ} →
  radius ρ ℚOrder.< radius σ →
  PowerSeriesMajorizedOnBall a σ v ν →
  HasPowerSeriesOnBall (derivativePowerSeries a) ρ
derivativePowerSeriesOnStrictSubballFromMajorizedOnBall
    {a = a}
    {ρ = ρ}
    {σ = σ}
    {v = v}
    {ν = ν}
    ρ<σ
    majorized =
  derivativeStrictSubballModulus {ρ = ρ} {σ = σ} ρ<σ ν ,
  derivativePowerSeriesOnStrictSubballWithFromMajorizedOnBall
    {a = a}
    {ρ = ρ}
    {σ = σ}
    {v = v}
    {ν = ν}
    ρ<σ
    majorized
