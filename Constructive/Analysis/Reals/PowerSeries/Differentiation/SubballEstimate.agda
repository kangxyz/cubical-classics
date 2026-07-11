{-

Term estimates for strict-subball derivative convergence from ball convergence.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Differentiation.SubballEstimate where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Modulus using (AntitoneNatModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
  using (0ᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
  using
    ( _·ᶜ_
    ; mulᶜ-assoc
    ; mulᶜ-rational-left
    ; mulᶜ-rational-rational
    )
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
  using (scalarMulᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_ ; ≤ᶜ-trans)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using
    ( absᶜ
    )
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
  using (≤ℚ→rational≤ᶜ)
open import Constructive.Analysis.Reals.Series
  using
    ( TailBound
    ; shift
    ; shift-index
    ; tailSum-one
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
open import Constructive.Analysis.Reals.Series.Geometric.Positive
open import Constructive.Analysis.GeometricDecay.Rational
  using (rationalPower ; rationalRatioPowerTimesPower)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Power
  using (realPower ; realPowerBoundsFromBound)
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( rationalScaleModulus-antitone
    ; rationalScaleTailBound
    )
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Bounds
  using
    ( positiveRationalSelfBounded
    ; powerSeriesCoefficientFromRationalProbe
    )
open import Constructive.Analysis.Reals.PowerSeries.FormalDerivative
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open import Constructive.Analysis.Reals.PowerSeries.Differentiation.Bounds
  using (geometricLinearCoefficient≤)
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.SubballParameters


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    weighted-scale-sigma-cancel-form :
      (i b p s sn : 𝓡 .fst) →
      ((i · b) · p) · (s · sn) ≡ (i · s) · ((b · p) · sn)
    weighted-scale-sigma-cancel-form _ _ _ _ _ = solve! 𝓡

    coefficient-sigma-cancel-form :
      (N i r s : 𝓡 .fst) →
      ((N · i) · r) · s ≡ N · ((i · s) · r)
    coefficient-sigma-cancel-form _ _ _ _ = solve! 𝓡

    weighted-ratio-scale-form :
      (N r s t : 𝓡 .fst) →
      ((N · r) · s) · t ≡ N · ((r · s) · t)
    weighted-ratio-scale-form _ _ _ _ = solve! 𝓡


constantTailModulusAntitone :
  {N : ℕ} →
  AntitoneNatModulus (λ _ → N)
constantTailModulusAntitone _ =
  zero , refl


derivativeStrictSubballFromOnBallMajorant :
  {ρ σ : ℚ⁺} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  ℕ →
  ℝᶜ
derivativeStrictSubballFromOnBallMajorant {ρ = ρ} {σ = σ} ρ<σ n =
  rational
    (radius (derivativeStrictSubballFromOnBallScale {ρ = ρ} {σ = σ} ρ<σ))
    ·ᶜ
  positiveGeometricTerm
    (derivativeStrictSubballOuterRatio {ρ = ρ} {σ = σ} ρ<σ)
    n


derivativeStrictSubballFromOnBallMajorTail :
  {ρ σ : ℚ⁺} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  TailBound
    (derivativeStrictSubballFromOnBallMajorant {ρ = ρ} {σ = σ} ρ<σ)
    (derivativeStrictSubballFromOnBallGeometricModulus {ρ = ρ} {σ = σ} ρ<σ)
derivativeStrictSubballFromOnBallMajorTail {ρ = ρ} {σ = σ} ρ<σ =
  rationalScaleTailBound
    (radius (derivativeStrictSubballFromOnBallScale {ρ = ρ} {σ = σ} ρ<σ))
    {u = positiveGeometricTerm outer}
    {μ = positiveGeometricPowerModulus outer outer<1}
    (positiveGeometricFiniteTailBoundFromRatio outer outer<1)
  where
  outer : ℚ⁺
  outer =
    derivativeStrictSubballOuterRatio {ρ = ρ} {σ = σ} ρ<σ

  outer<1 : radius outer ℚOrder.< Rational.1ℚ
  outer<1 =
    derivativeStrictSubballOuterRatio<1 {ρ = ρ} {σ = σ} ρ<σ


derivativeStrictSubballFromOnBallMajorAntitone :
  {ρ σ : ℚ⁺} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  AntitoneNatModulus
    (derivativeStrictSubballFromOnBallGeometricModulus {ρ = ρ} {σ = σ} ρ<σ)
derivativeStrictSubballFromOnBallMajorAntitone {ρ = ρ} {σ = σ} ρ<σ =
  rationalScaleModulus-antitone
    (radius (derivativeStrictSubballFromOnBallScale {ρ = ρ} {σ = σ} ρ<σ))
    (positiveGeometricPowerModulus-antitone outer outer<1)
  where
  outer : ℚ⁺
  outer =
    derivativeStrictSubballOuterRatio {ρ = ρ} {σ = σ} ρ<σ

  outer<1 : radius outer ℚOrder.< Rational.1ℚ
  outer<1 =
    derivativeStrictSubballOuterRatio<1 {ρ = ρ} {σ = σ} ρ<σ


scalarMulRationalOnePath :
  (q : ℚ) →
  scalarMulᶜ q (rational Rational.1ℚ) ≡ rational q
scalarMulRationalOnePath q =
  sym (mulᶜ-rational-left q (rational Rational.1ℚ)) ∙
  mulᶜ-rational-rational q Rational.1ℚ ∙
  cong rational (ℚ.·IdR q)


transportAbs≤Left :
  {x y M : ℝᶜ} →
  x ≡ y →
  absᶜ y ≤ᶜ M →
  absᶜ x ≤ᶜ M
transportAbs≤Left {M = M} p bound =
  subst
    (λ z → absᶜ z ≤ᶜ M)
    (sym p)
    bound


transport≤RightBack :
  {x y z : ℝᶜ} →
  y ≡ z →
  x ≤ᶜ z →
  x ≤ᶜ y
transport≤RightBack {x = x} p bound =
  subst
    (λ t → x ≤ᶜ t)
    (sym p)
    bound


geometricMajorantPath :
  {ρ σ : ℚ⁺} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  (n : ℕ) →
  derivativeStrictSubballFromOnBallMajorant {ρ = ρ} {σ = σ} ρ<σ n ≡
  rational
    (radius (derivativeStrictSubballFromOnBallScale {ρ = ρ} {σ = σ} ρ<σ)
      ℚ.·
     rationalPower
       (radius (derivativeStrictSubballOuterRatio {ρ = ρ} {σ = σ} ρ<σ))
       n)
geometricMajorantPath {ρ = ρ} {σ = σ} ρ<σ n =
  mulᶜ-rational-rational scale (radius (positivePower outer n)) ∙
  cong rational (cong (scale ℚ.·_) (positivePower-radius outer n))
  where
  scale : ℚ
  scale =
    radius (derivativeStrictSubballFromOnBallScale {ρ = ρ} {σ = σ} ρ<σ)

  outer : ℚ⁺
  outer =
    derivativeStrictSubballOuterRatio {ρ = ρ} {σ = σ} ρ<σ


derivativeStrictSubballWeightedCoefficient≤ :
  {ρ σ : ℚ⁺} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  (n : ℕ) →
  ((Rational.natMul (suc n) Rational.1ℚ ℚ.·
    radius (posInv⁺ (positivePower σ (suc n)))) ℚ.·
    radius (positivePower ρ n))
  ℚOrder.≤
  radius (derivativeStrictSubballFromOnBallScale {ρ = ρ} {σ = σ} ρ<σ)
    ℚ.·
    rationalPower
      (radius (derivativeStrictSubballOuterRatio {ρ = ρ} {σ = σ} ρ<σ))
      n
derivativeStrictSubballWeightedCoefficient≤ {ρ = ρ} {σ = σ} ρ<σ n =
  Rational.mul-right-cancel-positive-≤
    {p = coeff}
    {q = target}
    {c = σsuc}
    (positivePower σ (suc n) .snd)
    coeffσ≤targetσ
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

  σpow : ℚ
  σpow =
    radius (positivePower σ n)

  σsuc : ℚ
  σsuc =
    radius (positivePower σ (suc n))

  coeff : ℚ
  coeff =
    (natural ℚ.· invσsuc) ℚ.· ρpow

  ratio : ℚ⁺
  ratio =
    ratio⁺ ρ σ

  outer : ℚ⁺
  outer =
    derivativeStrictSubballOuterRatio {ρ = ρ} {σ = σ} ρ<σ

  inner : ℚ⁺
  inner =
    derivativeStrictSubballInnerRatio {ρ = ρ} {σ = σ} ρ<σ

  gap : ℚ⁺
  gap =
    derivativeStrictSubballInnerGap {ρ = ρ} {σ = σ} ρ<σ

  bound : ℚ
  bound =
    Rational.1ℚ ℚ.+ radius (posInv⁺ gap)

  scale : ℚ
  scale =
    radius (derivativeStrictSubballFromOnBallScale {ρ = ρ} {σ = σ} ρ<σ)

  spow : ℚ
  spow =
    rationalPower (radius outer) n

  innerpow : ℚ
  innerpow =
    rationalPower (radius inner) n

  target : ℚ
  target =
    scale ℚ.· spow

  left-path :
    coeff ℚ.· σsuc ≡ natural ℚ.· ρpow
  left-path =
    SolverHelpers.coefficient-sigma-cancel-form
      ℚCommRing
      natural
      invσsuc
      ρpow
      σsuc ∙
    cong
      (λ x → natural ℚ.· (x ℚ.· ρpow))
      (Rational.posInv-left σsuc (positivePower σ (suc n) .snd)) ∙
    cong (natural ℚ.·_) (ℚ.·IdL ρpow)

  right-path :
    target ℚ.· σsuc ≡ (bound ℚ.· spow) ℚ.· σpow
  right-path =
    SolverHelpers.weighted-scale-sigma-cancel-form
      ℚCommRing
      (radius (posInv⁺ σ))
      bound
      spow
      (radius σ)
      σpow ∙
    cong
      (λ x → x ℚ.· ((bound ℚ.· spow) ℚ.· σpow))
      (Rational.posInv-left (radius σ) (σ .snd)) ∙
    ℚ.·IdL ((bound ℚ.· spow) ℚ.· σpow)

  linear≤ :
    natural ℚ.· innerpow ℚOrder.≤ bound
  linear≤ =
    geometricLinearCoefficient≤
      inner
      gap
      (derivativeStrictSubballInnerRatio<1 {ρ = ρ} {σ = σ} ρ<σ)
      refl
      n

  spow-nonnegative : Rational.0ℚ ℚOrder.≤ spow
  spow-nonnegative =
    positiveRationalPower-nonnegative outer n

  σpow-nonnegative : Rational.0ℚ ℚOrder.≤ σpow
  σpow-nonnegative =
    Rational.<→≤
      {p = Rational.0ℚ}
      {q = σpow}
      (positivePower σ n .snd)

  scaled-inner≤ :
    ((natural ℚ.· innerpow) ℚ.· spow) ℚ.· σpow
      ℚOrder.≤
    (bound ℚ.· spow) ℚ.· σpow
  scaled-inner≤ =
    ℚOrder.≤-·o
      ((natural ℚ.· innerpow) ℚ.· spow)
      (bound ℚ.· spow)
      σpow
      σpow-nonnegative
      (ℚOrder.≤-·o
        (natural ℚ.· innerpow)
        bound
        spow
        spow-nonnegative
        linear≤)

  ratio-path :
    ((natural ℚ.· innerpow) ℚ.· spow) ℚ.· σpow
    ≡
    natural ℚ.· ρpow
  ratio-path =
    SolverHelpers.weighted-ratio-scale-form
      ℚCommRing
      natural
      innerpow
      spow
      σpow ∙
    cong
      (λ x → natural ℚ.· (x ℚ.· σpow))
      (rationalRatioPowerTimesPower
        (radius ratio)
        (radius outer)
        (outer .snd)
        n) ∙
    cong (natural ℚ.·_) (ratioPowerTimesPositivePower ρ σ n)

  scaled≤ :
    natural ℚ.· ρpow ℚOrder.≤ (bound ℚ.· spow) ℚ.· σpow
  scaled≤ =
    subst
      (λ x → x ℚOrder.≤ (bound ℚ.· spow) ℚ.· σpow)
      ratio-path
      scaled-inner≤

  coeffσ≤targetσ :
    coeff ℚ.· σsuc ℚOrder.≤ target ℚ.· σsuc
  coeffσ≤targetσ =
    subst2
      ℚOrder._≤_
      (sym left-path)
      (sym right-path)
      scaled≤


derivativeStrictSubballTermMajorizedFromProbeBound :
  {a : PowerSeries} →
  {ρ σ : ℚ⁺} →
  (ρ<σ : radius ρ ℚOrder.< radius σ) →
  (h : ℝᶜ) →
  BoundedByᶜ ρ h →
  (n : ℕ) →
  BoundedByᶜ
    1⁺
    (powerSeriesTerm a (rational (radius σ)) (suc n)) →
  absᶜ (powerSeriesTerm (derivativePowerSeries a) h n) ≤ᶜ
  derivativeStrictSubballFromOnBallMajorant {ρ = ρ} {σ = σ} ρ<σ n
derivativeStrictSubballTermMajorizedFromProbeBound
    {a = a}
    {ρ = ρ}
    {σ = σ}
    ρ<σ
    h
    h-bound
    n
    probe-bound =
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
    radius (derivativeStrictSubballFromOnBallScale {ρ = ρ} {σ = σ} ρ<σ)

  spow : ℚ
  spow =
    rationalPower
      (radius (derivativeStrictSubballOuterRatio {ρ = ρ} {σ = σ} ρ<σ))
      n

  probe : ℝᶜ
  probe =
    powerSeriesTerm a (rational (radius σ)) (suc n)

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
    0ᶜ ≤ᶜ scalarMulᶜ invσsuc (rational Rational.1ℚ)
  coefficient-majorant-nonnegative =
    subst
      (λ x → 0ᶜ ≤ᶜ x)
      (sym (scalarMulRationalOnePath invσsuc))
      (≤ℚ→rational≤ᶜ
        {q = Rational.0ℚ}
        {r = invσsuc}
        invσsuc-nonnegative)

  h-power-majorant-nonnegative :
    0ᶜ ≤ᶜ rational ρpow
  h-power-majorant-nonnegative =
    ≤ℚ→rational≤ᶜ
      {q = Rational.0ℚ}
      {r = ρpow}
      ρpow-nonnegative

  probe≤1 :
    absᶜ probe ≤ᶜ rational Rational.1ℚ
  probe≤1 =
    bounded-byᶜ-abs≤rational probe-bound

  coefficient≤majorant :
    absᶜ (a (suc n)) ≤ᶜ
    scalarMulᶜ invσsuc (rational Rational.1ℚ)
  coefficient≤majorant =
    subst
      (λ x →
        absᶜ x ≤ᶜ
        scalarMulᶜ invσsuc (rational Rational.1ℚ))
      (powerSeriesCoefficientFromRationalProbe σ a (suc n))
      (absᶜ-scalarMul≤
        invσsuc
        invσsuc-nonnegative
        (≤ℚ→rational≤ᶜ
          {q = Rational.0ℚ}
          {r = Rational.1ℚ}
          (Rational.<→≤
            {p = Rational.0ℚ}
            {q = Rational.1ℚ}
            Rational.0<1))
        probe≤1)

  h-power≤majorant :
    absᶜ (realPower h n) ≤ᶜ rational ρpow
  h-power≤majorant =
    bounded-byᶜ-abs≤rational
      (realPowerBoundsFromBound ρ h h-bound n)

  derivative-coefficient-majorant-nonnegative :
    0ᶜ ≤ᶜ rational natural ·ᶜ
      scalarMulᶜ invσsuc (rational Rational.1ℚ)
  derivative-coefficient-majorant-nonnegative =
    mulᶜ-nonnegative
      (rational natural)
      (scalarMulᶜ invσsuc (rational Rational.1ℚ))
      (≤ℚ→rational≤ᶜ
        {q = Rational.0ℚ}
        {r = natural}
        natural-nonnegative)
      coefficient-majorant-nonnegative

  derivative-coefficient≤majorant :
    absᶜ (derivativePowerSeries a n) ≤ᶜ
    rational natural ·ᶜ
      scalarMulᶜ invσsuc (rational Rational.1ℚ)
  derivative-coefficient≤majorant =
    absᶜ-mul≤product
      (naturalReal (suc n))
      (a (suc n))
      (rational natural)
      (scalarMulᶜ invσsuc (rational Rational.1ℚ))
      (≤ℚ→rational≤ᶜ
        {q = Rational.0ℚ}
        {r = natural}
        natural-nonnegative)
      coefficient-majorant-nonnegative
      (absᶜ-rational-nonnegative natural natural-nonnegative)
      coefficient≤majorant

  term≤product :
    absᶜ (powerSeriesTerm (derivativePowerSeries a) h n) ≤ᶜ
    (rational natural ·ᶜ scalarMulᶜ invσsuc (rational Rational.1ℚ)) ·ᶜ
      rational ρpow
  term≤product =
    absᶜ-mul≤product
      (derivativePowerSeries a n)
      (realPower h n)
      (rational natural ·ᶜ scalarMulᶜ invσsuc (rational Rational.1ℚ))
      (rational ρpow)
      derivative-coefficient-majorant-nonnegative
      h-power-majorant-nonnegative
      derivative-coefficient≤majorant
      h-power≤majorant

  product-path :
    (rational natural ·ᶜ scalarMulᶜ invσsuc (rational Rational.1ℚ)) ·ᶜ
      rational ρpow
    ≡
    rational coeff
  product-path =
    sym
      (mulᶜ-assoc
        (rational natural)
        (scalarMulᶜ invσsuc (rational Rational.1ℚ))
        (rational ρpow)) ∙
    tripleScalarProductPath
      natural
      invσsuc
      ρpow
      (rational Rational.1ℚ) ∙
    scalarMulRationalOnePath coeff

  product≤rational-majorant :
    (rational natural ·ᶜ scalarMulᶜ invσsuc (rational Rational.1ℚ)) ·ᶜ
      rational ρpow
    ≤ᶜ
    rational (scale ℚ.· spow)
  product≤rational-majorant =
    subst
      (λ x → x ≤ᶜ rational (scale ℚ.· spow))
      (sym product-path)
      (≤ℚ→rational≤ᶜ
        (derivativeStrictSubballWeightedCoefficient≤
          {ρ = ρ}
          {σ = σ}
          ρ<σ
          n))

  product≤majorant :
    (rational natural ·ᶜ scalarMulᶜ invσsuc (rational Rational.1ℚ)) ·ᶜ
      rational ρpow
    ≤ᶜ
    derivativeStrictSubballFromOnBallMajorant {ρ = ρ} {σ = σ} ρ<σ n
  product≤majorant =
    subst
      (λ x →
        (rational natural ·ᶜ
         scalarMulᶜ invσsuc (rational Rational.1ℚ)) ·ᶜ
          rational ρpow
        ≤ᶜ x)
      (sym (geometricMajorantPath {ρ = ρ} {σ = σ} ρ<σ n))
      product≤rational-majorant

  derivative-term≤majorant :
    absᶜ (powerSeriesTerm (derivativePowerSeries a) h n) ≤ᶜ
    derivativeStrictSubballFromOnBallMajorant {ρ = ρ} {σ = σ} ρ<σ n
  derivative-term≤majorant =
    ≤ᶜ-trans
      {x = absᶜ (powerSeriesTerm (derivativePowerSeries a) h n)}
      {y =
        (rational natural ·ᶜ
         scalarMulᶜ invσsuc (rational Rational.1ℚ)) ·ᶜ
          rational ρpow}
      {z = derivativeStrictSubballFromOnBallMajorant {ρ = ρ} {σ = σ} ρ<σ n}
      term≤product
      product≤majorant


derivativeStrictSubballProbeTermBound :
  {a : PowerSeries} →
  {σ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesOnBallWith a σ μ →
  (n : ℕ) →
  NatOrder._≤_ (μ 1⁺) (suc n) →
  BoundedByᶜ
    1⁺
    (powerSeriesTerm a (rational (radius σ)) (suc n))
derivativeStrictSubballProbeTermBound {a = a} {σ = σ} {μ = μ}
    convergence n μ1≤sucn =
  subst
    (BoundedByᶜ 1⁺)
    (tailSum-one (powerSeriesTerm a (rational (radius σ))) (suc n))
    (HasPowerSeriesOnBallWith.tailBound
      convergence
      (rational (radius σ))
      (positiveRationalSelfBounded σ)
      1⁺
      (suc n)
      (suc zero)
      μ1≤sucn)


abstract
  derivativeStrictSubballTermMajorizedFromProbeBoundOpaque :
    {a : PowerSeries} →
    {ρ σ : ℚ⁺} →
    (ρ<σ : radius ρ ℚOrder.< radius σ) →
    (h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (n : ℕ) →
    BoundedByᶜ
      1⁺
      (powerSeriesTerm a (rational (radius σ)) (suc n)) →
    absᶜ (powerSeriesTerm (derivativePowerSeries a) h n) ≤ᶜ
    derivativeStrictSubballFromOnBallMajorant {ρ = ρ} {σ = σ} ρ<σ n
  derivativeStrictSubballTermMajorizedFromProbeBoundOpaque =
    derivativeStrictSubballTermMajorizedFromProbeBound

  derivativeStrictSubballProbeTermBoundOpaque :
    {a : PowerSeries} →
    {σ : ℚ⁺} →
    {μ : ℚ⁺ → ℕ} →
    HasPowerSeriesOnBallWith a σ μ →
    (n : ℕ) →
    NatOrder._≤_ (μ 1⁺) (suc n) →
    BoundedByᶜ
      1⁺
      (powerSeriesTerm a (rational (radius σ)) (suc n))
  derivativeStrictSubballProbeTermBoundOpaque =
    derivativeStrictSubballProbeTermBound

  derivativeStrictSubballDroppedTerm≤Majorant :
    {a : PowerSeries} →
    {ρ σ : ℚ⁺} →
    {μ : ℚ⁺ → ℕ} →
    (ρ<σ : radius ρ ℚOrder.< radius σ) →
    HasPowerSeriesOnBallWith a σ μ →
    (h : ℝᶜ) →
    BoundedByᶜ ρ h →
    (m j : ℕ) →
    NatOrder._≤_ (μ 1⁺) (suc (m Nat.+ j)) →
    absᶜ
      (shift m (powerSeriesTerm (derivativePowerSeries a) h) j)
    ≤ᶜ
    shift m
      (derivativeStrictSubballFromOnBallMajorant {ρ = ρ} {σ = σ} ρ<σ)
      j
  derivativeStrictSubballDroppedTerm≤Majorant
      {a = a}
      {ρ = ρ}
      {σ = σ}
      {μ = μ}
      ρ<σ
      convergence
      h
      h-bound
      m
      j
      μ1≤sucm+j =
    transportAbs≤Left
      (shift-index m derivativeTerms j)
      (transport≤RightBack
        (shift-index m majorant j)
        (derivativeStrictSubballTermMajorizedFromProbeBoundOpaque
          {a = a}
          {ρ = ρ}
          {σ = σ}
          ρ<σ
          h
          h-bound
          (m Nat.+ j)
          (derivativeStrictSubballProbeTermBoundOpaque
            {a = a}
            {σ = σ}
            {μ = μ}
            convergence
            (m Nat.+ j)
            μ1≤sucm+j)))
    where
    derivativeTerms : ℕ → ℝᶜ
    derivativeTerms =
      powerSeriesTerm (derivativePowerSeries a) h

    majorant : ℕ → ℝᶜ
    majorant =
      derivativeStrictSubballFromOnBallMajorant {ρ = ρ} {σ = σ} ρ<σ
