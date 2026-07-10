{-

Part of Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Finite where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; max ; suc ; zero)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.Calculus.Derivative.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.CommRing
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base using (_≤ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.Series
  using
    ( partialSum
    ; partialSum-add
    ; seriesSumFromFiniteTailBoundConvergesAt
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower ; realPowerBoundsFromBound)
open import Constructive.Analysis.GeometricDecay
  using (positivePower)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( addPowerSeries
    ; addPowerSeriesTerm
    ; bounded-byᶜ-zero
    ; powerSeriesPartialSum-add
    ; powerSeriesPartialSum-shift
    ; shiftPowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using
    ( derivativePowerSeries
    ; derivativePrimitivePowerSeries
    ; naturalReal
    ; primitivePowerSeries
    )
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open ClosenessOf RationalsMetricSpace

open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Internal
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Index

powerSeriesPartialSum-one :
  (a : PowerSeries) →
  (y : ℝᶜ) →
  powerSeriesPartialSum a y (suc zero) ≡ a zero
powerSeriesPartialSum-one a y =
  powerSeriesPartialSum-shift a y zero ∙
  cong (a zero +ᶜ_) (mulᶜ-zero-right y) ∙
  add-zero-right (a zero)


powerSeriesConstantPartialSumRemainder-zero :
  (a da : PowerSeries) →
  (x h : ℝᶜ) →
  linearRemainder
    (λ y → powerSeriesPartialSum a y (suc zero))
    x
    (powerSeriesPartialSum da x zero)
    h
  ≡ 0ᶜ
powerSeriesConstantPartialSumRemainder-zero a da x h =
  cong₂
    (λ u v →
      (u +ᶜ (-ᶜ v)) +ᶜ
      (-ᶜ (powerSeriesPartialSum da x zero ·ᶜ h)))
    (powerSeriesPartialSum-one a (x +ᶜ h))
    (powerSeriesPartialSum-one a x) ∙
  SolverHelpers.constant-linear-remainder-zero
    CauchyRealsCommRing
    (a zero)
    h


powerSeriesConstantPartialSumHasDerivativeAtWith :
  {a da : PowerSeries} →
  {x : ℝᶜ} →
  {μ : PrecisionModulus} →
  HasDerivativeAtWith
    (λ y → powerSeriesPartialSum a y (suc zero))
    x
    (powerSeriesPartialSum da x zero)
    μ
powerSeriesConstantPartialSumHasDerivativeAtWith
  {a = a}
  {da = da}
  {x = x}
  ε
  η
  _
  h
  _ =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (sym (powerSeriesConstantPartialSumRemainder-zero a da x h))
    (bounded-byᶜ-zero (ε *⁺ η))






naturalReal-suc :
  (n : ℕ) →
  naturalReal (suc n) ≡ naturalReal n +ᶜ 1ᶜ
naturalReal-suc n =
  cong rational (Rational.natMul-suc n Rational.1ℚ) ∙
  sym (add-rational (Rational.natMul n Rational.1ℚ) Rational.1ℚ)


derivativePowerSeries-shift-coefficient :
  (a : PowerSeries) →
  (n : ℕ) →
  shiftPowerSeries (derivativePowerSeries a) n ≡
  addPowerSeries
    (shiftPowerSeries (shiftPowerSeries a))
    (derivativePowerSeries (shiftPowerSeries a))
    n
derivativePowerSeries-shift-coefficient a n =
  cong
    (_·ᶜ a (suc (suc n)))
    (naturalReal-suc (suc n)) ∙
  mulᶜ-distrib-left
    (naturalReal (suc n))
    1ᶜ
    (a (suc (suc n))) ∙
  cong
    (naturalReal (suc n) ·ᶜ a (suc (suc n)) +ᶜ_)
    (mulᶜ-one-left (a (suc (suc n)))) ∙
  add-comm
    (naturalReal (suc n) ·ᶜ a (suc (suc n)))
    (a (suc (suc n)))


powerSeriesDerivativeShiftPartialSum-decomposition :
  (a : PowerSeries) →
  (x : ℝᶜ) →
  (n : ℕ) →
  powerSeriesPartialSum (shiftPowerSeries (derivativePowerSeries a)) x n ≡
  powerSeriesPartialSum (shiftPowerSeries (shiftPowerSeries a)) x n +ᶜ
  powerSeriesPartialSum (derivativePowerSeries (shiftPowerSeries a)) x n
powerSeriesDerivativeShiftPartialSum-decomposition a x n =
  powerSeriesPartialSum-cong
    (derivativePowerSeries-shift-coefficient a)
    refl
    n ∙
  powerSeriesPartialSum-add
    (shiftPowerSeries (shiftPowerSeries a))
    (derivativePowerSeries (shiftPowerSeries a))
    x
    n


powerSeriesFormalDerivativePartialSum-step-value :
  (a : PowerSeries) →
  (x : ℝᶜ) →
  (n : ℕ) →
  powerSeriesPartialSum (derivativePowerSeries a) x (suc n) ≡
  powerSeriesPartialSum (shiftPowerSeries a) x (suc n) +ᶜ
  x ·ᶜ powerSeriesPartialSum (derivativePowerSeries (shiftPowerSeries a)) x n
powerSeriesFormalDerivativePartialSum-step-value a x n =
  powerSeriesPartialSum-shift (derivativePowerSeries a) x n ∙
  cong₂
    _+ᶜ_
    (mulᶜ-one-left (a (suc zero)))
    (cong
      (x ·ᶜ_)
      (powerSeriesDerivativeShiftPartialSum-decomposition a x n)) ∙
  cong
    (a (suc zero) +ᶜ_)
    (mulᶜ-distrib-right x shiftSum derivativeShiftSum) ∙
  add-assoc
    (a (suc zero))
    (x ·ᶜ shiftSum)
    (x ·ᶜ derivativeShiftSum) ∙
  cong
    (_+ᶜ (x ·ᶜ derivativeShiftSum))
    (sym (powerSeriesPartialSum-shift (shiftPowerSeries a) x n))
  where
  shiftSum : ℝᶜ
  shiftSum =
    powerSeriesPartialSum (shiftPowerSeries (shiftPowerSeries a)) x n

  derivativeShiftSum : ℝᶜ
  derivativeShiftSum =
    powerSeriesPartialSum (derivativePowerSeries (shiftPowerSeries a)) x n
