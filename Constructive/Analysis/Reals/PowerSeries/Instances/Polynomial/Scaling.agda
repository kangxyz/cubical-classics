{-

Part of Constructive.Analysis.Reals.PowerSeries.Instances.Polynomial

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Polynomial.Scaling where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.FinData.Base using (Fin)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using (neg-zeroᶜ)
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Analytic
  using (HasPowerSeriesAt)
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using (rationalScalePowerSeries)
open import Constructive.Data.PositiveRationals

open import Constructive.Analysis.Reals.PowerSeries.Instances.Polynomial.FiniteSupport
open import Constructive.Analysis.Reals.PowerSeries.Instances.Polynomial.Closure
open import Constructive.Analysis.Reals.PowerSeries.Instances.Polynomial.FiniteSeries
open import Constructive.Analysis.Reals.PowerSeries.Instances.Polynomial.Derivative
open import Constructive.Analysis.Reals.PowerSeries.Instances.Polynomial.Primitive

rationalScalePowerSeriesZeroAfter :
  (q : ℚ) →
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a N →
  PowerSeriesZeroAfter (rationalScalePowerSeries q a) N
rationalScalePowerSeriesZeroAfter q N zeroAfter n N≤n =
  cong
    (λ c → rational q ·ᶜ c)
    (zeroAfter n N≤n) ∙
  mulᶜ-zero-right (rational q)


rationalScalePowerSeriesPolynomial :
  (q : ℚ) →
  {a : PowerSeries} →
  IsPolynomialPowerSeries a →
  IsPolynomialPowerSeries (rationalScalePowerSeries q a)
rationalScalePowerSeriesPolynomial q (N , zeroAfter) =
  N , rationalScalePowerSeriesZeroAfter q N zeroAfter
