{-

Part of Constructive.Analysis.Reals.PowerSeries.Instances.Polynomial

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Polynomial.Closure where

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
  using
    ( AnalyticAt
    ; HasPowerSeriesAt
    ; HasPowerSeriesAtOnBall
    ; HasPowerSeriesAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using
    ( derivativePowerSeries
    ; inverseSucReal
    ; naturalReal
    ; primitivePowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct
  using (cauchyProductPowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( bounded-byᶜ-zero
    ; addPowerSeries
    ; constantPowerSeries
    ; negPowerSeries
    ; powerSeriesPartialSum-shift
    ; rationalScalePowerSeries
    ; shiftPowerSeries
    ; subPowerSeries
    ; tailSum-zero-sequence
    ; zeroPowerSeries
    )
open import Constructive.Data.PositiveRationals

open import Constructive.Analysis.Reals.PowerSeries.Instances.Polynomial.Internal
open import Constructive.Analysis.Reals.PowerSeries.Instances.Polynomial.FiniteSupport

addPowerSeriesZeroAfter :
  {a b : PowerSeries} →
  (N M : ℕ) →
  PowerSeriesZeroAfter a N →
  PowerSeriesZeroAfter b M →
  PowerSeriesZeroAfter (addPowerSeries a b) (Nat.max N M)
addPowerSeriesZeroAfter {a = a} {b = b} N M a-zero b-zero n max≤n =
  cong₂
    _+ᶜ_
    (a-zero n (NatOrder.≤-trans N≤max max≤n))
    (b-zero n (NatOrder.≤-trans M≤max max≤n)) ∙
  add-zero-left 0ᶜ
  where
  N≤max : NatOrder._≤_ N (Nat.max N M)
  N≤max =
    NatOrder.left-≤-max {m = N} {n = M}

  M≤max : NatOrder._≤_ M (Nat.max N M)
  M≤max =
    NatOrder.right-≤-max {n = M} {m = N}


addPowerSeriesPolynomial :
  {a b : PowerSeries} →
  IsPolynomialPowerSeries a →
  IsPolynomialPowerSeries b →
  IsPolynomialPowerSeries (addPowerSeries a b)
addPowerSeriesPolynomial (N , a-zero) (M , b-zero) =
  Nat.max N M , addPowerSeriesZeroAfter N M a-zero b-zero


negPowerSeriesZeroAfter :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a N →
  PowerSeriesZeroAfter (negPowerSeries a) N
negPowerSeriesZeroAfter N zeroAfter n N≤n =
  cong -ᶜ_ (zeroAfter n N≤n) ∙
  neg-zeroᶜ


negPowerSeriesPolynomial :
  {a : PowerSeries} →
  IsPolynomialPowerSeries a →
  IsPolynomialPowerSeries (negPowerSeries a)
negPowerSeriesPolynomial (N , zeroAfter) =
  N , negPowerSeriesZeroAfter N zeroAfter


subPowerSeriesPolynomial :
  {a b : PowerSeries} →
  IsPolynomialPowerSeries a →
  IsPolynomialPowerSeries b →
  IsPolynomialPowerSeries (subPowerSeries a b)
subPowerSeriesPolynomial left right =
  addPowerSeriesPolynomial left (negPowerSeriesPolynomial right)


shiftPowerSeriesZeroAfter :
  {a : PowerSeries} →
  (N : ℕ) →
  PowerSeriesZeroAfter a (suc N) →
  PowerSeriesZeroAfter (shiftPowerSeries a) N
shiftPowerSeriesZeroAfter N zeroAfter n N≤n =
  zeroAfter (suc n) (NatOrder.suc-≤-suc N≤n)


cauchyProductPowerSeriesZeroLeft :
  {a b : PowerSeries} →
  PowerSeriesZeroAfter a zero →
  PowerSeriesZeroAfter (cauchyProductPowerSeries a b) zero
cauchyProductPowerSeriesZeroLeft {a = a} {b = b} zeroAfter zero _ =
  cong
    (λ c → c ·ᶜ b zero)
    (zeroAfter zero NatOrder.zero-≤) ∙
  mulᶜ-zero-left (b zero)
cauchyProductPowerSeriesZeroLeft {a = a} {b = b} zeroAfter (suc n) _ =
  cong₂
    _+ᶜ_
    (cong
      (λ c → c ·ᶜ b (suc n))
      (zeroAfter zero NatOrder.zero-≤) ∙
    mulᶜ-zero-left (b (suc n)))
    (cauchyProductPowerSeriesZeroLeft
      (λ k _ → zeroAfter (suc k) NatOrder.zero-≤)
      n
      NatOrder.zero-≤) ∙
  add-zero-left 0ᶜ


cauchyProductPowerSeriesZeroAfter :
  {a b : PowerSeries} →
  (N M : ℕ) →
  PowerSeriesZeroAfter a N →
  PowerSeriesZeroAfter b M →
  PowerSeriesZeroAfter (cauchyProductPowerSeries a b) (N Nat.+ M)
cauchyProductPowerSeriesZeroAfter zero M a-zero b-zero =
  powerSeriesZeroAfter-weaken
    NatOrder.zero-≤
    (cauchyProductPowerSeriesZeroLeft a-zero)
cauchyProductPowerSeriesZeroAfter (suc N) M a-zero b-zero zero sucNM≤0 =
  Empty.rec (NatOrder.¬-<-zero sucNM≤0)
cauchyProductPowerSeriesZeroAfter
  {a = a}
  {b = b}
  (suc N)
  M
  a-zero
  b-zero
  (suc n)
  sucNM≤sucn =
  cong₂
    _+ᶜ_
    (cong
      (λ c → a zero ·ᶜ c)
      (b-zero (suc n) M≤sucn) ∙
    mulᶜ-zero-right (a zero))
    (cauchyProductPowerSeriesZeroAfter
      N
      M
      (shiftPowerSeriesZeroAfter N a-zero)
      b-zero
      n
      (NatOrder.pred-≤-pred sucNM≤sucn)) ∙
  add-zero-left 0ᶜ
  where
  M≤sucNM : NatOrder._≤_ M (suc N Nat.+ M)
  M≤sucNM =
    NatOrder.≤SumRight {n = M} {k = suc N}

  M≤sucn : NatOrder._≤_ M (suc n)
  M≤sucn =
    NatOrder.≤-trans M≤sucNM sucNM≤sucn


cauchyProductPowerSeriesPolynomial :
  {a b : PowerSeries} →
  IsPolynomialPowerSeries a →
  IsPolynomialPowerSeries b →
  IsPolynomialPowerSeries (cauchyProductPowerSeries a b)
cauchyProductPowerSeriesPolynomial (N , a-zero) (M , b-zero) =
  N Nat.+ M , cauchyProductPowerSeriesZeroAfter N M a-zero b-zero


zeroPowerSeriesZeroAfter :
  PowerSeriesZeroAfter zeroPowerSeries zero
zeroPowerSeriesZeroAfter n _ =
  refl


zeroPowerSeriesPolynomial :
  IsPolynomialPowerSeries zeroPowerSeries
zeroPowerSeriesPolynomial =
  zero , zeroPowerSeriesZeroAfter


constantPowerSeriesZeroAfter :
  (c : ℝᶜ) →
  PowerSeriesZeroAfter (constantPowerSeries c) (suc zero)
constantPowerSeriesZeroAfter c zero 1≤0 =
  Empty.rec (NatOrder.¬-<-zero 1≤0)
constantPowerSeriesZeroAfter c (suc n) _ =
  refl


constantPowerSeriesPolynomial :
  (c : ℝᶜ) →
  IsPolynomialPowerSeries (constantPowerSeries c)
constantPowerSeriesPolynomial c =
  suc zero , constantPowerSeriesZeroAfter c
