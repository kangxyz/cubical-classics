{-

Convergence of finite outer approximations for re-centered sums.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Recenter.OuterConvergence where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
  using (-ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  using (BoundedByᶜ ; bounded-byᶜ ; upperᶜ ; lowerᶜ)
open import Constructive.Analysis.Reals.Series
  using
    ( partialSum
    ; seriesSumFromFiniteTailBoundConvergesTo
    ; TailBound
    ; tailSum
    ; tailSum-suc-start
    )
open import Constructive.Analysis.GeometricDecay
  using (positivePower)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Power
  using (realPower ; realPowerBoundsFromBound)
open import Constructive.Analysis.Reals.Sequences.Algebra as SeqAlg
  using (addConvergesTo ; mulLeftConvergesToWithBound ; negConvergesTo)
open import Constructive.Analysis.Reals.Sequences.Base
  using (Sequence)
open import Constructive.Analysis.Reals.Sequences.Convergence
  using (ConvergesTo ; constantConvergesTo)
open import Constructive.Analysis.Reals.Sequences.Order
  using (eventuallyUpperBoundClosed)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Coefficients
open import Constructive.Data.PositiveRationals
  using (ℚ⁺)


boundedByClosedFromConvergentApproximants :
  {u : Sequence} →
  {x : ℝᶜ} →
  (κ : ℚ⁺) →
  ConvergesTo u x →
  ((n : ℕ) → BoundedByᶜ κ (u n)) →
  BoundedByᶜ κ x
boundedByClosedFromConvergentApproximants {u = u} {x = x} κ u-converges u-bound =
  bounded-byᶜ upperBound lowerBound
  where
  upperBound :
    x ≤ᶜ rational (radius κ)
  upperBound =
    eventuallyUpperBoundClosed
      u-converges
      (λ _ n _ → upperᶜ (u-bound n))

  lowerBound :
    (-ᶜ x) ≤ᶜ rational (radius κ)
  lowerBound =
    eventuallyUpperBoundClosed
      (negConvergesTo u-converges)
      (λ _ n _ → lowerᶜ (u-bound n))


recenterOuterTailApprox :
  (a : PowerSeries) →
  (d h : ℝᶜ) →
  (m k N : ℕ) →
  ℝᶜ
recenterOuterTailApprox a d h m zero N =
  0ᶜ
recenterOuterTailApprox a d h m (suc k) N =
  partialSum (recenterCoefficientTerm a d m) N ·ᶜ
  realPower h m +ᶜ
  recenterOuterTailApprox a d h (suc m) k N


recenterOuterTailApproxConvergesToTail :
  {a : PowerSeries} →
  {d h : ℝᶜ} →
  {τ : ℚ⁺} →
  (recenterData : RecenterPowerSeriesData a d) →
  BoundedByᶜ τ h →
  (m k : ℕ) →
  ConvergesTo
    (λ N → recenterOuterTailApprox a d h m k N)
    (tailSum (powerSeriesTerm (recenterPowerSeriesWith a d recenterData) h) m k)
recenterOuterTailApproxConvergesToTail recenterData h-bound m zero =
  constantConvergesTo 0ᶜ
recenterOuterTailApproxConvergesToTail
    {a = a}
    {d = d}
    {h = h}
    {τ = τ}
    recenterData
    h-bound
    m
    (suc k) =
  subst
    (ConvergesTo
      (λ N → recenterOuterTailApprox a d h m (suc k) N))
    (sym tail-path)
    (addConvergesTo row-converges rest-converges)
  where
  coeffData : RecenterCoefficientConvergenceData a d m
  coeffData =
    coefficientData recenterData m

  hpow-bound : BoundedByᶜ (positivePower τ m) (realPower h m)
  hpow-bound =
    realPowerBoundsFromBound τ h h-bound m

  row-converges :
    ConvergesTo
      (λ N →
        partialSum (recenterCoefficientTerm a d m) N ·ᶜ
        realPower h m)
      (powerSeriesTerm (recenterPowerSeriesWith a d recenterData) h m)
  row-converges =
    mulLeftConvergesToWithBound
      (positivePower τ m)
      (realPower h m)
      hpow-bound
      (seriesSumFromFiniteTailBoundConvergesTo
        (recenterCoefficientTerm a d m)
        (modulus coeffData)
        (tailBound coeffData)
        (modulus-antitone coeffData))

  rest-converges :
    ConvergesTo
      (λ N → recenterOuterTailApprox a d h (suc m) k N)
      (tailSum
        (powerSeriesTerm (recenterPowerSeriesWith a d recenterData) h)
        (suc m)
        k)
  rest-converges =
    recenterOuterTailApproxConvergesToTail recenterData h-bound (suc m) k

  tail-path :
    tailSum
      (powerSeriesTerm (recenterPowerSeriesWith a d recenterData) h)
      m
      (suc k)
    ≡
    powerSeriesTerm (recenterPowerSeriesWith a d recenterData) h m +ᶜ
    tailSum
      (powerSeriesTerm (recenterPowerSeriesWith a d recenterData) h)
      (suc m)
      k
  tail-path =
    tailSum-suc-start
      (powerSeriesTerm (recenterPowerSeriesWith a d recenterData) h)
      m
      k


recenterTailBoundFromOuterApproxBounds :
  {a : PowerSeries} →
  {d h : ℝᶜ} →
  {τ : ℚ⁺} →
  {ν : ℚ⁺ → ℕ} →
  (recenterData : RecenterPowerSeriesData a d) →
  BoundedByᶜ τ h →
  ((ε : ℚ⁺) →
    (m k N : ℕ) →
    NatOrder._≤_ (ν ε) m →
    BoundedByᶜ ε (recenterOuterTailApprox a d h m k N)) →
  TailBound
    (powerSeriesTerm (recenterPowerSeriesWith a d recenterData) h)
    ν
recenterTailBoundFromOuterApproxBounds
    {a = a}
    {d = d}
    {h = h}
    recenterData
    h-bound
    approxBound
    ε
    m
    k
    ν≤m =
  boundedByClosedFromConvergentApproximants
    ε
    (recenterOuterTailApproxConvergesToTail
      recenterData
      h-bound
      m
      k)
    (λ N → approxBound ε m k N ν≤m)
