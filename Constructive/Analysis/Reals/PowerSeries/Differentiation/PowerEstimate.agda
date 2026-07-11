{-

Termwise derivative criterion for power-series sums

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Differentiation.PowerEstimate where

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
open import Constructive.Analysis.Reals.Calculus.DerivativeData
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Structures
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base using (_≤ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.Series
  using
    ( partialSum
    ; partialSum-add
    ; seriesSumFromFiniteTailBoundConvergesAt
    )
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Power
  using (realPower ; realPowerBoundsFromBound)
open import Constructive.Analysis.GeometricDecay
  using (positivePower)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( addPowerSeries
    ; addPowerSeriesTerm
    ; powerSeriesPartialSum-add
    ; powerSeriesPartialSum-shift
    ; shiftPowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.FormalDerivative
  using
    ( derivativePowerSeries
    ; derivativePrimitivePowerSeries
    ; naturalReal
    ; primitivePowerSeries
    )
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open ClosenessOf RationalsMetricSpace


module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
  open CommRingStr (𝓡 .snd)

  linear-remainder-decomposition :
    (Fh Fx Ph Px d p' h : 𝓡 .fst) →
    (Fh + (- Fx)) + (- (d · h)) ≡
    ((((Fh + (- Ph)) + ((Ph + (- Px)) + (- (p' · h)))) +
      (Px + (- Fx))) +
      (- ((d + (- p')) · h)))
  linear-remainder-decomposition _ _ _ _ _ _ _ =
    solve! 𝓡

  linear-remainder-add :
    (Fh Fx Gh Gx df dg h : 𝓡 .fst) →
    (((Fh + Gh) + (- (Fx + Gx))) + (- ((df + dg) · h))) ≡
    (((Fh + (- Fx)) + (- (df · h))) +
      ((Gh + (- Gx)) + (- (dg · h))))
  linear-remainder-add _ _ _ _ _ _ _ =
    solve! 𝓡

  linear-remainder-neg :
    (Fh Fx d h : 𝓡 .fst) →
    ((- Fh) + (- (- Fx))) + (- ((- d) · h)) ≡
    - ((Fh + (- Fx)) + (- (d · h)))
  linear-remainder-neg _ _ _ _ =
    solve! 𝓡

  linear-remainder-rational-scale :
    (q Fh Fx d h : 𝓡 .fst) →
    ((q · Fh) + (- (q · Fx))) + (- ((q · d) · h)) ≡
    q · ((Fh + (- Fx)) + (- (d · h)))
  linear-remainder-rational-scale _ _ _ _ _ =
    solve! 𝓡

  linear-remainder-left-scale :
    (c Fh Fx d h : 𝓡 .fst) →
    ((c · Fh) + (- (c · Fx))) + (- ((c · d) · h)) ≡
    c · ((Fh + (- Fx)) + (- (d · h)))
  linear-remainder-left-scale _ _ _ _ _ =
    solve! 𝓡

  identity-product-remainder-decomposition :
    (x h fh fx d : 𝓡 .fst) →
    (((x + h) · fh) + (- (x · fx))) +
      (- ((fx + (x · d)) · h))
    ≡
    ((x + h) · ((fh + (- fx)) + (- (d · h)))) +
    ((d · h) · h)
  identity-product-remainder-decomposition _ _ _ _ _ =
    solve! 𝓡

  identity-linear-remainder-zero :
    (x h : 𝓡 .fst) →
    ((x + h) + (- x)) + (- (1r · h)) ≡ 0r
  identity-linear-remainder-zero _ _ =
    solve! 𝓡

  constant-linear-remainder-zero :
    (c h : 𝓡 .fst) →
    (c + (- c)) + (- (0r · h)) ≡ 0r
  constant-linear-remainder-zero _ _ =
    solve! 𝓡

  linear-partial-sum-remainder-zero :
    (a₀ a₁ x h : 𝓡 .fst) →
    ((a₀ + ((x + h) · a₁)) + (- (a₀ + (x · a₁)))) +
      (- (a₁ · h))
    ≡ 0r
  linear-partial-sum-remainder-zero _ _ _ _ =
    solve! 𝓡

summand-left≤sum :
  (ε δ : ℚ⁺) →
  radius ε ℚOrder.≤ radius (ε +⁺ δ)
summand-left≤sum ε δ =
  Rational.<→≤
    {p = radius ε}
    {q = radius (ε +⁺ δ)}
    (summand-left<sum ε δ)
