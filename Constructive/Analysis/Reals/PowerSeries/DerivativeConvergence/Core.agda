{-

Convergence transport for formal derivative coefficients

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.Core where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Tactics.CommRingSolver.Reflection

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
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
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
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
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
    ( AntitoneTailModulus
    ; SeriesMajorizedBy
    ; TailBound
    ; drop
    ; tailBound-drop
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Majorant
  using (bounded-byᶜ-abs)
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
  using
    ( positiveGeometricGap
    ; positiveGeometricPower-linear-bound
    ; positivePower
    ; positivePower-radius
    ; positiveRationalPower-nonnegative
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Rational
  using (rationalPower)
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower ; realPowerBoundsFromBound)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using
    ( PowerSeriesMajorizedOnBall
    ; hasPowerSeriesOnBallFromBoundedTerms
    ; hasPowerSeriesOnBallFromTermBounds
    ; hasPowerSeriesOnBallWithFromBoundedTerms
    ; hasPowerSeriesOnBallWithFromTermBounds
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.Internal


derivativePowerSeriesTermBoundPrecision :
  (ℕ → ℚ⁺) →
  ℚ⁺ →
  ℕ →
  ℚ⁺
derivativePowerSeriesTermBoundPrecision κ ρ n =
  scalar-bound (Rational.natMul (suc n) Rational.1ℚ) *⁺
    (κ (suc n) *⁺ positivePower ρ n)


DerivativePowerSeriesBoundMajorantOnBall :
  (ℕ → ℚ⁺) →
  ℚ⁺ →
  Type₀
DerivativePowerSeriesBoundMajorantOnBall κ ρ =
  Σ[ v ∈ (ℕ → ℝᶜ) ]
    Σ[ μ ∈ (ℚ⁺ → ℕ) ]
      Σ[ bound≤majorant ∈
          ((n : ℕ) →
            rational
              (radius (derivativePowerSeriesTermBoundPrecision κ ρ n)) ≤ᶜ
            v n) ]
        Σ[ majorantNonnegative ∈ ((n : ℕ) → 0ᶜ ≤ᶜ v n) ]
          Σ[ majorTail ∈ TailBound v μ ]
            AntitoneTailModulus μ


derivativePowerSeriesTermBoundsFromCoefficientBoundsWith :
  {a : PowerSeries} →
  (κ : ℕ → ℚ⁺) →
  (ρ : ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  (h : ℝᶜ) →
  BoundedByᶜ ρ h →
  (n : ℕ) →
  BoundedByᶜ
    (derivativePowerSeriesTermBoundPrecision κ ρ n)
    (powerSeriesTerm (derivativePowerSeries a) h n)
derivativePowerSeriesTermBoundsFromCoefficientBoundsWith
    {a = a}
    κ
    ρ
    coefficientBounds
    h
    h-bound
    n =
  subst
    (BoundedByᶜ (derivativePowerSeriesTermBoundPrecision κ ρ n))
    (sym (derivativePowerSeriesTerm a h n))
    (bounded-byᶜ-mul
      (scalar-bound natural)
      (κ (suc n) *⁺ positivePower ρ n)
      (naturalReal (suc n))
      (powerSeriesTerm (λ k → a (suc k)) h n)
      (naturalRealBound (suc n))
      (bounded-byᶜ-mul
        (κ (suc n))
        (positivePower ρ n)
        (a (suc n))
        (realPower h n)
        (coefficientBounds (suc n))
        (realPowerBoundsFromBound ρ h h-bound n)))
  where
  natural : ℚ
  natural =
    Rational.natMul (suc n) Rational.1ℚ


derivativePowerSeriesOnBallWithFromCoefficientBoundsAndMajorant :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  ((n : ℕ) →
    rational (radius (derivativePowerSeriesTermBoundPrecision κ ρ n)) ≤ᶜ
    v n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ v n) →
  TailBound v μ →
  AntitoneTailModulus μ →
  HasPowerSeriesOnBallWith (derivativePowerSeries a) ρ μ
derivativePowerSeriesOnBallWithFromCoefficientBoundsAndMajorant
    {a = a}
    {ρ = ρ}
    {v = v}
    {μ = μ}
    κ
    coefficientBounds
    bound≤majorant
    majorantNonnegative
    majorTail
    majorAntitone =
  hasPowerSeriesOnBallWithFromBoundedTerms
    {a = derivativePowerSeries a}
    {ρ = ρ}
    {κ = derivativePowerSeriesTermBoundPrecision κ ρ}
    {v = v}
    {μ = μ}
    (derivativePowerSeriesTermBoundsFromCoefficientBoundsWith
      κ
      ρ
      coefficientBounds)
    bound≤majorant
    majorantNonnegative
    majorTail
    majorAntitone


derivativePowerSeriesOnBallFromCoefficientBoundsAndMajorant :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {v : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  ((n : ℕ) →
    rational (radius (derivativePowerSeriesTermBoundPrecision κ ρ n)) ≤ᶜ
    v n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ v n) →
  TailBound v μ →
  AntitoneTailModulus μ →
  HasPowerSeriesOnBall (derivativePowerSeries a) ρ
derivativePowerSeriesOnBallFromCoefficientBoundsAndMajorant
    {a = a}
    {ρ = ρ}
    {v = v}
    {μ = μ}
    κ
    coefficientBounds
    bound≤majorant
    majorantNonnegative
    majorTail
    majorAntitone =
  hasPowerSeriesOnBallFromBoundedTerms
    {a = derivativePowerSeries a}
    {ρ = ρ}
    {κ = derivativePowerSeriesTermBoundPrecision κ ρ}
    {v = v}
    {μ = μ}
    (derivativePowerSeriesTermBoundsFromCoefficientBoundsWith
      κ
      ρ
      coefficientBounds)
    bound≤majorant
    majorantNonnegative
    majorTail
    majorAntitone


derivativePowerSeriesOnBallFromCoefficientBoundsAndBoundMajorant :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  DerivativePowerSeriesBoundMajorantOnBall κ ρ →
  HasPowerSeriesOnBall (derivativePowerSeries a) ρ
derivativePowerSeriesOnBallFromCoefficientBoundsAndBoundMajorant
    {a = a}
    {ρ = ρ}
    κ
    coefficientBounds
    (v , μ , bound≤majorant , majorantNonnegative , majorTail ,
      majorAntitone) =
  derivativePowerSeriesOnBallFromCoefficientBoundsAndMajorant
    {a = a}
    {ρ = ρ}
    {v = v}
    {μ = μ}
    κ
    coefficientBounds
    bound≤majorant
    majorantNonnegative
    majorTail
    majorAntitone
