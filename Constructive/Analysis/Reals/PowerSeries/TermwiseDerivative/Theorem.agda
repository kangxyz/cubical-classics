{-

Part of Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Theorem where

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
open import Constructive.Analysis.Reals.Calculus.Derivative.Rules
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
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Core
  using
    ( HasPowerSeriesAtWith
    ; centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Consequences
  using (hasPowerSeriesAtWith→hasDerivativeAtWithFromEverywhereModel)
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using
    ( derivativePowerSeries
    ; derivativePrimitivePowerSeries
    ; naturalReal
    ; primitivePowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence
  using
    ( DerivativePowerSeriesBoundMajorantOnBall
    ; derivativePowerSeriesInfiniteRadius
    ; derivativePowerSeriesInfiniteRadiusFromCoefficientBoundsAndMajorants
    ; derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    ; derivativePrimitivePowerSeriesInfiniteRadius
    )
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open ClosenessOf RationalsMetricSpace

open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Internal
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Index
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Finite
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.PartialSums
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.IteratedBounds
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.UniformPartialSums
open import Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.ErrorBounds

powerSeriesTermwiseDerivativeAtWithFromPieceBounds :
  {f : ℝᶜ → ℝᶜ} →
  {a da : PowerSeries} →
  {x d : ℝᶜ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  ((ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (μ ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    linearRemainder f x d h ≡
    powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h) →
  PowerSeriesTermwiseForwardErrorBoundWith f a x χ μ →
  PowerSeriesPartialDerivativeRemainderBoundWith a da x χ μ →
  PowerSeriesTermwiseCenterErrorBoundWith f a x χ μ →
  PowerSeriesTermwiseDerivativeLinearErrorBoundWith da x d χ μ →
  PowerSeriesTermwiseDerivativeAtWith f a da x d χ μ
powerSeriesTermwiseDerivativeAtWithFromPieceBounds
  remainderDecomposition
  forwardBound
  partialBound
  centerBound
  derivativeLinearBound =
  remainderDecomposition ,
  powerSeriesTermwisePieceBounds→decomposedRemainderBound
    forwardBound
    partialBound
    centerBound
    derivativeLinearBound


powerSeriesTermwiseDerivativeAtWithFromCanonicalPieceBounds :
  {f : ℝᶜ → ℝᶜ} →
  {a da : PowerSeries} →
  {x d : ℝᶜ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  PowerSeriesTermwiseForwardErrorBoundWith f a x χ μ →
  PowerSeriesPartialDerivativeRemainderBoundWith a da x χ μ →
  PowerSeriesTermwiseCenterErrorBoundWith f a x χ μ →
  PowerSeriesTermwiseDerivativeLinearErrorBoundWith da x d χ μ →
  PowerSeriesTermwiseDerivativeAtWith f a da x d χ μ
powerSeriesTermwiseDerivativeAtWithFromCanonicalPieceBounds
  {f = f}
  {a = a}
  {da = da}
  {x = x}
  {d = d}
  {χ = χ}
  forwardBound
  partialBound
  centerBound
  derivativeLinearBound =
  powerSeriesTermwiseDerivativeAtWithFromPieceBounds
    (λ ε η _ h _ →
      powerSeriesTermwiseRemainderDecomposition f a da x d χ ε η h)
    forwardBound
    partialBound
    centerBound
    derivativeLinearBound


powerSeriesTermwiseDerivativeAtWithFromCanonicalValueBounds :
  {f : ℝᶜ → ℝᶜ} →
  {a da : PowerSeries} →
  {x d : ℝᶜ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  PowerSeriesTermwiseForwardErrorBoundWith f a x χ μ →
  PowerSeriesPartialDerivativeRemainderBoundWith a da x χ μ →
  PowerSeriesTermwiseCenterErrorBoundWith f a x χ μ →
  PowerSeriesTermwiseDerivativeValueErrorBoundWith da x d χ μ →
  PowerSeriesTermwiseDerivativeAtWith f a da x d χ μ
powerSeriesTermwiseDerivativeAtWithFromCanonicalValueBounds
  forwardBound
  partialBound
  centerBound
  derivativeValueBound =
  powerSeriesTermwiseDerivativeAtWithFromCanonicalPieceBounds
    forwardBound
    partialBound
    centerBound
    (derivativeValueErrorBound→linearErrorBound derivativeValueBound)


powerSeriesTermwiseDerivativeAtWith→hasDerivativeAtWith :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {da : PowerSeries} →
  {x d : ℝᶜ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  PowerSeriesTermwiseDerivativeAtWith f a da x d χ μ →
  HasDerivativeAtWith f x d μ
powerSeriesTermwiseDerivativeAtWith→hasDerivativeAtWith
  {f = f}
  {a = a}
  {x = x}
  {d = d}
  {χ = χ}
  derivativeData
  ε
  η
  η≤με
  h
  h-bound =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (sym
      (PowerSeriesTermwiseDerivativeAtWith.remainderDecomposition
        derivativeData
        ε
        η
        η≤με
        h
        h-bound))
    (PowerSeriesTermwiseDerivativeAtWith.decomposedRemainderBound
      derivativeData
      ε
      η
      η≤με
      h
      h-bound)



hasDerivativeAtWith-derivative-path :
  {f : ℝᶜ → ℝᶜ} →
  {x d e : ℝᶜ} →
  {μ : PrecisionModulus} →
  d ≡ e →
  HasDerivativeAtWith f x d μ →
  HasDerivativeAtWith f x e μ
hasDerivativeAtWith-derivative-path {f = f} {x = x} {μ = μ} d≡e =
  subst (λ D → HasDerivativeAtWith f x D μ) d≡e


linearRemainder-center-translate :
  (f : ℝᶜ → ℝᶜ) →
  (c x d h : ℝᶜ) →
  linearRemainder
    (λ y → f (c +ᶜ y))
    (centeredDisplacement c x)
    d
    h
  ≡
  linearRemainder f x d h
linearRemainder-center-translate f c x d h =
  cong₂
    (λ forward base →
      (f forward +ᶜ (-ᶜ f base)) +ᶜ (-ᶜ (d ·ᶜ h)))
    (add-center-centeredDisplacement-forward c x h)
    (add-center-centeredDisplacement c x)


hasDerivativeAtWith-center-translate :
  {f : ℝᶜ → ℝᶜ} →
  {c x d : ℝᶜ} →
  {μ : PrecisionModulus} →
  HasDerivativeAtWith
    (λ y → f (c +ᶜ y))
    (centeredDisplacement c x)
    d
    μ →
  HasDerivativeAtWith f x d μ
hasDerivativeAtWith-center-translate
  {f = f}
  {c = c}
  {x = x}
  {d = d}
  derivative
  ε
  η
  η≤με
  h
  h-bound =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (linearRemainder-center-translate f c x d h)
    (derivative ε η η≤με h h-bound)


centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndPartialDerivativeRemainderOnSubballCanonicalIndex→hasDerivativeAtWith :
  {a b : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  (coeff≡ : (n : ℕ) → derivativePowerSeries a n ≡ b n) →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (derivativeRadius :
    HasInfinitePowerSeriesRadius (derivativePowerSeries a)) →
  (targetRadius : HasInfinitePowerSeriesRadius b) →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  PowerSeriesPartialDerivativeRemainderBoundWith
    a
    (derivativePowerSeries a)
    (centeredDisplacement c x)
    (termwiseConvergenceIndex
      (radiusData ρ .fst)
      (derivativeRadius σ .fst))
    μ →
  HasDerivativeAtWith
    (centeredPowerSeriesSumEverywhere a c radiusData)
    x
    (centeredPowerSeriesSumEverywhere b c targetRadius x)
    μ
centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndPartialDerivativeRemainderOnSubballCanonicalIndex→hasDerivativeAtWith
  {a = a}
  {b = b}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  coeff≡
  radiusData
  derivativeRadius
  targetRadius
  x-displacement-bound
  margin
  partialBound =
  hasDerivativeAtWith-derivative-path
    derivativeValuePath
    (hasDerivativeAtWith-center-translate translatedDerivative)
  where
  ν : ℚ⁺ → ℕ
  ν =
    radiusData ρ .fst

  convergence : HasPowerSeriesOnBallWith a ρ ν
  convergence =
    radiusData ρ .snd

  τ : ℚ⁺ → ℕ
  τ =
    derivativeRadius σ .fst

  derivativeConvergence :
    HasPowerSeriesOnBallWith (derivativePowerSeries a) σ τ
  derivativeConvergence =
    derivativeRadius σ .snd

  χ : TermwiseDerivativeIndex
  χ =
    termwiseConvergenceIndex ν τ

  z : ℝᶜ
  z =
    centeredDisplacement c x

  translatedSum : ℝᶜ → ℝᶜ
  translatedSum y =
    centeredPowerSeriesSumEverywhere a c radiusData (c +ᶜ y)

  derivativeLocalValue : ℝᶜ
  derivativeLocalValue =
    centeredPowerSeriesSumOnBall
      (derivativePowerSeries a)
      0ᶜ
      σ
      τ
      derivativeConvergence
      z
      (inPowerSeriesBallAtZeroFromBound x-displacement-bound)

  forwardInBall :
    (ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (μ ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    BoundedByᶜ ρ (z +ᶜ h)
  forwardInBall =
    powerSeriesForwardInBallFromCenterMargin x-displacement-bound margin

  centerBound : BoundedByᶜ ρ z
  centerBound =
    powerSeriesCenterInBallFromMargin x-displacement-bound margin

  forwardExpansion :
    (ε η : ℚ⁺) →
    (η≤με : radius η ℚOrder.≤ radius (μ ε)) →
    (h : ℝᶜ) →
    (h-bound : BoundedByᶜ η h) →
    translatedSum (z +ᶜ h) ≡
    powerSeriesSumOnBall
      a
      ρ
      ν
      convergence
      (z +ᶜ h)
      (forwardInBall ε η η≤με h h-bound)
  forwardExpansion ε η η≤με h h-bound =
    centeredPowerSeriesSumEverywhere-bound-path
      a
      c
      radiusData
      ρ
      (c +ᶜ (z +ᶜ h))
      (inPowerSeriesBallAtCenterPlusFromBound c y-bound) ∙
    centeredPowerSeriesSumOnBallAtCenterPlus-path
      convergence
      c
      (z +ᶜ h)
      y-bound
    where
    y-bound : BoundedByᶜ ρ (z +ᶜ h)
    y-bound =
      forwardInBall ε η η≤με h h-bound

  centerExpansion :
    translatedSum z ≡
    powerSeriesSumOnBall a ρ ν convergence z centerBound
  centerExpansion =
    centeredPowerSeriesSumEverywhere-bound-path
      a
      c
      radiusData
      ρ
      (c +ᶜ z)
      (inPowerSeriesBallAtCenterPlusFromBound c centerBound) ∙
    centeredPowerSeriesSumOnBallAtCenterPlus-path
      convergence
      c
      z
      centerBound

  forwardBound :
    PowerSeriesTermwiseForwardErrorBoundWith
      translatedSum
      a
      z
      χ
      μ
  forwardBound =
    powerSeriesTermwiseForwardErrorBoundFromConvergence
      convergence
      forwardInBall
      forwardExpansion
      (termwiseConvergenceIndex-sumLarge {ν = ν} {τ = τ})

  centerErrorBound :
    PowerSeriesTermwiseCenterErrorBoundWith
      translatedSum
      a
      z
      χ
      μ
  centerErrorBound =
    powerSeriesTermwiseCenterErrorBoundFromConvergence
      convergence
      centerBound
      centerExpansion
      (termwiseConvergenceIndex-sumLarge {ν = ν} {τ = τ})

  derivativeValueAtZeroPath :
    derivativeLocalValue ≡
    powerSeriesSumOnBall
      (derivativePowerSeries a)
      σ
      τ
      derivativeConvergence
      z
      x-displacement-bound
  derivativeValueAtZeroPath =
    centeredPowerSeriesSumOnBallAtZero-path
      derivativeConvergence
      z
      x-displacement-bound

  derivativeValueBound :
    PowerSeriesFormalDerivativeValueErrorBoundWith a z derivativeLocalValue χ μ
  derivativeValueBound =
    powerSeriesFormalDerivativeValueErrorBoundFromConvergence
      derivativeConvergence
      x-displacement-bound
      derivativeValueAtZeroPath
      (termwiseConvergenceIndex-derivativeValueLarge {ν = ν} {τ = τ})

  translatedDerivative :
    HasDerivativeAtWith
      translatedSum
      z
      derivativeLocalValue
      μ
  translatedDerivative =
    powerSeriesTermwiseDerivativeAtWith→hasDerivativeAtWith
      (powerSeriesTermwiseDerivativeAtWithFromCanonicalValueBounds
        forwardBound
        partialBound
        centerErrorBound
        derivativeValueBound)

  derivativeValuePath :
    derivativeLocalValue ≡
    centeredPowerSeriesSumEverywhere b c targetRadius x
  derivativeValuePath =
    centeredPowerSeriesSumOnBallAtZero-path
      derivativeConvergence
      z
      x-displacement-bound ∙
    sym
      (centeredPowerSeriesSumEverywhere-bound-path
        (derivativePowerSeries a)
        c
        derivativeRadius
        σ
        x
        (record { displacementBound = x-displacement-bound })) ∙
    centeredPowerSeriesSumEverywhere-coefficients-path
      coeff≡
      derivativeRadius
      targetRadius
      c
      x


centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith :
  {a b : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  {δ : ℕ → ℕ → ℚ⁺} →
  (coeff≡ : (n : ℕ) → derivativePowerSeries a n ≡ b n) →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (derivativeRadius :
    HasInfinitePowerSeriesRadius (derivativePowerSeries a)) →
  (targetRadius : HasInfinitePowerSeriesRadius b) →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    a
    (centeredDisplacement c x)
    δ →
  PowerSeriesPartialSumsDerivativeModulusLarge
    (termwiseConvergenceIndex
      (radiusData ρ .fst)
      (derivativeRadius σ .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus σ δ) →
  HasDerivativeAtWith
    (centeredPowerSeriesSumEverywhere a c radiusData)
    x
    (centeredPowerSeriesSumEverywhere b c targetRadius x)
    μ
centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
  {a = a}
  {b = b}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {δ = δ}
  coeff≡
  radiusData
  derivativeRadius
  targetRadius
  x-displacement-bound
  margin
  derivative-bounds
  partialModulus-large =
  centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndPartialDerivativeRemainderOnSubballCanonicalIndex→hasDerivativeAtWith
    {a = a}
    {b = b}
    {c = c}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ = μ}
    coeff≡
    radiusData
    derivativeRadius
    targetRadius
    x-displacement-bound
    margin
    (powerSeriesFormalPartialDerivativeRemainderBoundFromIteratedBounds
      σ
      x-displacement-bound
      derivative-bounds
      partialModulus-large)


centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndTargetRadiusAndIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith :
  {a b : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  {δ : ℕ → ℕ → ℚ⁺} →
  (coeff≡ : (n : ℕ) → derivativePowerSeries a n ≡ b n) →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (targetRadius : HasInfinitePowerSeriesRadius b) →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    a
    (centeredDisplacement c x)
    δ →
  PowerSeriesPartialSumsDerivativeModulusLarge
    (termwiseConvergenceIndex
      (radiusData ρ .fst)
      (derivativePowerSeriesInfiniteRadiusFromCoefficientPath
        {a = a}
        {b = b}
        coeff≡
        targetRadius
        σ
        .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus σ δ) →
  HasDerivativeAtWith
    (centeredPowerSeriesSumEverywhere a c radiusData)
    x
    (centeredPowerSeriesSumEverywhere b c targetRadius x)
    μ
centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndTargetRadiusAndIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
  {a = a}
  {b = b}
  coeff≡
  radiusData
  targetRadius =
  centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
    {a = a}
    {b = b}
    coeff≡
    radiusData
    (derivativePowerSeriesInfiniteRadiusFromCoefficientPath
      {a = a}
      {b = b}
      coeff≡
      targetRadius)
    targetRadius


centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndTargetRadiusAndCoefficientBoundsOnSubballCanonicalIndex→hasDerivativeAtWith :
  {a b : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  (coeff≡ : (n : ℕ) → derivativePowerSeries a n ≡ b n) →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (targetRadius : HasInfinitePowerSeriesRadius b) →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  PowerSeriesPartialSumsDerivativeModulusLarge
    (termwiseConvergenceIndex
      (radiusData ρ .fst)
      (derivativePowerSeriesInfiniteRadiusFromCoefficientPath
        {a = a}
        {b = b}
        coeff≡
        targetRadius
        σ
        .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus
      σ
      (powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds
        σ
        κ)) →
  HasDerivativeAtWith
    (centeredPowerSeriesSumEverywhere a c radiusData)
    x
    (centeredPowerSeriesSumEverywhere b c targetRadius x)
    μ
centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndTargetRadiusAndCoefficientBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
  {a = a}
  {b = b}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  coeff≡
  radiusData
  targetRadius
  x-displacement-bound
  margin
  κ
  coefficientBounds
  partialModulus-large =
  centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndTargetRadiusAndIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
    {a = a}
    {b = b}
    {c = c}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ = μ}
    {δ = powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds σ κ}
    coeff≡
    radiusData
    targetRadius
    x-displacement-bound
    margin
    (powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
      σ
      x-displacement-bound
      κ
      coefficientBounds)
    partialModulus-large


centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith :
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  {δ : ℕ → ℕ → ℚ⁺} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (derivativeRadius :
    HasInfinitePowerSeriesRadius (derivativePowerSeries a)) →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    a
    (centeredDisplacement c x)
    δ →
  PowerSeriesPartialSumsDerivativeModulusLarge
    (termwiseConvergenceIndex
      (radiusData ρ .fst)
      (derivativeRadius σ .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus σ δ) →
  HasDerivativeAtWith
    (centeredPowerSeriesSumEverywhere a c radiusData)
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      derivativeRadius
      x)
    μ
centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
  {a = a}
  radiusData
  derivativeRadius =
  centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
    {a = a}
    {b = derivativePowerSeries a}
    (λ _ → refl)
    radiusData
    derivativeRadius
    derivativeRadius


centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromIteratedBoundsOnSubballUniformModulus→hasDerivativeAtWith :
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  {δ : ℕ → ℕ → ℚ⁺} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    a
    (centeredDisplacement c x)
    δ →
  PowerSeriesPartialSumsDerivativeUniformModulus
    (termwiseConvergenceIndex
      (radiusData ρ .fst)
      (derivativePowerSeriesInfiniteRadius radiusData σ .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus σ δ) →
  HasDerivativeAtWith
    (centeredPowerSeriesSumEverywhere a c radiusData)
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      (derivativePowerSeriesInfiniteRadius radiusData)
      x)
    μ
centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromIteratedBoundsOnSubballUniformModulus→hasDerivativeAtWith
  {a = a}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {δ = δ}
  radiusData
  x-displacement-bound
  margin
  derivative-bounds
  uniformModulus =
  centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
    {a = a}
    {c = c}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ = μ}
    {δ = δ}
    radiusData
    derivativeRadius
    x-displacement-bound
    margin
    derivative-bounds
    (powerSeriesPartialSumsDerivativeModulusLargeFromUniformModulus
      {χ =
        termwiseConvergenceIndex
          (radiusData ρ .fst)
          (derivativeRadius σ .fst)}
      {μ = μ}
      {ω = powerSeriesFormalPartialSumsDerivativeModulus σ δ}
      uniformModulus)
  where
  derivativeRadius : HasInfinitePowerSeriesRadius (derivativePowerSeries a)
  derivativeRadius =
    derivativePowerSeriesInfiniteRadius radiusData


centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromIteratedBoundsOnSubballUniformSubmodulus→hasDerivativeAtWith :
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ ν : PrecisionModulus} →
  {δ : ℕ → ℕ → ℚ⁺} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin :
    (ε : ℚ⁺) →
    radius (σ +⁺ min⁺ (μ ε) (ν ε)) ℚOrder.≤ radius ρ) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    a
    (centeredDisplacement c x)
    δ →
  PowerSeriesPartialSumsDerivativeUniformModulus
    (termwiseConvergenceIndex
      (radiusData ρ .fst)
      (derivativePowerSeriesInfiniteRadius radiusData σ .fst))
    ν
    (powerSeriesFormalPartialSumsDerivativeModulus σ δ) →
  HasDerivativeAtWith
    (centeredPowerSeriesSumEverywhere a c radiusData)
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      (derivativePowerSeriesInfiniteRadius radiusData)
      x)
    (λ ε → min⁺ (μ ε) (ν ε))
centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromIteratedBoundsOnSubballUniformSubmodulus→hasDerivativeAtWith
  {a = a}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {ν = ν}
  {δ = δ}
  radiusData
  x-displacement-bound
  margin
  derivative-bounds
  uniformModulus =
  centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
    {a = a}
    {c = c}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ = λ ε → min⁺ (μ ε) (ν ε)}
    {δ = δ}
    radiusData
    derivativeRadius
    x-displacement-bound
    margin
    derivative-bounds
    (powerSeriesPartialSumsDerivativeModulusLargeFromUniformSubmodulus
      {χ =
        termwiseConvergenceIndex
          (radiusData ρ .fst)
          (derivativeRadius σ .fst)}
      μ
      ν
      {ω = powerSeriesFormalPartialSumsDerivativeModulus σ δ}
      uniformModulus)
  where
  derivativeRadius : HasInfinitePowerSeriesRadius (derivativePowerSeries a)
  derivativeRadius =
    derivativePowerSeriesInfiniteRadius radiusData


centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromUniformPartialSumsOnSubballCanonicalIndex→hasDerivativeAtWith :
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin :
    (ε : ℚ⁺) →
    radius (σ +⁺ partialSumsDerivativeTargetModulus μ ε)
      ℚOrder.≤ radius ρ) →
  PowerSeriesFormalPartialSumsHaveDerivativeWith
    a
    (centeredDisplacement c x)
    (λ _ → μ) →
  HasDerivativeAtWith
    (centeredPowerSeriesSumEverywhere a c radiusData)
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      (derivativePowerSeriesInfiniteRadius radiusData)
      x)
    (partialSumsDerivativeTargetModulus μ)
centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromUniformPartialSumsOnSubballCanonicalIndex→hasDerivativeAtWith
  {a = a}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  radiusData
  x-displacement-bound
  margin
  partialDerivative =
  centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndPartialDerivativeRemainderOnSubballCanonicalIndex→hasDerivativeAtWith
    {a = a}
    {b = derivativePowerSeries a}
    {c = c}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ = partialSumsDerivativeTargetModulus μ}
    (λ _ → refl)
    radiusData
    derivativeRadius
    derivativeRadius
    x-displacement-bound
    margin
    (powerSeriesFormalPartialDerivativeRemainderBoundFromUniformPartialSumsDerivative
      {a = a}
      {x = centeredDisplacement c x}
      {χ =
        termwiseConvergenceIndex
          (radiusData ρ .fst)
          (derivativeRadius σ .fst)}
      {μ = μ}
      partialDerivative)
  where
  derivativeRadius : HasInfinitePowerSeriesRadius (derivativePowerSeries a)
  derivativeRadius =
    derivativePowerSeriesInfiniteRadius radiusData


centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromSecondDerivativePartialSumsBoundOnSubballCanonicalIndex→hasDerivativeAtWith :
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ Γ : ℚ⁺} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin :
    (ε : ℚ⁺) →
    radius
      (σ +⁺
        partialSumsDerivativeTargetModulus
          (powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound Γ)
          ε)
      ℚOrder.≤ radius ρ) →
  PowerSeriesSecondDerivativePartialSumsBoundOnBallWith
    a
    (σ +⁺ 1⁺)
    Γ →
  HasDerivativeAtWith
    (centeredPowerSeriesSumEverywhere a c radiusData)
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      (derivativePowerSeriesInfiniteRadius radiusData)
      x)
    (partialSumsDerivativeTargetModulus
      (powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound Γ))
centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromSecondDerivativePartialSumsBoundOnSubballCanonicalIndex→hasDerivativeAtWith
  {a = a}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {Γ = Γ}
  radiusData
  x-displacement-bound
  margin
  secondDerivativeBound =
  centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromUniformPartialSumsOnSubballCanonicalIndex→hasDerivativeAtWith
    {a = a}
    {c = c}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ = powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound Γ}
    radiusData
    x-displacement-bound
    margin
    (powerSeriesFormalPartialSumsHaveDerivativeWithFromSecondDerivativeBound
      σ
      Γ
      x-displacement-bound
      secondDerivativeBound)


centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientBoundsOnSubballCanonicalIndex→hasDerivativeAtWith :
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (derivativeRadius :
    HasInfinitePowerSeriesRadius (derivativePowerSeries a)) →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  PowerSeriesPartialSumsDerivativeModulusLarge
    (termwiseConvergenceIndex
      (radiusData ρ .fst)
      (derivativeRadius σ .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus
      σ
      (powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds
        σ
        κ)) →
  HasDerivativeAtWith
    (centeredPowerSeriesSumEverywhere a c radiusData)
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      derivativeRadius
      x)
    μ
centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
  {a = a}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  radiusData
  derivativeRadius
  x-displacement-bound
  margin
  κ
  coefficientBounds
  partialModulus-large =
  centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
    {a = a}
    {c = c}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ = μ}
    {δ = powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds σ κ}
    radiusData
    derivativeRadius
    x-displacement-bound
    margin
    (powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
      σ
      x-displacement-bound
      κ
      coefficientBounds)
    partialModulus-large


centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientBoundsOnSubballUniformModulus→hasDerivativeAtWith :
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  PowerSeriesPartialSumsDerivativeUniformModulus
    (termwiseConvergenceIndex
      (radiusData ρ .fst)
      (derivativePowerSeriesInfiniteRadius radiusData σ .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus
      σ
      (powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds
        σ
        κ)) →
  HasDerivativeAtWith
    (centeredPowerSeriesSumEverywhere a c radiusData)
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      (derivativePowerSeriesInfiniteRadius radiusData)
      x)
    μ
centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientBoundsOnSubballUniformModulus→hasDerivativeAtWith
  {a = a}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  radiusData
  x-displacement-bound
  margin
  κ
  coefficientBounds
  uniformModulus =
  centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromIteratedBoundsOnSubballUniformModulus→hasDerivativeAtWith
    {a = a}
    {c = c}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ = μ}
    {δ = powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds σ κ}
    radiusData
    x-displacement-bound
    margin
    (powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
      σ
      x-displacement-bound
      κ
      coefficientBounds)
    uniformModulus


centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientBoundsOnSubballUniformSubmodulus→hasDerivativeAtWith :
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ ν : PrecisionModulus} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin :
    (ε : ℚ⁺) →
    radius (σ +⁺ min⁺ (μ ε) (ν ε)) ℚOrder.≤ radius ρ) →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  PowerSeriesPartialSumsDerivativeUniformModulus
    (termwiseConvergenceIndex
      (radiusData ρ .fst)
      (derivativePowerSeriesInfiniteRadius radiusData σ .fst))
    ν
    (powerSeriesFormalPartialSumsDerivativeModulus
      σ
      (powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds
        σ
        κ)) →
  HasDerivativeAtWith
    (centeredPowerSeriesSumEverywhere a c radiusData)
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      (derivativePowerSeriesInfiniteRadius radiusData)
      x)
    (λ ε → min⁺ (μ ε) (ν ε))
centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientBoundsOnSubballUniformSubmodulus→hasDerivativeAtWith
  {a = a}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {ν = ν}
  radiusData
  x-displacement-bound
  margin
  κ
  coefficientBounds
  uniformModulus =
  centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromIteratedBoundsOnSubballUniformSubmodulus→hasDerivativeAtWith
    {a = a}
    {c = c}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ = μ}
    {ν = ν}
    {δ = powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds σ κ}
    radiusData
    x-displacement-bound
    margin
    (powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
      σ
      x-displacement-bound
      κ
      coefficientBounds)
    uniformModulus


centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientBoundsAndDerivativeMajorantsOnSubballCanonicalIndex→hasDerivativeAtWith :
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  (κ : ℕ → ℚ⁺) →
  (coefficientBounds : (n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  (derivativeMajorants :
    (τ : ℚ⁺) → DerivativePowerSeriesBoundMajorantOnBall κ τ) →
  PowerSeriesPartialSumsDerivativeModulusLarge
    (termwiseConvergenceIndex
      (radiusData ρ .fst)
      (derivativePowerSeriesInfiniteRadiusFromCoefficientBoundsAndMajorants
        {a = a}
        κ
        coefficientBounds
        derivativeMajorants
        σ
        .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus
      σ
      (powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds
        σ
        κ)) →
  HasDerivativeAtWith
    (centeredPowerSeriesSumEverywhere a c radiusData)
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      (derivativePowerSeriesInfiniteRadiusFromCoefficientBoundsAndMajorants
        {a = a}
        κ
        coefficientBounds
        derivativeMajorants)
      x)
    μ
centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientBoundsAndDerivativeMajorantsOnSubballCanonicalIndex→hasDerivativeAtWith
  {a = a}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  radiusData
  x-displacement-bound
  margin
  κ
  coefficientBounds
  derivativeMajorants
  partialModulus-large =
  centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
    {a = a}
    {c = c}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ = μ}
    radiusData
    derivativeRadius
    x-displacement-bound
    margin
    κ
    coefficientBounds
    partialModulus-large
  where
  derivativeRadius : HasInfinitePowerSeriesRadius (derivativePowerSeries a)
  derivativeRadius =
    derivativePowerSeriesInfiniteRadiusFromCoefficientBoundsAndMajorants
      {a = a}
      κ
      coefficientBounds
      derivativeMajorants


hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientPathAndTargetRadiusAndIteratedBoundsOnSubballCanonicalIndex :
  {f : ℝᶜ → ℝᶜ} →
  {a b : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {seriesModulus : ℚ⁺ → ℕ} →
  {μ : PrecisionModulus} →
  {δ : ℕ → ℕ → ℚ⁺} →
  (coeff≡ : (n : ℕ) → derivativePowerSeries a n ≡ b n) →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (targetRadius : HasInfinitePowerSeriesRadius b) →
  HasPowerSeriesAtWith f c a ρ seriesModulus →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    a
    (centeredDisplacement c x)
    δ →
  PowerSeriesPartialSumsDerivativeModulusLarge
    (termwiseConvergenceIndex
      (radiusData ρ .fst)
      (derivativePowerSeriesInfiniteRadiusFromCoefficientPath
        {a = a}
        {b = b}
        coeff≡
        targetRadius
        σ
        .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus σ δ) →
  HasDerivativeAtWith f x (centeredPowerSeriesSumEverywhere b c targetRadius x) μ
hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientPathAndTargetRadiusAndIteratedBoundsOnSubballCanonicalIndex
  {a = a}
  {b = b}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {δ = δ}
  coeff≡
  radiusData
  targetRadius
  expansion
  x-displacement-bound
  margin
  derivative-bounds
  partialModulus-large =
  hasPowerSeriesAtWith→hasDerivativeAtWithFromEverywhereModel
    radiusData
    expansion
    x-inBall
    forward-inBall
    (centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndTargetRadiusAndIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
      {a = a}
      {b = b}
      {c = c}
      {x = x}
      {ρ = ρ}
      {σ = σ}
      {μ = μ}
      {δ = δ}
      coeff≡
      radiusData
      targetRadius
      x-displacement-bound
      margin
      derivative-bounds
      partialModulus-large)
  where
  x-inBall : InPowerSeriesBall c ρ x
  x-inBall =
    record
      { displacementBound =
          powerSeriesCenterInBallFromMargin x-displacement-bound margin
      }

  forward-inBall :
    (ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (μ ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    InPowerSeriesBall c ρ (x +ᶜ h)
  forward-inBall ε η η≤με h h-bound =
    subst
      (InPowerSeriesBall c ρ)
      (add-center-centeredDisplacement-forward c x h)
      (inPowerSeriesBallAtCenterPlusFromBound
        c
        (powerSeriesForwardInBallFromCenterMargin
          x-displacement-bound
          margin
          ε
          η
          η≤με
          h
          h-bound))


hasPowerSeriesAtWith→hasDerivativeAtWithFromIteratedBoundsOnSubballUniformModulus :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {seriesModulus : ℚ⁺ → ℕ} →
  {μ : PrecisionModulus} →
  {δ : ℕ → ℕ → ℚ⁺} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  HasPowerSeriesAtWith f c a ρ seriesModulus →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    a
    (centeredDisplacement c x)
    δ →
  PowerSeriesPartialSumsDerivativeUniformModulus
    (termwiseConvergenceIndex
      (radiusData ρ .fst)
      (derivativePowerSeriesInfiniteRadius radiusData σ .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus σ δ) →
  HasDerivativeAtWith
    f
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      (derivativePowerSeriesInfiniteRadius radiusData)
      x)
    μ
hasPowerSeriesAtWith→hasDerivativeAtWithFromIteratedBoundsOnSubballUniformModulus
  {a = a}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {δ = δ}
  radiusData
  expansion
  x-displacement-bound
  margin
  derivative-bounds
  uniformModulus =
  hasPowerSeriesAtWith→hasDerivativeAtWithFromEverywhereModel
    radiusData
    expansion
    x-inBall
    forward-inBall
    (centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromIteratedBoundsOnSubballUniformModulus→hasDerivativeAtWith
      {a = a}
      {c = c}
      {x = x}
      {ρ = ρ}
      {σ = σ}
      {μ = μ}
      {δ = δ}
      radiusData
      x-displacement-bound
      margin
      derivative-bounds
      uniformModulus)
  where
  x-inBall : InPowerSeriesBall c ρ x
  x-inBall =
    record
      { displacementBound =
          powerSeriesCenterInBallFromMargin x-displacement-bound margin
      }

  forward-inBall :
    (ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (μ ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    InPowerSeriesBall c ρ (x +ᶜ h)
  forward-inBall ε η η≤με h h-bound =
    subst
      (InPowerSeriesBall c ρ)
      (add-center-centeredDisplacement-forward c x h)
      (inPowerSeriesBallAtCenterPlusFromBound
        c
        (powerSeriesForwardInBallFromCenterMargin
          x-displacement-bound
          margin
          ε
          η
          η≤με
          h
          h-bound))


hasPowerSeriesAtWith→hasDerivativeAtWithFromIteratedBoundsOnSubballUniformSubmodulus :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {seriesModulus : ℚ⁺ → ℕ} →
  {μ ν : PrecisionModulus} →
  {δ : ℕ → ℕ → ℚ⁺} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  HasPowerSeriesAtWith f c a ρ seriesModulus →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin :
    (ε : ℚ⁺) →
    radius (σ +⁺ min⁺ (μ ε) (ν ε)) ℚOrder.≤ radius ρ) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    a
    (centeredDisplacement c x)
    δ →
  PowerSeriesPartialSumsDerivativeUniformModulus
    (termwiseConvergenceIndex
      (radiusData ρ .fst)
      (derivativePowerSeriesInfiniteRadius radiusData σ .fst))
    ν
    (powerSeriesFormalPartialSumsDerivativeModulus σ δ) →
  HasDerivativeAtWith
    f
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      (derivativePowerSeriesInfiniteRadius radiusData)
      x)
    (λ ε → min⁺ (μ ε) (ν ε))
hasPowerSeriesAtWith→hasDerivativeAtWithFromIteratedBoundsOnSubballUniformSubmodulus
  {a = a}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {ν = ν}
  {δ = δ}
  radiusData
  expansion
  x-displacement-bound
  margin
  derivative-bounds
  uniformModulus =
  hasPowerSeriesAtWith→hasDerivativeAtWithFromEverywhereModel
    radiusData
    expansion
    x-inBall
    forward-inBall
    (centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromIteratedBoundsOnSubballUniformSubmodulus→hasDerivativeAtWith
      {a = a}
      {c = c}
      {x = x}
      {ρ = ρ}
      {σ = σ}
      {μ = μ}
      {ν = ν}
      {δ = δ}
      radiusData
      x-displacement-bound
      margin
      derivative-bounds
      uniformModulus)
  where
  x-inBall : InPowerSeriesBall c ρ x
  x-inBall =
    record
      { displacementBound =
          powerSeriesCenterInBallFromMargin x-displacement-bound margin
      }

  forward-inBall :
    (ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (min⁺ (μ ε) (ν ε)) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    InPowerSeriesBall c ρ (x +ᶜ h)
  forward-inBall ε η η≤με h h-bound =
    subst
      (InPowerSeriesBall c ρ)
      (add-center-centeredDisplacement-forward c x h)
      (inPowerSeriesBallAtCenterPlusFromBound
        c
        (powerSeriesForwardInBallFromCenterMargin
          x-displacement-bound
          margin
          ε
          η
          η≤με
          h
          h-bound))


hasPowerSeriesAtWith→hasDerivativeAtWithFromUniformPartialSumsOnSubballCanonicalIndex :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {seriesModulus : ℚ⁺ → ℕ} →
  {μ : PrecisionModulus} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  HasPowerSeriesAtWith f c a ρ seriesModulus →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin :
    (ε : ℚ⁺) →
    radius (σ +⁺ partialSumsDerivativeTargetModulus μ ε)
      ℚOrder.≤ radius ρ) →
  PowerSeriesFormalPartialSumsHaveDerivativeWith
    a
    (centeredDisplacement c x)
    (λ _ → μ) →
  HasDerivativeAtWith
    f
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      (derivativePowerSeriesInfiniteRadius radiusData)
      x)
    (partialSumsDerivativeTargetModulus μ)
hasPowerSeriesAtWith→hasDerivativeAtWithFromUniformPartialSumsOnSubballCanonicalIndex
  {a = a}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  radiusData
  expansion
  x-displacement-bound
  margin
  partialDerivative =
  hasPowerSeriesAtWith→hasDerivativeAtWithFromEverywhereModel
    radiusData
    expansion
    x-inBall
    forward-inBall
    (centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromUniformPartialSumsOnSubballCanonicalIndex→hasDerivativeAtWith
      {a = a}
      {c = c}
      {x = x}
      {ρ = ρ}
      {σ = σ}
      {μ = μ}
      radiusData
      x-displacement-bound
      margin
      partialDerivative)
  where
  targetModulus : PrecisionModulus
  targetModulus =
    partialSumsDerivativeTargetModulus μ

  x-inBall : InPowerSeriesBall c ρ x
  x-inBall =
    record
      { displacementBound =
          powerSeriesCenterInBallFromMargin x-displacement-bound margin
      }

  forward-inBall :
    (ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (targetModulus ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    InPowerSeriesBall c ρ (x +ᶜ h)
  forward-inBall ε η η≤με h h-bound =
    subst
      (InPowerSeriesBall c ρ)
      (add-center-centeredDisplacement-forward c x h)
      (inPowerSeriesBallAtCenterPlusFromBound
        c
        (powerSeriesForwardInBallFromCenterMargin
          x-displacement-bound
          margin
        ε
        η
        η≤με
        h
        h-bound))


hasPowerSeriesAtWith→hasDerivativeAtWithFromSecondDerivativePartialSumsBoundOnSubballCanonicalIndex :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ Γ : ℚ⁺} →
  {seriesModulus : ℚ⁺ → ℕ} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  HasPowerSeriesAtWith f c a ρ seriesModulus →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin :
    (ε : ℚ⁺) →
    radius
      (σ +⁺
        partialSumsDerivativeTargetModulus
          (powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound Γ)
          ε)
      ℚOrder.≤ radius ρ) →
  PowerSeriesSecondDerivativePartialSumsBoundOnBallWith
    a
    (σ +⁺ 1⁺)
    Γ →
  HasDerivativeAtWith
    f
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      (derivativePowerSeriesInfiniteRadius radiusData)
      x)
    (partialSumsDerivativeTargetModulus
      (powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound Γ))
hasPowerSeriesAtWith→hasDerivativeAtWithFromSecondDerivativePartialSumsBoundOnSubballCanonicalIndex
  {a = a}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {Γ = Γ}
  radiusData
  expansion
  x-displacement-bound
  margin
  secondDerivativeBound =
  hasPowerSeriesAtWith→hasDerivativeAtWithFromUniformPartialSumsOnSubballCanonicalIndex
    {a = a}
    {c = c}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ = powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound Γ}
    radiusData
    expansion
    x-displacement-bound
    margin
    (powerSeriesFormalPartialSumsHaveDerivativeWithFromSecondDerivativeBound
      σ
      Γ
      x-displacement-bound
      secondDerivativeBound)


hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientPathAndTargetRadiusAndCoefficientBoundsOnSubballCanonicalIndex :
  {f : ℝᶜ → ℝᶜ} →
  {a b : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {seriesModulus : ℚ⁺ → ℕ} →
  {μ : PrecisionModulus} →
  (coeff≡ : (n : ℕ) → derivativePowerSeries a n ≡ b n) →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (targetRadius : HasInfinitePowerSeriesRadius b) →
  HasPowerSeriesAtWith f c a ρ seriesModulus →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  PowerSeriesPartialSumsDerivativeModulusLarge
    (termwiseConvergenceIndex
      (radiusData ρ .fst)
      (derivativePowerSeriesInfiniteRadiusFromCoefficientPath
        {a = a}
        {b = b}
        coeff≡
        targetRadius
        σ
        .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus
      σ
      (powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds
        σ
        κ)) →
  HasDerivativeAtWith f x (centeredPowerSeriesSumEverywhere b c targetRadius x) μ
hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientPathAndTargetRadiusAndCoefficientBoundsOnSubballCanonicalIndex
  {a = a}
  {b = b}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  coeff≡
  radiusData
  targetRadius
  expansion
  x-displacement-bound
  margin
  κ
  coefficientBounds
  partialModulus-large =
  hasPowerSeriesAtWith→hasDerivativeAtWithFromEverywhereModel
    radiusData
    expansion
    x-inBall
    forward-inBall
    (centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndTargetRadiusAndCoefficientBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
      {a = a}
      {b = b}
      {c = c}
      {x = x}
      {ρ = ρ}
      {σ = σ}
      {μ = μ}
      coeff≡
      radiusData
      targetRadius
      x-displacement-bound
      margin
      κ
      coefficientBounds
      partialModulus-large)
  where
  x-inBall : InPowerSeriesBall c ρ x
  x-inBall =
    record
      { displacementBound =
          powerSeriesCenterInBallFromMargin x-displacement-bound margin
      }

  forward-inBall :
    (ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (μ ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    InPowerSeriesBall c ρ (x +ᶜ h)
  forward-inBall ε η η≤με h h-bound =
    subst
      (InPowerSeriesBall c ρ)
      (add-center-centeredDisplacement-forward c x h)
      (inPowerSeriesBallAtCenterPlusFromBound
        c
        (powerSeriesForwardInBallFromCenterMargin
          x-displacement-bound
          margin
          ε
          η
          η≤με
          h
          h-bound))


hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientBoundsOnSubballCanonicalIndex :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {seriesModulus : ℚ⁺ → ℕ} →
  {μ : PrecisionModulus} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (derivativeRadius :
    HasInfinitePowerSeriesRadius (derivativePowerSeries a)) →
  HasPowerSeriesAtWith f c a ρ seriesModulus →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  PowerSeriesPartialSumsDerivativeModulusLarge
    (termwiseConvergenceIndex
      (radiusData ρ .fst)
      (derivativeRadius σ .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus
      σ
      (powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds
        σ
        κ)) →
  HasDerivativeAtWith
    f
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      derivativeRadius
      x)
    μ
hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientBoundsOnSubballCanonicalIndex
  {a = a}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  radiusData
  derivativeRadius
  expansion
  x-displacement-bound
  margin
  κ
  coefficientBounds
  partialModulus-large =
  hasPowerSeriesAtWith→hasDerivativeAtWithFromEverywhereModel
    radiusData
    expansion
    x-inBall
    forward-inBall
    (centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
      {a = a}
      {c = c}
      {x = x}
      {ρ = ρ}
      {σ = σ}
      {μ = μ}
      radiusData
      derivativeRadius
      x-displacement-bound
      margin
      κ
      coefficientBounds
      partialModulus-large)
  where
  x-inBall : InPowerSeriesBall c ρ x
  x-inBall =
    record
      { displacementBound =
          powerSeriesCenterInBallFromMargin x-displacement-bound margin
      }

  forward-inBall :
    (ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (μ ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    InPowerSeriesBall c ρ (x +ᶜ h)
  forward-inBall ε η η≤με h h-bound =
    subst
      (InPowerSeriesBall c ρ)
      (add-center-centeredDisplacement-forward c x h)
      (inPowerSeriesBallAtCenterPlusFromBound
        c
        (powerSeriesForwardInBallFromCenterMargin
          x-displacement-bound
          margin
          ε
          η
          η≤με
          h
          h-bound))


hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientBoundsOnSubballUniformModulus :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {seriesModulus : ℚ⁺ → ℕ} →
  {μ : PrecisionModulus} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  HasPowerSeriesAtWith f c a ρ seriesModulus →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  PowerSeriesPartialSumsDerivativeUniformModulus
    (termwiseConvergenceIndex
      (radiusData ρ .fst)
      (derivativePowerSeriesInfiniteRadius radiusData σ .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus
      σ
      (powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds
        σ
        κ)) →
  HasDerivativeAtWith
    f
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      (derivativePowerSeriesInfiniteRadius radiusData)
      x)
    μ
hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientBoundsOnSubballUniformModulus
  {a = a}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  radiusData
  expansion
  x-displacement-bound
  margin
  κ
  coefficientBounds
  uniformModulus =
  hasPowerSeriesAtWith→hasDerivativeAtWithFromIteratedBoundsOnSubballUniformModulus
    {a = a}
    {c = c}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ = μ}
    {δ = powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds σ κ}
    radiusData
    expansion
    x-displacement-bound
    margin
    (powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
      σ
      x-displacement-bound
      κ
      coefficientBounds)
    uniformModulus


hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientBoundsOnSubballUniformSubmodulus :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {seriesModulus : ℚ⁺ → ℕ} →
  {μ ν : PrecisionModulus} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  HasPowerSeriesAtWith f c a ρ seriesModulus →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin :
    (ε : ℚ⁺) →
    radius (σ +⁺ min⁺ (μ ε) (ν ε)) ℚOrder.≤ radius ρ) →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  PowerSeriesPartialSumsDerivativeUniformModulus
    (termwiseConvergenceIndex
      (radiusData ρ .fst)
      (derivativePowerSeriesInfiniteRadius radiusData σ .fst))
    ν
    (powerSeriesFormalPartialSumsDerivativeModulus
      σ
      (powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds
        σ
        κ)) →
  HasDerivativeAtWith
    f
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      (derivativePowerSeriesInfiniteRadius radiusData)
      x)
    (λ ε → min⁺ (μ ε) (ν ε))
hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientBoundsOnSubballUniformSubmodulus
  {a = a}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {ν = ν}
  radiusData
  expansion
  x-displacement-bound
  margin
  κ
  coefficientBounds
  uniformModulus =
  hasPowerSeriesAtWith→hasDerivativeAtWithFromIteratedBoundsOnSubballUniformSubmodulus
    {a = a}
    {c = c}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ = μ}
    {ν = ν}
    {δ = powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds σ κ}
    radiusData
    expansion
    x-displacement-bound
    margin
    (powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
      σ
      x-displacement-bound
      κ
      coefficientBounds)
    uniformModulus


hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientBoundsAndDerivativeMajorantsOnSubballCanonicalIndex :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {seriesModulus : ℚ⁺ → ℕ} →
  {μ : PrecisionModulus} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  HasPowerSeriesAtWith f c a ρ seriesModulus →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  (κ : ℕ → ℚ⁺) →
  (coefficientBounds : (n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  (derivativeMajorants :
    (τ : ℚ⁺) → DerivativePowerSeriesBoundMajorantOnBall κ τ) →
  PowerSeriesPartialSumsDerivativeModulusLarge
    (termwiseConvergenceIndex
      (radiusData ρ .fst)
      (derivativePowerSeriesInfiniteRadiusFromCoefficientBoundsAndMajorants
        {a = a}
        κ
        coefficientBounds
        derivativeMajorants
        σ
        .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus
      σ
      (powerSeriesFormalPartialDerivativeBoundFromSeriesCoefficientBounds
        σ
        κ)) →
  HasDerivativeAtWith
    f
    x
    (centeredPowerSeriesSumEverywhere
      (derivativePowerSeries a)
      c
      (derivativePowerSeriesInfiniteRadiusFromCoefficientBoundsAndMajorants
        {a = a}
        κ
        coefficientBounds
        derivativeMajorants)
      x)
    μ
hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientBoundsAndDerivativeMajorantsOnSubballCanonicalIndex
  {a = a}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  radiusData
  expansion
  x-displacement-bound
  margin
  κ
  coefficientBounds
  derivativeMajorants
  partialModulus-large =
  hasPowerSeriesAtWith→hasDerivativeAtWithFromCoefficientBoundsOnSubballCanonicalIndex
    {a = a}
    {c = c}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ = μ}
    radiusData
    derivativeRadius
    expansion
    x-displacement-bound
    margin
    κ
    coefficientBounds
    partialModulus-large
  where
  derivativeRadius : HasInfinitePowerSeriesRadius (derivativePowerSeries a)
  derivativeRadius =
    derivativePowerSeriesInfiniteRadiusFromCoefficientBoundsAndMajorants
      {a = a}
      κ
      coefficientBounds
      derivativeMajorants


PowerSeriesTermwiseDerivativeAt :
  (ℝᶜ → ℝᶜ) →
  PowerSeries →
  PowerSeries →
  ℝᶜ →
  ℝᶜ →
  Type₀
PowerSeriesTermwiseDerivativeAt f a da x d =
  Σ[ χ ∈ TermwiseDerivativeIndex ]
    Σ[ μ ∈ PrecisionModulus ]
      PowerSeriesTermwiseDerivativeAtWith f a da x d χ μ


PowerSeriesFormalTermwiseDerivativeAtWith :
  (ℝᶜ → ℝᶜ) →
  PowerSeries →
  (x d : ℝᶜ) →
  TermwiseDerivativeIndex →
  PrecisionModulus →
  Type₀
PowerSeriesFormalTermwiseDerivativeAtWith f a =
  PowerSeriesTermwiseDerivativeAtWith f a (derivativePowerSeries a)


PowerSeriesFormalTermwiseDerivativeAt :
  (ℝᶜ → ℝᶜ) →
  PowerSeries →
  ℝᶜ →
  ℝᶜ →
  Type₀
PowerSeriesFormalTermwiseDerivativeAt f a =
  PowerSeriesTermwiseDerivativeAt f a (derivativePowerSeries a)


powerSeriesTermwiseDerivativeAt→hasDerivativeAt :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {da : PowerSeries} →
  {x d : ℝᶜ} →
  PowerSeriesTermwiseDerivativeAt f a da x d →
  HasDerivativeAt f x d
powerSeriesTermwiseDerivativeAt→hasDerivativeAt (χ , μ , derivativeData) =
  μ ,
  powerSeriesTermwiseDerivativeAtWith→hasDerivativeAtWith
    {χ = χ}
    derivativeData
