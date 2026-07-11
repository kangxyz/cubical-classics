{-

Part of Constructive.Analysis.Reals.PowerSeries.Differentiation

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Differentiation.Limit where

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
open import Constructive.Analysis.Reals.Calculus.DerivativeRules
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
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Base
  using (HasPowerSeriesAtWith)
open import Constructive.Analysis.Reals.PowerSeries.Analytic.Consequences
  using (hasPowerSeriesAtWith→hasDerivativeAtWithFromEverywhereModel)
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.FormalDerivative
  using
    ( derivativePowerSeries
    ; derivativePrimitivePowerSeries
    ; naturalReal
    ; primitivePowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.Majorant
  using (DerivativePowerSeriesBoundMajorantOnBall)
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.Radius
  using
    ( derivativePowerSeriesInfiniteRadius
    ; derivativePowerSeriesInfiniteRadiusFromCoefficientPath
    )
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open ClosenessOf RationalsMetricSpace

open import Constructive.Analysis.Reals.PowerSeries.Differentiation.PowerEstimate
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.Index
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.Finite
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.PartialSums
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.IteratedBounds
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.UniformPartialSums
open import Constructive.Analysis.Reals.PowerSeries.Differentiation.ErrorBounds

termwiseDerivativeFromPieceBounds :
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
termwiseDerivativeFromPieceBounds
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


termwiseDerivativeFromCanonicalPieceBounds :
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
termwiseDerivativeFromCanonicalPieceBounds
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
  termwiseDerivativeFromPieceBounds
    (λ ε η _ h _ →
      powerSeriesTermwiseRemainderDecomposition f a da x d χ ε η h)
    forwardBound
    partialBound
    centerBound
    derivativeLinearBound


termwiseDerivativeFromCanonicalValueBounds :
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
termwiseDerivativeFromCanonicalValueBounds
  forwardBound
  partialBound
  centerBound
  derivativeValueBound =
  termwiseDerivativeFromCanonicalPieceBounds
    forwardBound
    partialBound
    centerBound
    (derivativeValueErrorBound→linearErrorBound derivativeValueBound)


termwiseDerivative→hasDerivative :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {da : PowerSeries} →
  {x d : ℝᶜ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  PowerSeriesTermwiseDerivativeAtWith f a da x d χ μ →
  HasDerivativeAtWith f x d μ
termwiseDerivative→hasDerivative
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



hasDerivativeAtWith-congDerivative :
  {f : ℝᶜ → ℝᶜ} →
  {x d e : ℝᶜ} →
  {μ : PrecisionModulus} →
  d ≡ e →
  HasDerivativeAtWith f x d μ →
  HasDerivativeAtWith f x e μ
hasDerivativeAtWith-congDerivative {f = f} {x = x} {μ = μ} d≡e =
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


centeredPowerSeriesHasDerivativeFromRemainderBounds :
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
centeredPowerSeriesHasDerivativeFromRemainderBounds
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
  hasDerivativeAtWith-congDerivative
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
    powerSeriesTermwiseDerivativeValueErrorBoundFromConvergence
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
    termwiseDerivative→hasDerivative
      (termwiseDerivativeFromCanonicalValueBounds
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


centeredPowerSeriesHasDerivativeFromIteratedBounds :
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
centeredPowerSeriesHasDerivativeFromIteratedBounds
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
  centeredPowerSeriesHasDerivativeFromRemainderBounds
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









centeredPowerSeriesHasDerivativeFromSecondDerivativeBounds :
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
centeredPowerSeriesHasDerivativeFromSecondDerivativeBounds
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
  centeredPowerSeriesHasDerivativeFromRemainderBounds
    {a = a}
    {b = derivativePowerSeries a}
    {c = c}
    {x = x}
    {ρ = ρ}
    {σ = σ}
    {μ =
      partialSumsDerivativeTargetModulus
        (powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound Γ)}
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
      {μ = powerSeriesFormalPartialSumsDerivativeModulusFromSecondBound Γ}
      (powerSeriesFormalPartialSumsHaveDerivativeWithFromSecondDerivativeBound
        σ
        Γ
        x-displacement-bound
        secondDerivativeBound))
  where
  derivativeRadius : HasInfinitePowerSeriesRadius (derivativePowerSeries a)
  derivativeRadius =
    derivativePowerSeriesInfiniteRadius radiusData



private
  transportCenteredDerivative :
    {f : ℝᶜ → ℝᶜ} →
    {a : PowerSeries} →
    {c x d : ℝᶜ} →
    {ρ σ : ℚ⁺} →
    {seriesModulus : ℚ⁺ → ℕ} →
    {μ : PrecisionModulus} →
    (radiusData : HasInfinitePowerSeriesRadius a) →
    HasPowerSeriesAtWith f c a ρ seriesModulus →
    (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
    ((ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
    HasDerivativeAtWith
      (centeredPowerSeriesSumEverywhere a c radiusData)
      x
      d
      μ →
    HasDerivativeAtWith f x d μ
  transportCenteredDerivative
    {c = c}
    {x = x}
    {ρ = ρ}
    {μ = μ}
    radiusData
    expansion
    x-displacement-bound
    margin =
    hasPowerSeriesAtWith→hasDerivativeAtWithFromEverywhereModel
      radiusData
      expansion
      x-inBall
      forward-inBall
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


hasPowerSeriesDerivativeFromIteratedBounds :
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
hasPowerSeriesDerivativeFromIteratedBounds
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
  transportCenteredDerivative
    radiusData
    expansion
    x-displacement-bound
    margin
    (centeredPowerSeriesHasDerivativeFromIteratedBounds
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
      (derivativePowerSeriesInfiniteRadiusFromCoefficientPath
        {a = a}
        {b = b}
        coeff≡
        targetRadius)
      targetRadius
      x-displacement-bound
      margin
      derivative-bounds
      partialModulus-large)


hasPowerSeriesDerivativeFromSecondDerivativeBounds :
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
hasPowerSeriesDerivativeFromSecondDerivativeBounds
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
  transportCenteredDerivative
    radiusData
    expansion
    x-displacement-bound
    margin
    (centeredPowerSeriesHasDerivativeFromSecondDerivativeBounds
      {a = a}
      {c = c}
      {x = x}
      {ρ = ρ}
      {σ = σ}
      radiusData
      x-displacement-bound
      margin
      secondDerivativeBound)


hasPowerSeriesDerivativeFromCoefficientBounds :
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
hasPowerSeriesDerivativeFromCoefficientBounds
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
  hasPowerSeriesDerivativeFromIteratedBounds
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
    expansion
    x-displacement-bound
    margin
    (powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
      σ
      x-displacement-bound
      κ
      coefficientBounds)
    partialModulus-large
