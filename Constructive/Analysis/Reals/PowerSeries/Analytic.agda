{-

Function-facing analytic power-series data

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Analytic where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Rationals using (ℚ)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)

open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Metric.Instances.CauchyReals
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
  using (_+ᶜ_ ; add-close-left)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
  using (_·ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
  using (-ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.Series
  using (AntitoneTailModulus ; TailBound)
open import Constructive.Analysis.Reals.Sequences.Base
  using (maxModulus ; splitModulus)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( addPowerSeries
    ; addPowerSeriesOnBallWithMax
    ; negPowerSeries
    ; negPowerSeriesOnBallWith
    ; powerSeriesSumOnBall-addWithMax
    ; powerSeriesSumOnBall-neg
    ; powerSeriesSumOnBall-rationalScale
    ; powerSeriesSumOnBall-realScale
    ; powerSeriesSumOnBall-subWithMax
    ; rationalScaleModulus
    ; rationalScalePowerSeries
    ; rationalScalePowerSeriesOnBallWith
    ; realScaleModulus
    ; realScalePowerSeries
    ; realScalePowerSeriesOnBallWith
    ; subPowerSeries
    ; subPowerSeriesOnBallWithMax
    )
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct
  using
    ( cauchyProductPowerSeries
    ; cauchyProductPowerSeriesOnBallWithFromMajorants
    ; cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTail
    ; sequenceCauchyProduct
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using
    ( PowerSeriesMajorizedOnBall
    ; majorizedOnBall→hasPowerSeriesOnBallWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals


PowerSeriesExpansionPath :
  (ℝᶜ → ℝᶜ) →
  ℝᶜ →
  (a : PowerSeries) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  HasPowerSeriesOnBallWith a ρ μ →
  Type₀
PowerSeriesExpansionPath f c a ρ μ convergence =
  (x : ℝᶜ) →
  (inBall : InPowerSeriesBall c ρ x) →
  f x ≡ centeredPowerSeriesSumOnBall a c ρ μ convergence x inBall


HasPowerSeriesAtWith :
  (ℝᶜ → ℝᶜ) →
  ℝᶜ →
  PowerSeries →
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type₀
HasPowerSeriesAtWith f c a ρ μ =
  Σ[ convergence ∈ HasPowerSeriesOnBallWith a ρ μ ]
    PowerSeriesExpansionPath f c a ρ μ convergence


HasPowerSeriesAtOnBall :
  (ℝᶜ → ℝᶜ) →
  ℝᶜ →
  PowerSeries →
  ℚ⁺ →
  Type₀
HasPowerSeriesAtOnBall f c a ρ =
  Σ[ μ ∈ (ℚ⁺ → ℕ) ] HasPowerSeriesAtWith f c a ρ μ


HasPowerSeriesAt :
  (ℝᶜ → ℝᶜ) →
  ℝᶜ →
  PowerSeries →
  Type₀
HasPowerSeriesAt f c a =
  Σ[ ρ ∈ ℚ⁺ ] HasPowerSeriesAtOnBall f c a ρ


AnalyticAt :
  (ℝᶜ → ℝᶜ) →
  ℝᶜ →
  Type₀
AnalyticAt f c =
  Σ[ a ∈ PowerSeries ] HasPowerSeriesAt f c a


centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (ρ : ℚ⁺) →
  HasPowerSeriesAtWith
    (centeredPowerSeriesSumEverywhere a c radiusData)
    c
    a
    ρ
    (fst (radiusData ρ))
centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
  {a = a}
  {c = c}
  radiusData
  ρ =
  snd (radiusData ρ) ,
  λ x inBall →
    centeredPowerSeriesSumEverywhere-bound-path
      a
      c
      radiusData
      ρ
      x
      inBall


centeredPowerSeriesSumEverywhereHasPowerSeriesAtOnBall :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (ρ : ℚ⁺) →
  HasPowerSeriesAtOnBall
    (centeredPowerSeriesSumEverywhere a c radiusData)
    c
    a
    ρ
centeredPowerSeriesSumEverywhereHasPowerSeriesAtOnBall radiusData ρ =
  fst (radiusData ρ) ,
  centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith radiusData ρ


centeredPowerSeriesSumEverywhereHasPowerSeriesAt :
  {a : PowerSeries} →
  {c : ℝᶜ} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  HasPowerSeriesAt
    (centeredPowerSeriesSumEverywhere a c radiusData)
    c
    a
centeredPowerSeriesSumEverywhereHasPowerSeriesAt radiusData =
  1⁺ ,
  centeredPowerSeriesSumEverywhereHasPowerSeriesAtOnBall radiusData 1⁺


centeredPowerSeriesSumEverywhereAnalyticAt :
  (a : PowerSeries) →
  (c : ℝᶜ) →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  AnalyticAt (centeredPowerSeriesSumEverywhere a c radiusData) c
centeredPowerSeriesSumEverywhereAnalyticAt a c radiusData =
  a ,
  centeredPowerSeriesSumEverywhereHasPowerSeriesAt radiusData


PowerSeriesWithinExpansionPath :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  ℝᶜ →
  (a : PowerSeries) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  HasPowerSeriesOnBallWith a ρ μ →
  Type ℓ
PowerSeriesWithinExpansionPath {D = D} f c a ρ μ convergence =
  (x : ℝᶜ) →
  (domain : D x) →
  (inBall : InPowerSeriesBall c ρ x) →
  f x domain ≡ centeredPowerSeriesSumOnBall a c ρ μ convergence x inBall


HasPowerSeriesWithinAtWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  ℝᶜ →
  PowerSeries →
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  Type ℓ
HasPowerSeriesWithinAtWith {D = D} f c a ρ μ =
  Σ[ convergence ∈ HasPowerSeriesOnBallWith a ρ μ ]
    PowerSeriesWithinExpansionPath {D = D} f c a ρ μ convergence


HasPowerSeriesWithinAtOnBall :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  ℝᶜ →
  PowerSeries →
  ℚ⁺ →
  Type ℓ
HasPowerSeriesWithinAtOnBall {D = D} f c a ρ =
  Σ[ μ ∈ (ℚ⁺ → ℕ) ] HasPowerSeriesWithinAtWith {D = D} f c a ρ μ


HasPowerSeriesWithinAt :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  ℝᶜ →
  PowerSeries →
  Type ℓ
HasPowerSeriesWithinAt {D = D} f c a =
  Σ[ ρ ∈ ℚ⁺ ] HasPowerSeriesWithinAtOnBall {D = D} f c a ρ


AnalyticWithinAt :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  ℝᶜ →
  Type ℓ
AnalyticWithinAt {D = D} f c =
  Σ[ a ∈ PowerSeries ] HasPowerSeriesWithinAt {D = D} f c a


centeredPowerSeriesWithinBallFunction :
  (a : PowerSeries) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  HasPowerSeriesOnBallWith a ρ μ →
  (x : ℝᶜ) →
  InPowerSeriesBall c ρ x →
  ℝᶜ
centeredPowerSeriesWithinBallFunction a c ρ μ convergence x x-inBall =
  centeredPowerSeriesSumOnBall a c ρ μ convergence x x-inBall


centeredPowerSeriesWithinBallHasPowerSeriesWithinAtWith :
  (a : PowerSeries) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  HasPowerSeriesWithinAtWith
    {D = InPowerSeriesBall c ρ}
    (centeredPowerSeriesWithinBallFunction a c ρ μ convergence)
    c
    a
    ρ
    μ
centeredPowerSeriesWithinBallHasPowerSeriesWithinAtWith a c ρ μ convergence =
  convergence ,
  λ x domain inBall →
    centeredPowerSeriesSumOnBall-inBall-independent
      convergence
      x
      domain
      inBall


centeredPowerSeriesWithinBallHasPowerSeriesWithinAtOnBall :
  (a : PowerSeries) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  HasPowerSeriesWithinAtOnBall
    {D = InPowerSeriesBall c ρ}
    (centeredPowerSeriesWithinBallFunction a c ρ μ convergence)
    c
    a
    ρ
centeredPowerSeriesWithinBallHasPowerSeriesWithinAtOnBall a c ρ μ convergence =
  μ ,
  centeredPowerSeriesWithinBallHasPowerSeriesWithinAtWith
    a
    c
    ρ
    μ
    convergence


centeredPowerSeriesWithinBallHasPowerSeriesWithinAt :
  (a : PowerSeries) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  HasPowerSeriesWithinAt
    {D = InPowerSeriesBall c ρ}
    (centeredPowerSeriesWithinBallFunction a c ρ μ convergence)
    c
    a
centeredPowerSeriesWithinBallHasPowerSeriesWithinAt a c ρ μ convergence =
  ρ ,
  centeredPowerSeriesWithinBallHasPowerSeriesWithinAtOnBall
    a
    c
    ρ
    μ
    convergence


centeredPowerSeriesWithinBallAnalyticWithinAt :
  (a : PowerSeries) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (μ : ℚ⁺ → ℕ) →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  AnalyticWithinAt
    {D = InPowerSeriesBall c ρ}
    (centeredPowerSeriesWithinBallFunction a c ρ μ convergence)
    c
centeredPowerSeriesWithinBallAnalyticWithinAt a c ρ μ convergence =
  a ,
  centeredPowerSeriesWithinBallHasPowerSeriesWithinAt
    a
    c
    ρ
    μ
    convergence


HasPowerSeriesAtUniformlyContinuousOnBallWith :
  (ℝᶜ → ℝᶜ) →
  ℝᶜ →
  ℚ⁺ →
  PrecisionModulus →
  Type₀
HasPowerSeriesAtUniformlyContinuousOnBallWith f c ρ ν =
  (ε : ℚ⁺) →
  {x y : ℝᶜ} →
  (x-inBall : InPowerSeriesBall c ρ x) →
  (y-inBall : InPowerSeriesBall c ρ y) →
  MetricSpace.Close CauchyRealsMetricSpace x (ν ε) y →
  MetricSpace.Close CauchyRealsMetricSpace (f x) ε (f y)


HasPowerSeriesAtUniformlyContinuousOnBall :
  (ℝᶜ → ℝᶜ) →
  ℝᶜ →
  ℚ⁺ →
  Type₀
HasPowerSeriesAtUniformlyContinuousOnBall f c ρ =
  Σ[ ν ∈ PrecisionModulus ]
    HasPowerSeriesAtUniformlyContinuousOnBallWith f c ρ ν


HasPowerSeriesAtContinuousAtWith :
  (f : ℝᶜ → ℝᶜ) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (x : ℝᶜ) →
  InPowerSeriesBall c ρ x →
  PrecisionModulus →
  Type₀
HasPowerSeriesAtContinuousAtWith f c ρ x x-inBall ν =
  (ε : ℚ⁺) →
  {y : ℝᶜ} →
  (y-inBall : InPowerSeriesBall c ρ y) →
  MetricSpace.Close CauchyRealsMetricSpace x (ν ε) y →
  MetricSpace.Close CauchyRealsMetricSpace (f x) ε (f y)


HasPowerSeriesAtContinuousAt :
  (f : ℝᶜ → ℝᶜ) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (x : ℝᶜ) →
  InPowerSeriesBall c ρ x →
  Type₀
HasPowerSeriesAtContinuousAt f c ρ x x-inBall =
  Σ[ ν ∈ PrecisionModulus ]
    HasPowerSeriesAtContinuousAtWith f c ρ x x-inBall ν


HasPowerSeriesWithinAtUniformlyContinuousOnBallWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  ℝᶜ →
  ℚ⁺ →
  PrecisionModulus →
  Type ℓ
HasPowerSeriesWithinAtUniformlyContinuousOnBallWith {D = D} f c ρ ν =
  (ε : ℚ⁺) →
  {x y : ℝᶜ} →
  (x-domain : D x) →
  (y-domain : D y) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  (y-inBall : InPowerSeriesBall c ρ y) →
  MetricSpace.Close CauchyRealsMetricSpace x (ν ε) y →
  MetricSpace.Close CauchyRealsMetricSpace
    (f x x-domain)
    ε
    (f y y-domain)


HasPowerSeriesWithinAtUniformlyContinuousOnBall :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  ((x : ℝᶜ) → D x → ℝᶜ) →
  ℝᶜ →
  ℚ⁺ →
  Type ℓ
HasPowerSeriesWithinAtUniformlyContinuousOnBall {D = D} f c ρ =
  Σ[ ν ∈ PrecisionModulus ]
    HasPowerSeriesWithinAtUniformlyContinuousOnBallWith {D = D} f c ρ ν


HasPowerSeriesWithinAtContinuousAtWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  (f : (x : ℝᶜ) → D x → ℝᶜ) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (x : ℝᶜ) →
  D x →
  InPowerSeriesBall c ρ x →
  PrecisionModulus →
  Type ℓ
HasPowerSeriesWithinAtContinuousAtWith {D = D} f c ρ x x-domain x-inBall ν =
  (ε : ℚ⁺) →
  {y : ℝᶜ} →
  (y-domain : D y) →
  (y-inBall : InPowerSeriesBall c ρ y) →
  MetricSpace.Close CauchyRealsMetricSpace x (ν ε) y →
  MetricSpace.Close CauchyRealsMetricSpace
    (f x x-domain)
    ε
    (f y y-domain)


HasPowerSeriesWithinAtContinuousAt :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  (f : (x : ℝᶜ) → D x → ℝᶜ) →
  (c : ℝᶜ) →
  (ρ : ℚ⁺) →
  (x : ℝᶜ) →
  D x →
  InPowerSeriesBall c ρ x →
  Type ℓ
HasPowerSeriesWithinAtContinuousAt {D = D} f c ρ x x-domain x-inBall =
  Σ[ ν ∈ PrecisionModulus ]
    HasPowerSeriesWithinAtContinuousAtWith
      {D = D}
      f
      c
      ρ
      x
      x-domain
      x-inBall
      ν


hasPowerSeriesAtWith-congFunction :
  {f g : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  ((x : ℝᶜ) → f x ≡ g x) →
  HasPowerSeriesAtWith f c a ρ μ →
  HasPowerSeriesAtWith g c a ρ μ
hasPowerSeriesAtWith-congFunction f≡g (convergence , sumPath) =
  convergence ,
  λ x inBall →
    sym (f≡g x) ∙
    sumPath x inBall


hasPowerSeriesAtWith-neg :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesAtWith f c a ρ μ →
  HasPowerSeriesAtWith
    (λ x → -ᶜ f x)
    c
    (negPowerSeries a)
    ρ
    μ
hasPowerSeriesAtWith-neg {c = c} {a = a} (convergence , sumPath) =
  negPowerSeriesOnBallWith convergence ,
  λ x inBall →
    cong -ᶜ_ (sumPath x inBall) ∙
    sym
      (powerSeriesSumOnBall-neg
        convergence
        (centeredDisplacement c x)
        (InPowerSeriesBall.displacementBound inBall))


hasPowerSeriesAtWith-add :
  {f g : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν : ℚ⁺ → ℕ} →
  HasPowerSeriesAtWith f c a ρ μ →
  HasPowerSeriesAtWith g c b ρ ν →
  HasPowerSeriesAtWith
    (λ x → f x +ᶜ g x)
    c
    (addPowerSeries a b)
    ρ
    (splitModulus (maxModulus μ ν))
hasPowerSeriesAtWith-add
  {c = c}
  {a = a}
  {b = b}
  (leftConvergence , leftPath)
  (rightConvergence , rightPath) =
  addPowerSeriesOnBallWithMax leftConvergence rightConvergence ,
  λ x inBall →
    cong₂ _+ᶜ_ (leftPath x inBall) (rightPath x inBall) ∙
    sym
      (powerSeriesSumOnBall-addWithMax
        leftConvergence
        rightConvergence
        (centeredDisplacement c x)
        (InPowerSeriesBall.displacementBound inBall))


hasPowerSeriesAtWith-sub :
  {f g : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν : ℚ⁺ → ℕ} →
  HasPowerSeriesAtWith f c a ρ μ →
  HasPowerSeriesAtWith g c b ρ ν →
  HasPowerSeriesAtWith
    (λ x → f x +ᶜ (-ᶜ g x))
    c
    (subPowerSeries a b)
    ρ
    (splitModulus (maxModulus μ ν))
hasPowerSeriesAtWith-sub
  {c = c}
  {a = a}
  {b = b}
  (leftConvergence , leftPath)
  (rightConvergence , rightPath) =
  subPowerSeriesOnBallWithMax leftConvergence rightConvergence ,
  λ x inBall →
    cong₂ _+ᶜ_
      (leftPath x inBall)
      (cong -ᶜ_ (rightPath x inBall)) ∙
    sym
      (powerSeriesSumOnBall-subWithMax
        leftConvergence
        rightConvergence
        (centeredDisplacement c x)
        (InPowerSeriesBall.displacementBound inBall))


hasPowerSeriesAtWith-rationalScale :
  (q : ℚ) →
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesAtWith f c a ρ μ →
  HasPowerSeriesAtWith
    (λ x → rational q ·ᶜ f x)
    c
    (rationalScalePowerSeries q a)
    ρ
    (rationalScaleModulus q μ)
hasPowerSeriesAtWith-rationalScale q {c = c} (convergence , sumPath) =
  rationalScalePowerSeriesOnBallWith q convergence ,
  λ x inBall →
    cong (rational q ·ᶜ_) (sumPath x inBall) ∙
    sym
      (powerSeriesSumOnBall-rationalScale
        q
        convergence
        (centeredDisplacement c x)
        (InPowerSeriesBall.displacementBound inBall))


hasPowerSeriesAtWith-realScale :
  (s : ℝᶜ) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ s →
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesAtWith f c a ρ μ →
  HasPowerSeriesAtWith
    (λ x → s ·ᶜ f x)
    c
    (realScalePowerSeries s a)
    ρ
    (realScaleModulus κ μ)
hasPowerSeriesAtWith-realScale s κ s-bound {c = c} (convergence , sumPath) =
  realScalePowerSeriesOnBallWith s κ s-bound convergence ,
  λ x inBall →
    cong (s ·ᶜ_) (sumPath x inBall) ∙
    sym
      (powerSeriesSumOnBall-realScale
        s
        κ
        s-bound
        convergence
        (centeredDisplacement c x)
        (InPowerSeriesBall.displacementBound inBall))


hasPowerSeriesAtWith-cauchyProductFromMajorants :
  {f g : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a b A B : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν τ : ℚ⁺ → ℕ} →
  HasPowerSeriesAtWith f c a ρ ν →
  HasPowerSeriesAtWith g c b ρ τ →
  PowerSeriesMajorizedOnBall a ρ A ν →
  PowerSeriesMajorizedOnBall b ρ B τ →
  TailBound (sequenceCauchyProduct A B) μ →
  AntitoneTailModulus μ →
  HasPowerSeriesAtWith
    (λ x → f x ·ᶜ g x)
    c
    (cauchyProductPowerSeries a b)
    ρ
    μ
hasPowerSeriesAtWith-cauchyProductFromMajorants
  {c = c}
  {a = a}
  {b = b}
  {ρ = ρ}
  {μ = μ}
  {ν = ν}
  {τ = τ}
  (leftConvergence , leftPath)
  (rightConvergence , rightPath)
  leftMajorized
  rightMajorized
  productTail
  productAntitone =
  productConvergence ,
  λ x inBall →
    cong₂ _·ᶜ_ (leftPath x inBall) (rightPath x inBall) ∙
    cong₂ _·ᶜ_ (leftDataPath x inBall) (rightDataPath x inBall) ∙
    sym (productPath x inBall)
  where
  leftMajorConvergence :
    HasPowerSeriesOnBallWith a ρ ν
  leftMajorConvergence =
    majorizedOnBall→hasPowerSeriesOnBallWith leftMajorized

  rightMajorConvergence :
    HasPowerSeriesOnBallWith b ρ τ
  rightMajorConvergence =
    majorizedOnBall→hasPowerSeriesOnBallWith rightMajorized

  productConvergence :
    HasPowerSeriesOnBallWith (cauchyProductPowerSeries a b) ρ μ
  productConvergence =
    cauchyProductPowerSeriesOnBallWithFromMajorants
      leftMajorized
      rightMajorized
      productTail
      productAntitone

  leftDataPath :
    (x : ℝᶜ) →
    (inBall : InPowerSeriesBall c ρ x) →
    centeredPowerSeriesSumOnBall a c ρ ν leftConvergence x inBall ≡
    powerSeriesSumOnBall
      a
      ρ
      ν
      leftMajorConvergence
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
  leftDataPath x inBall =
    powerSeriesSumOnBall-data-independent
      leftConvergence
      leftMajorConvergence
      (centeredDisplacement c x)
      h-bound
      h-bound
    where
    h-bound : BoundedByᶜ ρ (centeredDisplacement c x)
    h-bound =
      InPowerSeriesBall.displacementBound inBall

  rightDataPath :
    (x : ℝᶜ) →
    (inBall : InPowerSeriesBall c ρ x) →
    centeredPowerSeriesSumOnBall b c ρ τ rightConvergence x inBall ≡
    powerSeriesSumOnBall
      b
      ρ
      τ
      rightMajorConvergence
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
  rightDataPath x inBall =
    powerSeriesSumOnBall-data-independent
      rightConvergence
      rightMajorConvergence
      (centeredDisplacement c x)
      h-bound
      h-bound
    where
    h-bound : BoundedByᶜ ρ (centeredDisplacement c x)
    h-bound =
      InPowerSeriesBall.displacementBound inBall

  productPath :
    (x : ℝᶜ) →
    (inBall : InPowerSeriesBall c ρ x) →
    powerSeriesSumOnBall
      (cauchyProductPowerSeries a b)
      ρ
      μ
      productConvergence
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
    ≡
    powerSeriesSumOnBall
      a
      ρ
      ν
      leftMajorConvergence
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
    ·ᶜ
    powerSeriesSumOnBall
      b
      ρ
      τ
      rightMajorConvergence
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
  productPath x inBall =
    cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTail
      leftMajorized
      rightMajorized
      productTail
      productAntitone
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)


hasPowerSeriesWithinAtWith-cauchyProductFromMajorants :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f g : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a b A B : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν τ : ℚ⁺ → ℕ} →
  HasPowerSeriesWithinAtWith {D = D} f c a ρ ν →
  HasPowerSeriesWithinAtWith {D = D} g c b ρ τ →
  PowerSeriesMajorizedOnBall a ρ A ν →
  PowerSeriesMajorizedOnBall b ρ B τ →
  TailBound (sequenceCauchyProduct A B) μ →
  AntitoneTailModulus μ →
  HasPowerSeriesWithinAtWith
    {D = D}
    (λ x domain → f x domain ·ᶜ g x domain)
    c
    (cauchyProductPowerSeries a b)
    ρ
    μ
hasPowerSeriesWithinAtWith-cauchyProductFromMajorants
  {D = D}
  {c = c}
  {a = a}
  {b = b}
  {ρ = ρ}
  {μ = μ}
  {ν = ν}
  {τ = τ}
  (leftConvergence , leftPath)
  (rightConvergence , rightPath)
  leftMajorized
  rightMajorized
  productTail
  productAntitone =
  productConvergence ,
  λ x domain inBall →
    cong₂ _·ᶜ_ (leftPath x domain inBall) (rightPath x domain inBall) ∙
    cong₂ _·ᶜ_ (leftDataPath x inBall) (rightDataPath x inBall) ∙
    sym (productPath x inBall)
  where
  leftMajorConvergence :
    HasPowerSeriesOnBallWith a ρ ν
  leftMajorConvergence =
    majorizedOnBall→hasPowerSeriesOnBallWith leftMajorized

  rightMajorConvergence :
    HasPowerSeriesOnBallWith b ρ τ
  rightMajorConvergence =
    majorizedOnBall→hasPowerSeriesOnBallWith rightMajorized

  productConvergence :
    HasPowerSeriesOnBallWith (cauchyProductPowerSeries a b) ρ μ
  productConvergence =
    cauchyProductPowerSeriesOnBallWithFromMajorants
      leftMajorized
      rightMajorized
      productTail
      productAntitone

  leftDataPath :
    (x : ℝᶜ) →
    (inBall : InPowerSeriesBall c ρ x) →
    centeredPowerSeriesSumOnBall a c ρ ν leftConvergence x inBall ≡
    powerSeriesSumOnBall
      a
      ρ
      ν
      leftMajorConvergence
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
  leftDataPath x inBall =
    powerSeriesSumOnBall-data-independent
      leftConvergence
      leftMajorConvergence
      (centeredDisplacement c x)
      h-bound
      h-bound
    where
    h-bound : BoundedByᶜ ρ (centeredDisplacement c x)
    h-bound =
      InPowerSeriesBall.displacementBound inBall

  rightDataPath :
    (x : ℝᶜ) →
    (inBall : InPowerSeriesBall c ρ x) →
    centeredPowerSeriesSumOnBall b c ρ τ rightConvergence x inBall ≡
    powerSeriesSumOnBall
      b
      ρ
      τ
      rightMajorConvergence
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
  rightDataPath x inBall =
    powerSeriesSumOnBall-data-independent
      rightConvergence
      rightMajorConvergence
      (centeredDisplacement c x)
      h-bound
      h-bound
    where
    h-bound : BoundedByᶜ ρ (centeredDisplacement c x)
    h-bound =
      InPowerSeriesBall.displacementBound inBall

  productPath :
    (x : ℝᶜ) →
    (inBall : InPowerSeriesBall c ρ x) →
    powerSeriesSumOnBall
      (cauchyProductPowerSeries a b)
      ρ
      μ
      productConvergence
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
    ≡
    powerSeriesSumOnBall
      a
      ρ
      ν
      leftMajorConvergence
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
    ·ᶜ
    powerSeriesSumOnBall
      b
      ρ
      τ
      rightMajorConvergence
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
  productPath x inBall =
    cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTail
      leftMajorized
      rightMajorized
      productTail
      productAntitone
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)


hasPowerSeriesWithinAtWith-congFunction :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f g : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  ((x : ℝᶜ) → (domain : D x) → f x domain ≡ g x domain) →
  HasPowerSeriesWithinAtWith {D = D} f c a ρ μ →
  HasPowerSeriesWithinAtWith {D = D} g c a ρ μ
hasPowerSeriesWithinAtWith-congFunction f≡g (convergence , sumPath) =
  convergence ,
  λ x domain inBall →
    sym (f≡g x domain) ∙
    sumPath x domain inBall


hasPowerSeriesAtWith→uniformlyContinuousOnBallWith :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  {ν : PrecisionModulus} →
  CenteredPowerSeriesSumUniformlyContinuousOnBallWith
    a
    c
    ρ
    μ
    (fst expansion)
    ν →
  HasPowerSeriesAtUniformlyContinuousOnBallWith f c ρ ν
hasPowerSeriesAtWith→uniformlyContinuousOnBallWith
  expansion
  uniform
  ε
  {x = x}
  {y = y}
  x-inBall
  y-inBall
  x∼y =
  subst2
    (λ u v → MetricSpace.Close CauchyRealsMetricSpace u ε v)
    (sym (snd expansion x x-inBall))
    (sym (snd expansion y y-inBall))
    (uniform ε x-inBall y-inBall x∼y)


hasPowerSeriesAtWith→uniformlyContinuousOnBall :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  CenteredPowerSeriesSumUniformlyContinuousOnBall
    a
    c
    ρ
    μ
    (fst expansion) →
  HasPowerSeriesAtUniformlyContinuousOnBall f c ρ
hasPowerSeriesAtWith→uniformlyContinuousOnBall expansion (ν , uniform) =
  ν ,
  hasPowerSeriesAtWith→uniformlyContinuousOnBallWith expansion uniform


hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  {ν : PrecisionModulus} →
  CenteredPowerSeriesSumUniformlyContinuousOnBallWith
    a
    c
    ρ
    μ
    (fst expansion)
    ν →
  HasPowerSeriesWithinAtUniformlyContinuousOnBallWith {D = D} f c ρ ν
hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallWith
  expansion
  uniform
  ε
  {x = x}
  {y = y}
  x-domain
  y-domain
  x-inBall
  y-inBall
  x∼y =
  subst2
    (λ u v → MetricSpace.Close CauchyRealsMetricSpace u ε v)
    (sym (snd expansion x x-domain x-inBall))
    (sym (snd expansion y y-domain y-inBall))
    (uniform ε x-inBall y-inBall x∼y)


hasPowerSeriesWithinAtWith→uniformlyContinuousOnBall :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  CenteredPowerSeriesSumUniformlyContinuousOnBall
    a
    c
    ρ
    μ
    (fst expansion) →
  HasPowerSeriesWithinAtUniformlyContinuousOnBall {D = D} f c ρ
hasPowerSeriesWithinAtWith→uniformlyContinuousOnBall expansion (ν , uniform) =
  ν ,
  hasPowerSeriesWithinAtWith→uniformlyContinuousOnBallWith expansion uniform


hasPowerSeriesAtWith→continuousAtWith :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  {ν : PrecisionModulus} →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  PowerSeriesSumContinuousAtWith
    a
    ρ
    μ
    (fst expansion)
    (centeredDisplacement c x)
    (InPowerSeriesBall.displacementBound x-inBall)
    ν →
  HasPowerSeriesAtContinuousAtWith f c ρ x x-inBall ν
hasPowerSeriesAtWith→continuousAtWith
  {c = c}
  expansion
  x
  x-inBall
  continuous
  ε
  {y = y}
  y-inBall
  x∼y =
  subst2
    (λ u v → MetricSpace.Close CauchyRealsMetricSpace u ε v)
    (sym (snd expansion x x-inBall))
    (sym (snd expansion y y-inBall))
    (continuous
      ε
      (InPowerSeriesBall.displacementBound y-inBall)
      (add-close-left x∼y (-ᶜ c)))


hasPowerSeriesAtWith→continuousAt :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesAtWith f c a ρ μ) →
  (x : ℝᶜ) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  PowerSeriesSumContinuousAt
    a
    ρ
    μ
    (fst expansion)
    (centeredDisplacement c x)
    (InPowerSeriesBall.displacementBound x-inBall) →
  HasPowerSeriesAtContinuousAt f c ρ x x-inBall
hasPowerSeriesAtWith→continuousAt expansion x x-inBall (ν , continuous) =
  ν ,
  hasPowerSeriesAtWith→continuousAtWith
    expansion
    x
    x-inBall
    continuous


hasPowerSeriesWithinAtWith→continuousAtWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  {ν : PrecisionModulus} →
  (x : ℝᶜ) →
  (x-domain : D x) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  PowerSeriesSumContinuousAtWith
    a
    ρ
    μ
    (fst expansion)
    (centeredDisplacement c x)
    (InPowerSeriesBall.displacementBound x-inBall)
    ν →
  HasPowerSeriesWithinAtContinuousAtWith
    {D = D}
    f
    c
    ρ
    x
    x-domain
    x-inBall
    ν
hasPowerSeriesWithinAtWith→continuousAtWith
  {c = c}
  expansion
  x
  x-domain
  x-inBall
  continuous
  ε
  {y = y}
  y-domain
  y-inBall
  x∼y =
  subst2
    (λ u v → MetricSpace.Close CauchyRealsMetricSpace u ε v)
    (sym (snd expansion x x-domain x-inBall))
    (sym (snd expansion y y-domain y-inBall))
    (continuous
      ε
      (InPowerSeriesBall.displacementBound y-inBall)
      (add-close-left x∼y (-ᶜ c)))


hasPowerSeriesWithinAtWith→continuousAt :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (expansion : HasPowerSeriesWithinAtWith {D = D} f c a ρ μ) →
  (x : ℝᶜ) →
  (x-domain : D x) →
  (x-inBall : InPowerSeriesBall c ρ x) →
  PowerSeriesSumContinuousAt
    a
    ρ
    μ
    (fst expansion)
    (centeredDisplacement c x)
    (InPowerSeriesBall.displacementBound x-inBall) →
  HasPowerSeriesWithinAtContinuousAt {D = D} f c ρ x x-domain x-inBall
hasPowerSeriesWithinAtWith→continuousAt
  expansion
  x
  x-domain
  x-inBall
  (ν , continuous) =
  ν ,
  hasPowerSeriesWithinAtWith→continuousAtWith
    expansion
    x
    x-domain
    x-inBall
    continuous
