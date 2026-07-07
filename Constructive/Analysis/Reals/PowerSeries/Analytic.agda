{-

Function-facing analytic power-series data

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.Analytic where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)

open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Metric.Instances.CauchyReals
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
  using (add-close-left)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
  using (-ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.PowerSeries.Base
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
