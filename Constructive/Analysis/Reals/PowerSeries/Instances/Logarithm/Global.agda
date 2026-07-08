{-

Domain-evidenced global logarithm through the atanh transform

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.Global where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Tactics.CommRingSolver.Reflection

import Constructive.Algebra.OrderedCommRing.Properties as OrderedProperties
open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Metric.Instances.CauchyReals
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedDivision
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.CommRing
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (CauchyRealsOrderedCommRing ; mulᶜ-pres≤ᶜ-right)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using (nonnegativeᶜ-add)
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
  using (≤ℚ→rational≤ᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
  using (positiveSepᶜ→nonnegative)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Coefficients
  using (atanhPowerSeries)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Bounds
  using (atanhPowerSeriesCoefficientBounds)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Convergence
  using (atanhPowerSeriesOnSubunitBallWith)
open import Constructive.Analysis.Reals.PowerSeries.Continuity
  using (powerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonical)
open import Constructive.Analysis.Reals.PowerSeries.Radius
  using
    ( PowerSeriesSumUniformlyContinuousOnBall
    ; powerSeriesSumOnBall
    ; powerSeriesSumOnBall-data-independent
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
  using (positiveGeometricPowerModulus)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


private
  module CauchyRealsOrdered =
    OrderedProperties.OrderedCommRingTheory CauchyRealsOrderedCommRing

  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    upper-transform-margin :
      (x α : 𝓡 .fst) →
      ((1r + (- α)) · (x + 1r)) + (- (x + (- 1r))) ≡
      1r + (1r + (- (α · (x + 1r))))
    upper-transform-margin _ _ =
      solve! 𝓡

    lower-transform-margin :
      (x α : 𝓡 .fst) →
      ((1r + (- α)) · (x + 1r)) + (- (- (x + (- 1r)))) ≡
      x + (x + (- (α · (x + 1r))))
    lower-transform-margin _ _ =
      solve! 𝓡

    diff-plus-cancel :
      (x α : 𝓡 .fst) →
      (x + (- α)) + α ≡ x
    diff-plus-cancel _ _ =
      solve! 𝓡

  rational-subunit-path :
    (α : ℚ⁺) →
    (α<1 : radius α ℚOrder.< Rational.1ℚ) →
    rational (radius (1⁺ ⊖ α [ α<1 ])) ≡
    1ᶜ +ᶜ (-ᶜ rational (radius α))
  rational-subunit-path α α<1 =
    add-rational Rational.1ℚ (ℚ.- radius α) ∙
    cong (1ᶜ +ᶜ_) (sym (neg-rational (radius α)))

  scale-precision-cancel :
    (κ ε : ℚ⁺) →
    κ *⁺ (posInv⁺ κ *⁺ ε) ≡ ε
  scale-precision-cancel κ ε =
    sym (*⁺-assoc κ (posInv⁺ κ) ε) ∙
    cong (λ θ → θ *⁺ ε) (*⁺-posInv-right κ) ∙
    *⁺-identity-left ε

  scale-precision-mono :
    (κ ε δ : ℚ⁺) →
    ε <⁺ δ →
    κ *⁺ ε <⁺ κ *⁺ δ
  scale-precision-mono κ ε δ ε<δ =
    Rational.mul-left-positive-<
      {a = radius κ}
      {b = radius ε}
      {c = radius δ}
      (κ .snd)
      ε<δ

  scale-half-inverse< :
    (κ ε : ℚ⁺) →
    κ *⁺ half⁺ (posInv⁺ κ *⁺ ε) <⁺ ε
  scale-half-inverse< κ ε =
    subst
      (λ θ → κ *⁺ half⁺ (posInv⁺ κ *⁺ ε) <⁺ θ)
      (scale-precision-cancel κ ε)
      (scale-precision-mono
        κ
        (half⁺ (posInv⁺ κ *⁺ ε))
        (posInv⁺ κ *⁺ ε)
        (half< (posInv⁺ κ *⁺ ε)))

  mulᶜ-neg-left :
    (x y : ℝᶜ) →
    (-ᶜ x) ·ᶜ y ≡ -ᶜ (x ·ᶜ y)
  mulᶜ-neg-left x y =
    mulᶜ-comm (-ᶜ x) y ∙
    mulᶜ-neg-right y x ∙
    cong -ᶜ_ (mulᶜ-comm y x)


twoℚ : ℚ
twoℚ =
  Rational.1ℚ ℚ.+ Rational.1ℚ


twoᶜ : ℝᶜ
twoᶜ =
  rational twoℚ


two⁺ : ℚ⁺
two⁺ =
  1⁺ +⁺ 1⁺


twoᶜ-bound :
  BoundedByᶜ two⁺ twoᶜ
twoᶜ-bound =
  subst
    (BoundedByᶜ two⁺)
    (sym (add-rational Rational.1ℚ Rational.1ℚ))
    (bounded-byᶜ-add
      1⁺
      1⁺
      1ᶜ
      1ᶜ
      oneBoundedᶜ
      oneBoundedᶜ)


logTransformSubunitAlphaFromWindow :
  ℚ⁺ →
  ℚ⁺ →
  ℚ⁺
logTransformSubunitAlphaFromWindow lo hi =
  min⁺ 1⁺ lo *⁺ posInv⁺ (hi +⁺ 1⁺)


logTransformSubunitAlphaFromWindow<1 :
  (lo hi : ℚ⁺) →
  radius (logTransformSubunitAlphaFromWindow lo hi) ℚOrder.< Rational.1ℚ
logTransformSubunitAlphaFromWindow<1 lo hi =
  Rational.div-positive-denom-<1
    {q = radius m}
    {a = radius M}
    m<M
    (M .snd)
  where
  M : ℚ⁺
  M =
    hi +⁺ 1⁺

  m : ℚ⁺
  m =
    min⁺ 1⁺ lo

  m<M : radius m ℚOrder.< radius M
  m<M =
    Rational.≤<-trans
      {p = radius m}
      {q = Rational.1ℚ}
      {r = radius M}
      (min⁺≤left 1⁺ lo)
      1<M
    where
    1<M : Rational.1ℚ ℚOrder.< radius M
    1<M =
      subst2
        ℚOrder._<_
        (ℚ.+IdR Rational.1ℚ)
        (ℚ.+Comm Rational.1ℚ (radius hi))
        (ℚOrder.<-o+
          Rational.0ℚ
          (radius hi)
          Rational.1ℚ
          (hi .snd))


logTransformSubunitRadiusFromWindow :
  ℚ⁺ →
  ℚ⁺ →
  ℚ⁺
logTransformSubunitRadiusFromWindow lo hi =
  1⁺ ⊖
    logTransformSubunitAlphaFromWindow lo hi
    [ logTransformSubunitAlphaFromWindow<1 lo hi ]


logTransformSubunitRadiusFromWindow<1 :
  (lo hi : ℚ⁺) →
  radius (logTransformSubunitRadiusFromWindow lo hi) ℚOrder.< Rational.1ℚ
logTransformSubunitRadiusFromWindow<1 lo hi =
  subst
    (λ q → radius ρ ℚOrder.< q)
    (SolverHelpers.diff-plus-cancel ℚCommRing Rational.1ℚ (radius α))
    (Rational.q<q+positive (radius ρ) (radius α) (α .snd))
  where
  α : ℚ⁺
  α =
    logTransformSubunitAlphaFromWindow lo hi

  ρ : ℚ⁺
  ρ =
    logTransformSubunitRadiusFromWindow lo hi


logTransformᶜ :
  (x : ℝᶜ) →
  (denomLower : ℚ⁺) →
  BoundedAwayPositiveᶜ denomLower (x +ᶜ 1ᶜ) →
  ℝᶜ
logTransformᶜ x denomLower denomBound =
  divideByPositiveᶜ
    (x +ᶜ (-ᶜ 1ᶜ))
    denomLower
    (x +ᶜ 1ᶜ)
    denomBound


logTransformᶜ-data-independent :
  (x : ℝᶜ) →
  (leftLower rightLower : ℚ⁺) →
  (leftBound : BoundedAwayPositiveᶜ leftLower (x +ᶜ 1ᶜ)) →
  (rightBound : BoundedAwayPositiveᶜ rightLower (x +ᶜ 1ᶜ)) →
  logTransformᶜ x leftLower leftBound ≡
  logTransformᶜ x rightLower rightBound
logTransformᶜ-data-independent x leftLower rightLower leftBound rightBound =
  divideByPositiveᶜ-data-independent
    (x +ᶜ (-ᶜ 1ᶜ))
    leftLower
    rightLower
    (x +ᶜ 1ᶜ)
    leftBound
    rightBound


logTransformᶜ-uniformlyContinuousOnPositiveWindow :
  (lo hi : ℚ⁺) →
  Σ[ μ ∈ PrecisionModulus ]
    ((ε : ℚ⁺) →
      {x y : ℝᶜ} →
      (x-lower : BoundedAwayPositiveᶜ lo x) →
      (x-upper : BoundedByᶜ hi x) →
      (y-lower : BoundedAwayPositiveᶜ lo y) →
      (y-upper : BoundedByᶜ hi y) →
      MetricSpace.Close CauchyRealsMetricSpace x (μ ε) y →
      MetricSpace.Close CauchyRealsMetricSpace
        (logTransformᶜ
          x
          (lo +⁺ 1⁺)
          (lowerBound (positiveBoundedDomain-add-one
            (positive-bounded-domainᶜ lo hi x-lower x-upper))))
        ε
        (logTransformᶜ
          y
          (lo +⁺ 1⁺)
          (lowerBound (positiveBoundedDomain-add-one
            (positive-bounded-domainᶜ lo hi y-lower y-upper)))))
logTransformᶜ-uniformlyContinuousOnPositiveWindow lo hi =
  μ , closeAt
  where
  numeratorBound : ℚ⁺
  numeratorBound =
    hi +⁺ 1⁺

  denominatorLower : ℚ⁺
  denominatorLower =
    lo +⁺ 1⁺

  divisionUniform =
    divideByPositiveᶜ-uniformlyContinuousOnBounds
      numeratorBound
      denominatorLower

  μ : PrecisionModulus
  μ =
    fst divisionUniform

  minus-one-bound :
    BoundedByᶜ 1⁺ (-ᶜ 1ᶜ)
  minus-one-bound =
    bounded-byᶜ-neg 1⁺ 1ᶜ oneBoundedᶜ

  closeAt :
    (ε : ℚ⁺) →
    {x y : ℝᶜ} →
    (x-lower : BoundedAwayPositiveᶜ lo x) →
    (x-upper : BoundedByᶜ hi x) →
    (y-lower : BoundedAwayPositiveᶜ lo y) →
    (y-upper : BoundedByᶜ hi y) →
    MetricSpace.Close CauchyRealsMetricSpace x (μ ε) y →
    MetricSpace.Close CauchyRealsMetricSpace
      (logTransformᶜ
        x
        denominatorLower
        (lowerBound (positiveBoundedDomain-add-one
          (positive-bounded-domainᶜ lo hi x-lower x-upper))))
      ε
      (logTransformᶜ
        y
        denominatorLower
        (lowerBound (positiveBoundedDomain-add-one
          (positive-bounded-domainᶜ lo hi y-lower y-upper))))
  closeAt ε {x = x} {y = y} x-lower x-upper y-lower y-upper x∼y =
    snd divisionUniform
      ε
      x-minus-one-bound
      y-minus-one-bound
      x-denominator-bound
      y-denominator-bound
      x-minus-one∼y-minus-one
      x-plus-one∼y-plus-one
    where
    x-domain : PositiveBoundedDomainᶜ x
    x-domain =
      positive-bounded-domainᶜ lo hi x-lower x-upper

    y-domain : PositiveBoundedDomainᶜ y
    y-domain =
      positive-bounded-domainᶜ lo hi y-lower y-upper

    x-denominator-bound :
      BoundedAwayPositiveᶜ denominatorLower (x +ᶜ 1ᶜ)
    x-denominator-bound =
      lowerBound (positiveBoundedDomain-add-one x-domain)

    y-denominator-bound :
      BoundedAwayPositiveᶜ denominatorLower (y +ᶜ 1ᶜ)
    y-denominator-bound =
      lowerBound (positiveBoundedDomain-add-one y-domain)

    x-minus-one-bound :
      BoundedByᶜ numeratorBound (x +ᶜ (-ᶜ 1ᶜ))
    x-minus-one-bound =
      bounded-byᶜ-add
        hi
        1⁺
        x
        (-ᶜ 1ᶜ)
        x-upper
        minus-one-bound

    y-minus-one-bound :
      BoundedByᶜ numeratorBound (y +ᶜ (-ᶜ 1ᶜ))
    y-minus-one-bound =
      bounded-byᶜ-add
        hi
        1⁺
        y
        (-ᶜ 1ᶜ)
        y-upper
        minus-one-bound

    x-minus-one∼y-minus-one :
      MetricSpace.Close CauchyRealsMetricSpace
        (x +ᶜ (-ᶜ 1ᶜ))
        (μ ε)
        (y +ᶜ (-ᶜ 1ᶜ))
    x-minus-one∼y-minus-one =
      add-close-left x∼y (-ᶜ 1ᶜ)

    x-plus-one∼y-plus-one :
      MetricSpace.Close CauchyRealsMetricSpace
        (x +ᶜ 1ᶜ)
        (μ ε)
        (y +ᶜ 1ᶜ)
    x-plus-one∼y-plus-one =
      add-close-left x∼y 1ᶜ


record SubunitBoundᶜ (z : ℝᶜ) : Type₀ where
  constructor log-transform-subunit-boundᶜ

  field
    transformRadius : ℚ⁺
    transformRadius<1 :
      radius transformRadius ℚOrder.< Rational.1ℚ
    transformBound :
      BoundedByᶜ transformRadius z


open SubunitBoundᶜ public


LogTransformSubunitBoundᶜ :
  (x : ℝᶜ) →
  (denomLower : ℚ⁺) →
  BoundedAwayPositiveᶜ denomLower (x +ᶜ 1ᶜ) →
  Type₀
LogTransformSubunitBoundᶜ x denomLower denomBound =
  SubunitBoundᶜ (logTransformᶜ x denomLower denomBound)


atanhᶜFromSubunitBound :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  (z : ℝᶜ) →
  BoundedByᶜ ρ z →
  ℝᶜ
atanhᶜFromSubunitBound ρ ρ<1 z z-bound =
  powerSeriesSumOnBall
    atanhPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (atanhPowerSeriesOnSubunitBallWith ρ ρ<1)
    z
    z-bound


atanhᶜFromSubunitBound-data-independent :
  (ρ σ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (σ<1 : radius σ ℚOrder.< Rational.1ℚ) →
  (z : ℝᶜ) →
  (zρ : BoundedByᶜ ρ z) →
  (zσ : BoundedByᶜ σ z) →
  atanhᶜFromSubunitBound ρ ρ<1 z zρ ≡
  atanhᶜFromSubunitBound σ σ<1 z zσ
atanhᶜFromSubunitBound-data-independent ρ σ ρ<1 σ<1 z zρ zσ =
  powerSeriesSumOnBall-data-independent
    (atanhPowerSeriesOnSubunitBallWith ρ ρ<1)
    (atanhPowerSeriesOnSubunitBallWith σ σ<1)
    z
    zρ
    zσ


atanhᶜFromSubunitBound-uniformlyContinuous :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  PowerSeriesSumUniformlyContinuousOnBall
    atanhPowerSeries
    ρ
    (positiveGeometricPowerModulus ρ ρ<1)
    (atanhPowerSeriesOnSubunitBallWith ρ ρ<1)
atanhᶜFromSubunitBound-uniformlyContinuous ρ ρ<1 =
  powerSeriesSumUniformlyContinuousFromCoefficientBoundsCanonical
    {a = atanhPowerSeries}
    {ρ = ρ}
    {μ = positiveGeometricPowerModulus ρ ρ<1}
    {convergence = atanhPowerSeriesOnSubunitBallWith ρ ρ<1}
    atanhPowerSeriesCoefficientBounds


record LogDomainᶜ (x : ℝᶜ) : Type₀ where
  constructor log-domainᶜ

  field
    positiveDomain : PositiveBoundedDomainᶜ x
    denominatorLower : ℚ⁺
    denominatorBound :
      BoundedAwayPositiveᶜ denominatorLower (x +ᶜ 1ᶜ)
    transformValue : ℝᶜ
    transformRadius : ℚ⁺
    transformRadius<1 :
      radius transformRadius ℚOrder.< Rational.1ℚ
    transformBound :
      BoundedByᶜ transformRadius transformValue


open LogDomainᶜ public


logᶜ :
  (x : ℝᶜ) →
  LogDomainᶜ x →
  ℝᶜ
logᶜ x domain =
  twoᶜ ·ᶜ
  atanhᶜFromSubunitBound
    (transformRadius domain)
    (transformRadius<1 domain)
    (transformValue domain)
    (transformBound domain)


log-domain-from-transform-boundᶜ :
  (x : ℝᶜ) →
  (domain : PositiveBoundedDomainᶜ x) →
  (denomLower : ℚ⁺) →
  (denomBound : BoundedAwayPositiveᶜ denomLower (x +ᶜ 1ᶜ)) →
  LogTransformSubunitBoundᶜ x denomLower denomBound →
  LogDomainᶜ x
log-domain-from-transform-boundᶜ
  x
  domain
  denomLower
  denomBound
  boundData =
  log-domainᶜ
    domain
    denomLower
    denomBound
    (logTransformᶜ x denomLower denomBound)
    (transformRadius boundData)
    (transformRadius<1 boundData)
    (transformBound boundData)


logTransformSubunitBoundFromPositiveBoundedᶜ :
  (x : ℝᶜ) →
  (domain : PositiveBoundedDomainᶜ x) →
  LogTransformSubunitBoundᶜ
    x
    (lower (positiveBoundedDomain-add-one domain))
    (lowerBound (positiveBoundedDomain-add-one domain))
logTransformSubunitBoundFromPositiveBoundedᶜ x domain =
  log-transform-subunit-boundᶜ
    ρ
    ρ<1
    transform-bound
  where
  denominatorDomain : PositiveBoundedDomainᶜ (x +ᶜ 1ᶜ)
  denominatorDomain =
    positiveBoundedDomain-add-one domain

  y : ℝᶜ
  y =
    x +ᶜ 1ᶜ

  n : ℝᶜ
  n =
    x +ᶜ (-ᶜ 1ᶜ)

  denomLower : ℚ⁺
  denomLower =
    lower denominatorDomain

  denomBound :
    BoundedAwayPositiveᶜ denomLower y
  denomBound =
    lowerBound denominatorDomain

  r : ℝᶜ
  r =
    reciprocalPositiveᶜ denomLower y denomBound

  M : ℚ⁺
  M =
    upper denominatorDomain

  m : ℚ⁺
  m =
    min⁺ 1⁺ (lower domain)

  α : ℚ⁺
  α =
    logTransformSubunitAlphaFromWindow
      (lower domain)
      (upper domain)

  α<1 : radius α ℚOrder.< Rational.1ℚ
  α<1 =
    logTransformSubunitAlphaFromWindow<1
      (lower domain)
      (upper domain)

  ρ : ℚ⁺
  ρ =
    logTransformSubunitRadiusFromWindow
      (lower domain)
      (upper domain)

  ρ<1 : radius ρ ℚOrder.< Rational.1ℚ
  ρ<1 =
    logTransformSubunitRadiusFromWindow<1
      (lower domain)
      (upper domain)

  αᶜ : ℝᶜ
  αᶜ =
    rational (radius α)

  ρᶜ : ℝᶜ
  ρᶜ =
    rational (radius ρ)

  ρᶜ-path :
    ρᶜ ≡ 1ᶜ +ᶜ (-ᶜ αᶜ)
  ρᶜ-path =
    rational-subunit-path α α<1

  y-nonnegative :
    0ᶜ ≤ᶜ y
  y-nonnegative =
    positiveSepᶜ→nonnegative
      (boundedAwayPositiveᶜ→positiveSepᶜ denomBound)

  α-nonnegative :
    0ᶜ ≤ᶜ αᶜ
  α-nonnegative =
    ≤ℚ→rational≤ᶜ
      (Rational.<→≤
        {p = Rational.0ℚ}
        {q = radius α}
        (α .snd))

  αM-path :
    αᶜ ·ᶜ rational (radius M) ≡ rational (radius m)
  αM-path =
    mulᶜ-rational-rational (radius α) (radius M) ∙
    cong rational αM≡m
    where
    αM≡m :
      radius α ℚ.· radius M ≡ radius m
    αM≡m =
      sym
        (ℚ.·Assoc
          (radius m)
          (Rational.posInv (radius M) (M .snd))
          (radius M)) ∙
      cong (radius m ℚ.·_)
        (Rational.posInv-left (radius M) (M .snd)) ∙
      ℚ.·IdR (radius m)

  αy≤αM :
    αᶜ ·ᶜ y ≤ᶜ αᶜ ·ᶜ rational (radius M)
  αy≤αM =
    CauchyRealsOrdered.·-PosPres≥
      α-nonnegative
      y-nonnegative
      (≤ᶜ-refl αᶜ)
      (upperᶜ (upperBound denominatorDomain))

  αM≤m :
    αᶜ ·ᶜ rational (radius M) ≤ᶜ rational (radius m)
  αM≤m =
    subst
      (λ z → z ≤ᶜ rational (radius m))
      (sym αM-path)
      (≤ᶜ-refl (rational (radius m)))

  αy≤m :
    αᶜ ·ᶜ y ≤ᶜ rational (radius m)
  αy≤m =
    ≤ᶜ-trans αy≤αM αM≤m

  αy≤1 :
    αᶜ ·ᶜ y ≤ᶜ 1ᶜ
  αy≤1 =
    ≤ᶜ-trans
      αy≤m
      (≤ℚ→rational≤ᶜ (min⁺≤left 1⁺ (lower domain)))

  αy≤x :
    αᶜ ·ᶜ y ≤ᶜ x
  αy≤x =
    ≤ᶜ-trans
      αy≤m
      (≤ᶜ-trans
        (≤ℚ→rational≤ᶜ (min⁺≤right 1⁺ (lower domain)))
        (lowerBound domain .BoundedAwayPositiveᶜ.lowerᶜ))

  upper-margin-nonnegative :
    0ᶜ ≤ᶜ 1ᶜ +ᶜ (1ᶜ +ᶜ (-ᶜ (αᶜ ·ᶜ y)))
  upper-margin-nonnegative =
    nonnegativeᶜ-add
      (≤ℚ→rational≤ᶜ
        (Rational.<→≤
          {p = Rational.0ℚ}
          {q = Rational.1ℚ}
          Rational.0<1))
      (CauchyRealsOrdered.≥→Diff≥0
        {x = 1ᶜ}
        {y = αᶜ ·ᶜ y}
        αy≤1)

  upper-diff-path :
    (ρᶜ ·ᶜ y) +ᶜ (-ᶜ n) ≡
    1ᶜ +ᶜ (1ᶜ +ᶜ (-ᶜ (αᶜ ·ᶜ y)))
  upper-diff-path =
    cong (λ w → (w ·ᶜ y) +ᶜ (-ᶜ n)) ρᶜ-path ∙
    SolverHelpers.upper-transform-margin CauchyRealsCommRing x αᶜ

  n≤ρy :
    n ≤ᶜ ρᶜ ·ᶜ y
  n≤ρy =
    CauchyRealsOrdered.Diff≥0→≥
      {x = ρᶜ ·ᶜ y}
      {y = n}
      (subst
        (λ z → 0ᶜ ≤ᶜ z)
        (sym upper-diff-path)
        upper-margin-nonnegative)

  lower-margin-nonnegative :
    0ᶜ ≤ᶜ x +ᶜ (x +ᶜ (-ᶜ (αᶜ ·ᶜ y)))
  lower-margin-nonnegative =
    nonnegativeᶜ-add
      (positiveSepᶜ→nonnegative
        (boundedAwayPositiveᶜ→positiveSepᶜ (lowerBound domain)))
      (CauchyRealsOrdered.≥→Diff≥0
        {x = x}
        {y = αᶜ ·ᶜ y}
        αy≤x)

  lower-diff-path :
    (ρᶜ ·ᶜ y) +ᶜ (-ᶜ (-ᶜ n)) ≡
    x +ᶜ (x +ᶜ (-ᶜ (αᶜ ·ᶜ y)))
  lower-diff-path =
    cong (λ w → (w ·ᶜ y) +ᶜ (-ᶜ (-ᶜ n))) ρᶜ-path ∙
    SolverHelpers.lower-transform-margin CauchyRealsCommRing x αᶜ

  -n≤ρy :
    -ᶜ n ≤ᶜ ρᶜ ·ᶜ y
  -n≤ρy =
    CauchyRealsOrdered.Diff≥0→≥
      {x = ρᶜ ·ᶜ y}
      {y = -ᶜ n}
      (subst
        (λ z → 0ᶜ ≤ᶜ z)
        (sym lower-diff-path)
        lower-margin-nonnegative)

  r-nonnegative :
    0ᶜ ≤ᶜ r
  r-nonnegative =
    reciprocalPositiveᶜ-nonnegative denomLower y denomBound

  ρyr-path :
    (ρᶜ ·ᶜ y) ·ᶜ r ≡ ρᶜ
  ρyr-path =
    sym (mulᶜ-assoc ρᶜ y r) ∙
    cong (ρᶜ ·ᶜ_) (reciprocalPositiveᶜ-right denomLower y denomBound) ∙
    mulᶜ-one-right ρᶜ

  transform-bound :
    BoundedByᶜ
      ρ
      (logTransformᶜ x denomLower denomBound)
  transform-bound =
    bounded-byᶜ upper-bound lower-bound
    where
    upper-bound :
      logTransformᶜ x denomLower denomBound ≤ᶜ ρᶜ
    upper-bound =
      ≤ᶜ-trans
        (mulᶜ-pres≤ᶜ-right n (ρᶜ ·ᶜ y) r r-nonnegative n≤ρy)
        (subst
          (λ z → z ≤ᶜ ρᶜ)
          (sym ρyr-path)
          (≤ᶜ-refl ρᶜ))

    lower-bound :
      -ᶜ logTransformᶜ x denomLower denomBound ≤ᶜ ρᶜ
    lower-bound =
      subst2
        _≤ᶜ_
        (mulᶜ-neg-left n r)
        ρyr-path
        (mulᶜ-pres≤ᶜ-right
          (-ᶜ n)
          (ρᶜ ·ᶜ y)
          r
          r-nonnegative
          -n≤ρy)


log-domain-from-positive-boundedᶜ :
  (x : ℝᶜ) →
  (domain : PositiveBoundedDomainᶜ x) →
  LogDomainᶜ x
log-domain-from-positive-boundedᶜ x domain =
  log-domain-from-transform-boundᶜ
    x
    domain
    (lower denominatorDomain)
    (lowerBound denominatorDomain)
    (logTransformSubunitBoundFromPositiveBoundedᶜ x domain)
  where
  denominatorDomain : PositiveBoundedDomainᶜ (x +ᶜ 1ᶜ)
  denominatorDomain =
    positiveBoundedDomain-add-one domain


logᶜ-positive-bounded :
  (x : ℝᶜ) →
  PositiveBoundedDomainᶜ x →
  ℝᶜ
logᶜ-positive-bounded x domain =
  logᶜ x (log-domain-from-positive-boundedᶜ x domain)


logᶜ-positive-bounded-uniformlyContinuousOnWindow :
  (lo hi : ℚ⁺) →
  Σ[ μ ∈ PrecisionModulus ]
    ((ε : ℚ⁺) →
      {x y : ℝᶜ} →
      (x-lower : BoundedAwayPositiveᶜ lo x) →
      (x-upper : BoundedByᶜ hi x) →
      (y-lower : BoundedAwayPositiveᶜ lo y) →
      (y-upper : BoundedByᶜ hi y) →
      MetricSpace.Close CauchyRealsMetricSpace x (μ ε) y →
      MetricSpace.Close CauchyRealsMetricSpace
        (logᶜ-positive-bounded
          x
          (positive-bounded-domainᶜ lo hi x-lower x-upper))
        ε
        (logᶜ-positive-bounded
          y
          (positive-bounded-domainᶜ lo hi y-lower y-upper)))
logᶜ-positive-bounded-uniformlyContinuousOnWindow lo hi =
  μ , closeAt
  where
  ρ : ℚ⁺
  ρ =
    logTransformSubunitRadiusFromWindow lo hi

  ρ<1 : radius ρ ℚOrder.< Rational.1ℚ
  ρ<1 =
    logTransformSubunitRadiusFromWindow<1 lo hi

  atanhUniform =
    atanhᶜFromSubunitBound-uniformlyContinuous ρ ρ<1

  atanhModulus : PrecisionModulus
  atanhModulus =
    fst atanhUniform

  outerTarget : PrecisionModulus
  outerTarget ε =
    half⁺ (posInv⁺ two⁺ *⁺ ε)

  transformUniform =
    logTransformᶜ-uniformlyContinuousOnPositiveWindow lo hi

  transformModulus : PrecisionModulus
  transformModulus =
    fst transformUniform

  μ : PrecisionModulus
  μ ε =
    transformModulus (atanhModulus (outerTarget ε))

  closeAt :
    (ε : ℚ⁺) →
    {x y : ℝᶜ} →
    (x-lower : BoundedAwayPositiveᶜ lo x) →
    (x-upper : BoundedByᶜ hi x) →
    (y-lower : BoundedAwayPositiveᶜ lo y) →
    (y-upper : BoundedByᶜ hi y) →
    MetricSpace.Close CauchyRealsMetricSpace x (μ ε) y →
    MetricSpace.Close CauchyRealsMetricSpace
      (logᶜ-positive-bounded
        x
        (positive-bounded-domainᶜ lo hi x-lower x-upper))
      ε
      (logᶜ-positive-bounded
        y
        (positive-bounded-domainᶜ lo hi y-lower y-upper))
  closeAt ε {x = x} {y = y} x-lower x-upper y-lower y-upper x∼y =
    MetricSpace.close-mono
      CauchyRealsMetricSpace
      (scale-half-inverse< two⁺ ε)
      (mulᶜ-close-right-with-bound
        two⁺
        twoᶜ
        twoᶜ-bound
        atanh-close)
    where
    x-domain : PositiveBoundedDomainᶜ x
    x-domain =
      positive-bounded-domainᶜ lo hi x-lower x-upper

    y-domain : PositiveBoundedDomainᶜ y
    y-domain =
      positive-bounded-domainᶜ lo hi y-lower y-upper

    x-denominator-domain : PositiveBoundedDomainᶜ (x +ᶜ 1ᶜ)
    x-denominator-domain =
      positiveBoundedDomain-add-one x-domain

    y-denominator-domain : PositiveBoundedDomainᶜ (y +ᶜ 1ᶜ)
    y-denominator-domain =
      positiveBoundedDomain-add-one y-domain

    x-denominator-bound :
      BoundedAwayPositiveᶜ (lo +⁺ 1⁺) (x +ᶜ 1ᶜ)
    x-denominator-bound =
      lowerBound x-denominator-domain

    y-denominator-bound :
      BoundedAwayPositiveᶜ (lo +⁺ 1⁺) (y +ᶜ 1ᶜ)
    y-denominator-bound =
      lowerBound y-denominator-domain

    x-transform-bound :
      BoundedByᶜ ρ (logTransformᶜ x (lo +⁺ 1⁺) x-denominator-bound)
    x-transform-bound =
      transformBound (logTransformSubunitBoundFromPositiveBoundedᶜ x x-domain)

    y-transform-bound :
      BoundedByᶜ ρ (logTransformᶜ y (lo +⁺ 1⁺) y-denominator-bound)
    y-transform-bound =
      transformBound (logTransformSubunitBoundFromPositiveBoundedᶜ y y-domain)

    transform-close :
      MetricSpace.Close CauchyRealsMetricSpace
        (logTransformᶜ x (lo +⁺ 1⁺) x-denominator-bound)
        (atanhModulus (outerTarget ε))
        (logTransformᶜ y (lo +⁺ 1⁺) y-denominator-bound)
    transform-close =
      snd transformUniform
        (atanhModulus (outerTarget ε))
        x-lower
        x-upper
        y-lower
        y-upper
        x∼y

    atanh-close :
      MetricSpace.Close CauchyRealsMetricSpace
        (atanhᶜFromSubunitBound
          ρ
          ρ<1
          (logTransformᶜ x (lo +⁺ 1⁺) x-denominator-bound)
          x-transform-bound)
        (outerTarget ε)
        (atanhᶜFromSubunitBound
          ρ
          ρ<1
          (logTransformᶜ y (lo +⁺ 1⁺) y-denominator-bound)
          y-transform-bound)
    atanh-close =
      snd atanhUniform
        (outerTarget ε)
        x-transform-bound
        y-transform-bound
        transform-close


logᶜ-fromPositiveBounded :
  (x : ℝᶜ) →
  (domain : PositiveBoundedDomainᶜ x) →
  (denomLower : ℚ⁺) →
  (denomBound : BoundedAwayPositiveᶜ denomLower (x +ᶜ 1ᶜ)) →
  LogTransformSubunitBoundᶜ x denomLower denomBound →
  ℝᶜ
logᶜ-fromPositiveBounded x domain denomLower denomBound boundData =
  logᶜ x
    (log-domain-from-transform-boundᶜ
      x
      domain
      denomLower
      denomBound
      boundData)


logᶜ-fromPositiveBounded-bound-independent :
  (x : ℝᶜ) →
  (domain : PositiveBoundedDomainᶜ x) →
  (denomLower : ℚ⁺) →
  (denomBound : BoundedAwayPositiveᶜ denomLower (x +ᶜ 1ᶜ)) →
  (left right : LogTransformSubunitBoundᶜ x denomLower denomBound) →
  logᶜ-fromPositiveBounded x domain denomLower denomBound left ≡
  logᶜ-fromPositiveBounded x domain denomLower denomBound right
logᶜ-fromPositiveBounded-bound-independent
  x
  domain
  denomLower
  denomBound
  left
  right =
  cong (twoᶜ ·ᶜ_)
    (atanhᶜFromSubunitBound-data-independent
      (transformRadius left)
      (transformRadius right)
      (transformRadius<1 left)
      (transformRadius<1 right)
      (logTransformᶜ x denomLower denomBound)
      (transformBound left)
      (transformBound right))
