{-

Bounded positive reciprocal and division data for HoTT Cauchy reals

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedDivision where

open import Cubical.Foundations.Prelude

import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Relation.Nullary using (¬_)

import Constructive.Algebra.OrderedCommRing.Properties as OrderedProperties
open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Metric.Instances.CauchyReals
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Inverse
  using (right-inverse-uniqueᶜ)
open import
  Constructive.Analysis.Reals.CauchyReals.Arithmetic.Internal.BoundedReciprocal
  public
  using
    ( BoundedAwayPositiveᶜ
    ; bounded-away-positiveᶜ
    ; boundedAwayPositiveᶜ→positiveSepᶜ
    ; positiveSepᶜ→merelyBoundedAwayPositiveᶜ
    ; boundedAwayPositiveᶜ-weaken
    ; positive-rational-awayᶜ
    )
open import
  Constructive.Analysis.Reals.CauchyReals.Arithmetic.Internal.BoundedReciprocal
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using
    ( CauchyRealsOrderedCommRing
    ; bounded-byᶜ-mul
    ; mulᶜ-pres<ᶜ-right
    ; mulᶜ-pres≤ᶜ-right
    )
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using (neg-zeroᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
  using (≤ℚ→rational≤ᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
  using (PositiveSepᶜ ; _<ᶜ_ ; 0ᶜ<1ᶜ ; ≤ᶜ-add ; negᶜ-pres≤ᶜ)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


private
  module CauchyRealsOrdered =
    OrderedProperties.OrderedCommRingTheory CauchyRealsOrderedCommRing

  scale-precision-cancel :
    (κ ε : ℚ⁺) →
    κ *⁺ (posInv⁺ κ *⁺ ε) ≡ ε
  scale-precision-cancel κ ε =
    sym (*⁺-assoc κ (posInv⁺ κ) ε) ∙
    cong (λ ρ → ρ *⁺ ε) (*⁺-posInv-right κ) ∙
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


reciprocalPositiveᶜ :
  (ε : ℚ⁺) →
  (x : ℝᶜ) →
  BoundedAwayPositiveᶜ ε x →
  ℝᶜ
reciprocalPositiveᶜ =
  boundedAwayReciprocalᶜ


reciprocalPositiveᶜ-bound :
  (ε : ℚ⁺) →
  (x : ℝᶜ) →
  (x-bound : BoundedAwayPositiveᶜ ε x) →
  BoundedByᶜ
    (reciprocalLipschitzBase⁺ (half⁺ ε))
    (reciprocalPositiveᶜ ε x x-bound)
reciprocalPositiveᶜ-bound =
  boundedAwayReciprocalᶜ-bound


reciprocalPositiveᶜ-right :
  (ε : ℚ⁺) →
  (x : ℝᶜ) →
  (x-bound : BoundedAwayPositiveᶜ ε x) →
  x ·ᶜ reciprocalPositiveᶜ ε x x-bound ≡ 1ᶜ
reciprocalPositiveᶜ-right =
  boundedAwayReciprocalᶜ-right


reciprocalPositiveᶜ-left :
  (ε : ℚ⁺) →
  (x : ℝᶜ) →
  (x-bound : BoundedAwayPositiveᶜ ε x) →
  reciprocalPositiveᶜ ε x x-bound ·ᶜ x ≡ 1ᶜ
reciprocalPositiveᶜ-left =
  boundedAwayReciprocalᶜ-left


reciprocalPositiveᶜ-data-independent :
  (ε δ : ℚ⁺) →
  (x : ℝᶜ) →
  (xε : BoundedAwayPositiveᶜ ε x) →
  (xδ : BoundedAwayPositiveᶜ δ x) →
  reciprocalPositiveᶜ ε x xε ≡
  reciprocalPositiveᶜ δ x xδ
reciprocalPositiveᶜ-data-independent ε δ x xε xδ =
  right-inverse-uniqueᶜ
    {x = x}
    {y = reciprocalPositiveᶜ ε x xε}
    {z = reciprocalPositiveᶜ δ x xδ}
    (reciprocalPositiveᶜ-right ε x xε)
    (reciprocalPositiveᶜ-right δ x xδ)


reciprocalPositiveᶜ-nonnegative :
  (ε : ℚ⁺) →
  (x : ℝᶜ) →
  (x-bound : BoundedAwayPositiveᶜ ε x) →
  0ᶜ ≤ᶜ reciprocalPositiveᶜ ε x x-bound
reciprocalPositiveᶜ-nonnegative ε x x-bound =
  CauchyRealsOrdered.¬<→≥ {x = r} {y = 0ᶜ} not-r<0
  where
  r : ℝᶜ
  r =
    reciprocalPositiveᶜ ε x x-bound

  negative-zeroᶜ :
    -ᶜ 0ᶜ ≡ 0ᶜ
  negative-zeroᶜ =
    inverse-unique-right 0ᶜ 0ᶜ (add-zero-right 0ᶜ)

  x-positive :
    0ᶜ <ᶜ x
  x-positive =
    subst
      PositiveSepᶜ
      (sym (cong (x +ᶜ_) negative-zeroᶜ ∙ add-zero-right x))
      (boundedAwayPositiveᶜ→positiveSepᶜ x-bound)

  not-r<0 :
    ¬ (r <ᶜ 0ᶜ)
  not-r<0 r<0 =
    CauchyRealsOrdered.<-asym {x = 0ᶜ} {y = 1ᶜ} 0ᶜ<1ᶜ one<zero
    where
    r*x<0*x :
      r ·ᶜ x <ᶜ 0ᶜ ·ᶜ x
    r*x<0*x =
      mulᶜ-pres<ᶜ-right r 0ᶜ x x-positive r<0

    one<zero :
      1ᶜ <ᶜ 0ᶜ
    one<zero =
      subst2
        _<ᶜ_
        (reciprocalPositiveᶜ-left ε x x-bound)
        (mulᶜ-zero-left x)
        r*x<0*x


reciprocalPositiveᶜ-posInv-bound :
  (ε : ℚ⁺) →
  (x : ℝᶜ) →
  (x-bound : BoundedAwayPositiveᶜ ε x) →
  BoundedByᶜ
    (posInv⁺ ε)
    (reciprocalPositiveᶜ ε x x-bound)
reciprocalPositiveᶜ-posInv-bound ε x x-bound =
  bounded-byᶜ upper-bound lower-bound
  where
  r : ℝᶜ
  r =
    reciprocalPositiveᶜ ε x x-bound

  invε : ℚ
  invε =
    radius (posInv⁺ ε)

  r-nonnegative : 0ᶜ ≤ᶜ r
  r-nonnegative =
    reciprocalPositiveᶜ-nonnegative ε x x-bound

  invε-nonnegative : 0ᶜ ≤ᶜ rational invε
  invε-nonnegative =
    ≤ℚ→rational≤ᶜ
      {q = Rational.0ℚ}
      {r = invε}
      (Rational.<→≤
        {p = Rational.0ℚ}
        {q = invε}
        (posInv⁺ ε .snd))

  ε*r≤x*r :
    rational (radius ε) ·ᶜ r ≤ᶜ x ·ᶜ r
  ε*r≤x*r =
    mulᶜ-pres≤ᶜ-right
      (rational (radius ε))
      x
      r
      r-nonnegative
      (x-bound .BoundedAwayPositiveᶜ.lowerᶜ)

  ε*r≤1 :
    rational (radius ε) ·ᶜ r ≤ᶜ 1ᶜ
  ε*r≤1 =
    subst
      (λ θ → rational (radius ε) ·ᶜ r ≤ᶜ θ)
      (reciprocalPositiveᶜ-right ε x x-bound)
      ε*r≤x*r

  scaled≤ :
    (rational (radius ε) ·ᶜ r) ·ᶜ rational invε ≤ᶜ
    1ᶜ ·ᶜ rational invε
  scaled≤ =
    mulᶜ-pres≤ᶜ-right
      (rational (radius ε) ·ᶜ r)
      1ᶜ
      (rational invε)
      invε-nonnegative
      ε*r≤1

  left-path :
    (rational (radius ε) ·ᶜ r) ·ᶜ rational invε ≡ r
  left-path =
    sym (mulᶜ-assoc (rational (radius ε)) r (rational invε)) ∙
    cong (rational (radius ε) ·ᶜ_)
      (mulᶜ-comm r (rational invε)) ∙
    mulᶜ-assoc (rational (radius ε)) (rational invε) r ∙
    cong (_·ᶜ r)
      (mulᶜ-rational-rational (radius ε) invε ∙
       cong rational (Rational.posInv-right (radius ε) (ε .snd))) ∙
    mulᶜ-one-left r

  right-path :
    1ᶜ ·ᶜ rational invε ≡ rational invε
  right-path =
    mulᶜ-one-left (rational invε)

  upper-bound : r ≤ᶜ rational invε
  upper-bound =
    subst2 _≤ᶜ_ left-path right-path scaled≤

  lower-bound : (-ᶜ r) ≤ᶜ rational invε
  lower-bound =
    ≤ᶜ-trans
      (subst
        (λ θ → (-ᶜ r) ≤ᶜ θ)
        neg-zeroᶜ
        (negᶜ-pres≤ᶜ {x = 0ᶜ} {y = r} r-nonnegative))
      invε-nonnegative


divideByPositiveᶜ :
  ℝᶜ →
  (ε : ℚ⁺) →
  (y : ℝᶜ) →
  BoundedAwayPositiveᶜ ε y →
  ℝᶜ
divideByPositiveᶜ x ε y y-bound =
  x ·ᶜ reciprocalPositiveᶜ ε y y-bound


divideByPositiveᶜ-data-independent :
  (x : ℝᶜ) →
  (ε δ : ℚ⁺) →
  (y : ℝᶜ) →
  (yε : BoundedAwayPositiveᶜ ε y) →
  (yδ : BoundedAwayPositiveᶜ δ y) →
  divideByPositiveᶜ x ε y yε ≡
  divideByPositiveᶜ x δ y yδ
divideByPositiveᶜ-data-independent x ε δ y yε yδ =
  cong (x ·ᶜ_)
    (reciprocalPositiveᶜ-data-independent ε δ y yε yδ)


divideByPositiveᶜ-uniformModulus :
  ℚ⁺ →
  ℚ⁺ →
  PrecisionModulus
divideByPositiveᶜ-uniformModulus κ ε η =
  half⁺ (min⁺ numeratorSource denominatorSource)
  where
  α : ℚ⁺
  α =
    half⁺ η

  reciprocalBound : ℚ⁺
  reciprocalBound =
    reciprocalLipschitzBase⁺ (half⁺ ε)

  reciprocalPrecision : ℚ⁺
  reciprocalPrecision =
    half⁺ (posInv⁺ κ *⁺ α)

  numeratorSource : ℚ⁺
  numeratorSource =
    half⁺ (posInv⁺ reciprocalBound *⁺ α)

  denominatorSource : ℚ⁺
  denominatorSource =
    fst (boundedReciprocalᶜ-continuous (half⁺ ε)) reciprocalPrecision


divideByPositiveᶜ-uniformlyContinuousOnBounds :
  (κ ε : ℚ⁺) →
  Σ[ μ ∈ PrecisionModulus ]
    ((η : ℚ⁺) →
      {x x' y y' : ℝᶜ} →
      BoundedByᶜ κ x →
      BoundedByᶜ κ x' →
      (y-bound : BoundedAwayPositiveᶜ ε y) →
      (y'-bound : BoundedAwayPositiveᶜ ε y') →
      MetricSpace.Close CauchyRealsMetricSpace x (μ η) x' →
      MetricSpace.Close CauchyRealsMetricSpace y (μ η) y' →
      MetricSpace.Close CauchyRealsMetricSpace
        (divideByPositiveᶜ x ε y y-bound)
        η
        (divideByPositiveᶜ x' ε y' y'-bound))
divideByPositiveᶜ-uniformlyContinuousOnBounds κ ε =
  μ , closeAt
  where
  μ : PrecisionModulus
  μ =
    divideByPositiveᶜ-uniformModulus κ ε

  closeAt :
    (η : ℚ⁺) →
    {x x' y y' : ℝᶜ} →
    BoundedByᶜ κ x →
    BoundedByᶜ κ x' →
    (y-bound : BoundedAwayPositiveᶜ ε y) →
    (y'-bound : BoundedAwayPositiveᶜ ε y') →
    MetricSpace.Close CauchyRealsMetricSpace x (μ η) x' →
    MetricSpace.Close CauchyRealsMetricSpace y (μ η) y' →
    MetricSpace.Close CauchyRealsMetricSpace
      (divideByPositiveᶜ x ε y y-bound)
      η
      (divideByPositiveᶜ x' ε y' y'-bound)
  closeAt η {x = x} {x' = x'} {y = y} {y' = y'}
    xκ
    x'κ
    y-bound
    y'-bound
    x∼x'
    y∼y' =
    subst
      (λ θ →
        MetricSpace.Close CauchyRealsMetricSpace
          (divideByPositiveᶜ x ε y y-bound)
          θ
          (divideByPositiveᶜ x' ε y' y'-bound))
      (half⁺+half⁺≡ η)
      (MetricSpace.close-triangle CauchyRealsMetricSpace left-step right-step)
    where
    α : ℚ⁺
    α =
      half⁺ η

    reciprocalBound : ℚ⁺
    reciprocalBound =
      reciprocalLipschitzBase⁺ (half⁺ ε)

    reciprocalPrecision : ℚ⁺
    reciprocalPrecision =
      half⁺ (posInv⁺ κ *⁺ α)

    numeratorSource : ℚ⁺
    numeratorSource =
      half⁺ (posInv⁺ reciprocalBound *⁺ α)

    denominatorSource : ℚ⁺
    denominatorSource =
      fst (boundedReciprocalᶜ-continuous (half⁺ ε)) reciprocalPrecision

    r : ℝᶜ
    r =
      reciprocalPositiveᶜ ε y y-bound

    r-bound : BoundedByᶜ reciprocalBound r
    r-bound =
      reciprocalPositiveᶜ-bound ε y y-bound

    x-close :
      MetricSpace.Close CauchyRealsMetricSpace x numeratorSource x'
    x-close =
      MetricSpace.close-mono
        CauchyRealsMetricSpace
        (half-min⁺<left numeratorSource denominatorSource)
        x∼x'

    y-close :
      MetricSpace.Close CauchyRealsMetricSpace y denominatorSource y'
    y-close =
      MetricSpace.close-mono
        CauchyRealsMetricSpace
        (half-min⁺<right numeratorSource denominatorSource)
        y∼y'

    reciprocal-close :
      MetricSpace.Close CauchyRealsMetricSpace
        (reciprocalPositiveᶜ ε y y-bound)
        reciprocalPrecision
        (reciprocalPositiveᶜ ε y' y'-bound)
    reciprocal-close =
      snd (boundedReciprocalᶜ-continuous (half⁺ ε))
        reciprocalPrecision
        y-close

    left-step :
      MetricSpace.Close CauchyRealsMetricSpace
        (divideByPositiveᶜ x ε y y-bound)
        α
        (divideByPositiveᶜ x' ε y y-bound)
    left-step =
      MetricSpace.close-mono
        CauchyRealsMetricSpace
        (scale-half-inverse< reciprocalBound α)
        (mulᶜ-close-left-with-bound
          reciprocalBound
          r
          r-bound
          x-close)

    right-step :
      MetricSpace.Close CauchyRealsMetricSpace
        (divideByPositiveᶜ x' ε y y-bound)
        α
        (divideByPositiveᶜ x' ε y' y'-bound)
    right-step =
      MetricSpace.close-mono
        CauchyRealsMetricSpace
        (scale-half-inverse< κ α)
        (mulᶜ-close-right-with-bound
          κ
          x'
          x'κ
          reciprocal-close)


divideByPositiveᶜ-bound :
  (κ ε : ℚ⁺) →
  (x y : ℝᶜ) →
  BoundedByᶜ κ x →
  (y-bound : BoundedAwayPositiveᶜ ε y) →
  BoundedByᶜ
    (κ *⁺ reciprocalLipschitzBase⁺ (half⁺ ε))
    (divideByPositiveᶜ x ε y y-bound)
divideByPositiveᶜ-bound κ ε x y x-bound y-bound =
  bounded-byᶜ-mul
    κ
    (reciprocalLipschitzBase⁺ (half⁺ ε))
    x
    (reciprocalPositiveᶜ ε y y-bound)
    x-bound
    (reciprocalPositiveᶜ-bound ε y y-bound)


record PositiveBoundedDomainᶜ (x : ℝᶜ) : Type₀ where
  constructor positive-bounded-domainᶜ

  field
    lower : ℚ⁺
    upper : ℚ⁺
    lowerBound : BoundedAwayPositiveᶜ lower x
    upperBound : BoundedByᶜ upper x


open PositiveBoundedDomainᶜ public


oneBoundedᶜ :
  BoundedByᶜ 1⁺ 1ᶜ
oneBoundedᶜ =
  rational-closed-bound→boundedᶜ
    1⁺
    Rational.1ℚ
    (rational-closed-boundᶜ
      (Rational.≤-refl Rational.1ℚ)
      -1≤1)
  where
  -1≤1 :
    Rational.-1ℚ ℚOrder.≤ Rational.1ℚ
  -1≤1 =
    Rational.<→≤
      {p = Rational.-1ℚ}
      {q = Rational.1ℚ}
      (ℚOrder.isTrans<
        Rational.-1ℚ
        Rational.0ℚ
        Rational.1ℚ
        Rational.-1<0
        Rational.0<1)


positiveBoundedDomain-add-one :
  {x : ℝᶜ} →
  PositiveBoundedDomainᶜ x →
  PositiveBoundedDomainᶜ (x +ᶜ 1ᶜ)
positiveBoundedDomain-add-one {x = x} domain =
  positive-bounded-domainᶜ
    (lower domain +⁺ 1⁺)
    (upper domain +⁺ 1⁺)
    lower'
    upper'
  where
  lower' : BoundedAwayPositiveᶜ (lower domain +⁺ 1⁺) (x +ᶜ 1ᶜ)
  lower' =
    bounded-away-positiveᶜ
      (subst
        (λ y → y ≤ᶜ x +ᶜ 1ᶜ)
        (add-rational (radius (lower domain)) Rational.1ℚ)
        (≤ᶜ-add
          {a = rational (radius (lower domain))}
          {b = x}
          {c = 1ᶜ}
          {d = 1ᶜ}
          (lowerBound domain .BoundedAwayPositiveᶜ.lowerᶜ)
          (≤ᶜ-refl 1ᶜ)))

  upper' : BoundedByᶜ (upper domain +⁺ 1⁺) (x +ᶜ 1ᶜ)
  upper' =
    bounded-byᶜ-add
      (upper domain)
      1⁺
      x
      1ᶜ
      (upperBound domain)
      oneBoundedᶜ
