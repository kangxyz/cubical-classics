{-

Derivative of the global positive logarithm on an explicit positive window

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.GlobalDerivative where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.Derivative.Domain.Base
open import Constructive.Analysis.Reals.Calculus.Derivative.Domain.Rules
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedDivision
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.CommRing
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Inverse
  using (right-inverse-uniqueᶜ)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Derivative.Core
  using (atanhDerivativePowerSeriesReciprocalOnBall)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Arctangent.Derivative.Within
  using
    ( atanhWithinDerivativeModulus
    ; atanhᶜFromSubunitBoundHasDerivativeWithinDomainAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.Core
  using (onePlusStrictSubunitDomain)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.AtanhTransport
  using (atanhᶜFromSubunitBound-argument-path)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.Global
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


private
  module SolverHelpers {ℓ : Level} (𝒩 : CommRing ℓ) where
    open CommRingStr (𝒩 .snd)

    transform-remainder :
      (x h r s : 𝒩 .fst) →
      let
        two = 1r + 1r
        A = x + 1r
        B = (x + h) + 1r
        N = x + (- 1r)
        M = (x + h) + (- 1r)
        E₁ = (A · r) + (- 1r)
        E₂ = (B · s) + (- 1r)
        target = - (((((two · r) · r) · s) · h) · h)
      in
      (((M · s) + (- (N · r))) +
        (- (((two · r) · r) · h))) ≡
      target +
        ((E₁ · ((- 1r) + ((two · s) +
          (- (((two · r) · s) · h))))) +
         (E₂ · (1r + ((- (two · r)) +
          (((two · r) · r) · h)))))
    transform-remainder _ _ _ _ =
      solve! 𝒩

    one-minus-one :
      1r + (- 1r) ≡ 0r
    one-minus-one =
      solve! 𝒩

    remove-errors :
      (target c₁ c₂ : 𝒩 .fst) →
      target + ((0r · c₁) + (0r · c₂)) ≡ target
    remove-errors _ _ _ =
      solve! 𝒩

    factor-from-denominator :
      (x r : 𝒩 .fst) →
      let
        two = 1r + 1r
        denominator = x + 1r
        numerator = x + (- 1r)
      in
      ((denominator · r) · (denominator · r)) +
        (- ((numerator · r) · (numerator · r))) ≡
      (((two · (two · x)) · r) · r)
    factor-from-denominator _ _ =
      solve! 𝒩

    normalized-product :
      (x p r : 𝒩 .fst) →
      let two = 1r + 1r in
      x · (two · (p · ((two · r) · r))) ≡
      ((((two · (two · x)) · r) · r) · p)
    normalized-product _ _ _ =
      solve! 𝒩

  multiply-positive-left-≤ :
    {a b c : ℚ⁺} →
    radius a ℚOrder.≤ radius b →
    radius (c *⁺ a) ℚOrder.≤ radius (c *⁺ b)
  multiply-positive-left-≤ {a = a} {b = b} {c = c} a≤b =
    subst2
      ℚOrder._≤_
      (ℚ.·Comm (radius a) (radius c))
      (ℚ.·Comm (radius b) (radius c))
      (ℚOrder.≤-·o
        (radius a)
        (radius b)
        (radius c)
        (ℚOrder.<Weaken≤ Rational.0ℚ (radius c) (c .snd))
        a≤b)

  multiply-positive-right-≤ :
    {a b c : ℚ⁺} →
    radius a ℚOrder.≤ radius b →
    radius (a *⁺ c) ℚOrder.≤ radius (b *⁺ c)
  multiply-positive-right-≤ {a = a} {b = b} {c = c} a≤b =
    ℚOrder.≤-·o
      (radius a)
      (radius b)
      (radius c)
      (ℚOrder.<Weaken≤ Rational.0ℚ (radius c) (c .snd))
      a≤b

  scale-precision-cancel :
    (κ ε : ℚ⁺) →
    κ *⁺ (posInv⁺ κ *⁺ ε) ≡ ε
  scale-precision-cancel κ ε =
    sym (*⁺-assoc κ (posInv⁺ κ) ε) ∙
    cong (λ θ → θ *⁺ ε) (*⁺-posInv-right κ) ∙
    *⁺-identity-left ε


PositiveWindowᶜ :
  ℚ⁺ →
  ℚ⁺ →
  ℝᶜ →
  Type₀
PositiveWindowᶜ lo hi x =
  BoundedAwayPositiveᶜ lo x × BoundedByᶜ hi x


positiveWindowDomain :
  (lo hi : ℚ⁺) →
  (x : ℝᶜ) →
  PositiveWindowᶜ lo hi x →
  PositiveBoundedDomainᶜ x
positiveWindowDomain lo hi x window =
  positive-bounded-domainᶜ lo hi (window .fst) (window .snd)


logᶜ-positive-window :
  (lo hi : ℚ⁺) →
  (x : ℝᶜ) →
  PositiveWindowᶜ lo hi x →
  ℝᶜ
logᶜ-positive-window lo hi x window =
  logᶜ-positive-bounded x (positiveWindowDomain lo hi x window)


logᶜ-positive-bounded-data-independent :
  (x : ℝᶜ) →
  (left right : PositiveBoundedDomainᶜ x) →
  logᶜ-positive-bounded x left ≡
  logᶜ-positive-bounded x right
logᶜ-positive-bounded-data-independent x left right =
  cong
    (twoᶜ ·ᶜ_)
    (atanhᶜFromSubunitBound-argument-path
      leftRadius
      leftRadius<1
      transform-path
      leftTransformBound ∙
     atanhᶜFromSubunitBound-data-independent
      leftRadius
      rightRadius
      leftRadius<1
      rightRadius<1
      rightTransform
      (subst (BoundedByᶜ leftRadius) transform-path leftTransformBound)
      rightTransformBound)
  where
  leftData =
    logTransformSubunitBoundFromPositiveBoundedᶜ x left

  rightData =
    logTransformSubunitBoundFromPositiveBoundedᶜ x right

  leftDenominator =
    positiveBoundedDomain-add-one left

  rightDenominator =
    positiveBoundedDomain-add-one right

  leftTransform =
    logTransformᶜ x (lower leftDenominator) (lowerBound leftDenominator)

  rightTransform =
    logTransformᶜ x (lower rightDenominator) (lowerBound rightDenominator)

  transform-path : leftTransform ≡ rightTransform
  transform-path =
    logTransformᶜ-data-independent
      x
      (lower leftDenominator)
      (lower rightDenominator)
      (lowerBound leftDenominator)
      (lowerBound rightDenominator)

  leftRadius =
    transformRadius leftData

  rightRadius =
    transformRadius rightData

  leftRadius<1 =
    transformRadius<1 leftData

  rightRadius<1 =
    transformRadius<1 rightData

  leftTransformBound : BoundedByᶜ leftRadius leftTransform
  leftTransformBound =
    transformBound leftData

  rightTransformBound : BoundedByᶜ rightRadius rightTransform
  rightTransformBound =
    transformBound rightData


logᶜ-positive-window-data-independent :
  (lo hi : ℚ⁺) →
  DomainValueIndependent (logᶜ-positive-window lo hi)
logᶜ-positive-window-data-independent lo hi x left right =
  logᶜ-positive-bounded-data-independent
    x
    (positiveWindowDomain lo hi x left)
    (positiveWindowDomain lo hi x right)


logTransformWindow :
  (lo hi : ℚ⁺) →
  (x : ℝᶜ) →
  PositiveWindowᶜ lo hi x →
  ℝᶜ
logTransformWindow lo hi x window =
  logTransformᶜ
    x
    (lo +⁺ 1⁺)
    (lowerBound
      (positiveBoundedDomain-add-one
        (positiveWindowDomain lo hi x window)))


logTransformWindow-data-independent :
  (lo hi : ℚ⁺) →
  DomainValueIndependent (logTransformWindow lo hi)
logTransformWindow-data-independent lo hi x left right =
  logTransformᶜ-data-independent
    x
    (lo +⁺ 1⁺)
    (lo +⁺ 1⁺)
    (lowerBound
      (positiveBoundedDomain-add-one
        (positiveWindowDomain lo hi x left)))
    (lowerBound
      (positiveBoundedDomain-add-one
        (positiveWindowDomain lo hi x right)))


logTransformWindowBound :
  (lo hi : ℚ⁺) →
  (x : ℝᶜ) →
  (window : PositiveWindowᶜ lo hi x) →
  BoundedByᶜ
    (logTransformSubunitRadiusFromWindow lo hi)
    (logTransformWindow lo hi x window)
logTransformWindowBound lo hi x window =
  transformBound
    (logTransformSubunitBoundFromPositiveBoundedᶜ
      x
      (positiveWindowDomain lo hi x window))


logTransformWindowDerivativeValue :
  (lo hi : ℚ⁺) →
  (x : ℝᶜ) →
  PositiveWindowᶜ lo hi x →
  ℝᶜ
logTransformWindowDerivativeValue lo hi x window =
  (1ᶜ +ᶜ 1ᶜ) ·ᶜ reciprocal ·ᶜ reciprocal
  where
  denominator =
    x +ᶜ 1ᶜ

  denominator-away =
    lowerBound
      (positiveBoundedDomain-add-one
        (positiveWindowDomain lo hi x window))

  reciprocal =
    reciprocalPositiveᶜ (lo +⁺ 1⁺) denominator denominator-away


logTransformWindowDerivativeBoundRadius :
  ℚ⁺ →
  ℚ⁺
logTransformWindowDerivativeBoundRadius lo =
  ((1⁺ +⁺ 1⁺) *⁺ posInv⁺ (lo +⁺ 1⁺)) *⁺
  posInv⁺ (lo +⁺ 1⁺)


logTransformWindowDerivativeBound :
  (lo hi : ℚ⁺) →
  (x : ℝᶜ) →
  (window : PositiveWindowᶜ lo hi x) →
  BoundedByᶜ
    (logTransformWindowDerivativeBoundRadius lo)
    (logTransformWindowDerivativeValue lo hi x window)
logTransformWindowDerivativeBound lo hi x window =
  bounded-byᶜ-mul
    ((1⁺ +⁺ 1⁺) *⁺ invLower)
    invLower
    ((1ᶜ +ᶜ 1ᶜ) ·ᶜ reciprocal)
    reciprocal
    (bounded-byᶜ-mul
      (1⁺ +⁺ 1⁺)
      invLower
      (1ᶜ +ᶜ 1ᶜ)
      reciprocal
      (bounded-byᶜ-add 1⁺ 1⁺ 1ᶜ 1ᶜ oneBoundedᶜ oneBoundedᶜ)
      reciprocal-bound)
    reciprocal-bound
  where
  invLower =
    posInv⁺ (lo +⁺ 1⁺)

  denominator =
    x +ᶜ 1ᶜ

  denominator-away =
    lowerBound
      (positiveBoundedDomain-add-one
        (positiveWindowDomain lo hi x window))

  reciprocal =
    reciprocalPositiveᶜ (lo +⁺ 1⁺) denominator denominator-away

  reciprocal-bound : BoundedByᶜ invLower reciprocal
  reciprocal-bound =
    reciprocalPositiveᶜ-posInv-bound
      (lo +⁺ 1⁺)
      denominator
      denominator-away


logTransformWindowDerivativeModulus :
  ℚ⁺ →
  PrecisionModulus
logTransformWindowDerivativeModulus lo ε =
  posInv⁺ remainderScale *⁺ ε
  where
  invLower =
    posInv⁺ (lo +⁺ 1⁺)

  remainderScale =
    (((1⁺ +⁺ 1⁺) *⁺ invLower) *⁺ invLower) *⁺ invLower


logTransformWindowHasDerivativeWithinDomainAtWith :
  (lo hi : ℚ⁺) →
  (x : ℝᶜ) →
  (window : PositiveWindowᶜ lo hi x) →
  HasDerivativeWithinDomainAtWith
    (logTransformWindow lo hi)
    x
    window
    (logTransformWindowDerivativeValue lo hi x window)
    (logTransformWindowDerivativeModulus lo)
logTransformWindowHasDerivativeWithinDomainAtWith
    lo hi x window ε η η≤modulus h h-bound forward-window =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (sym remainder-path)
    target-bound
  where
  lowerDenominator =
    lo +⁺ 1⁺

  invLower =
    posInv⁺ lowerDenominator

  twoBound =
    1⁺ +⁺ 1⁺

  remainderScale =
    ((twoBound *⁺ invLower) *⁺ invLower) *⁺ invLower

  denominator =
    x +ᶜ 1ᶜ

  forward-denominator =
    (x +ᶜ h) +ᶜ 1ᶜ

  denominator-away =
    lowerBound
      (positiveBoundedDomain-add-one
        (positiveWindowDomain lo hi x window))

  forward-denominator-away =
    lowerBound
      (positiveBoundedDomain-add-one
        (positiveWindowDomain lo hi (x +ᶜ h) forward-window))

  r =
    reciprocalPositiveᶜ lowerDenominator denominator denominator-away

  s =
    reciprocalPositiveᶜ
      lowerDenominator forward-denominator forward-denominator-away

  r-bound : BoundedByᶜ invLower r
  r-bound =
    reciprocalPositiveᶜ-posInv-bound lowerDenominator denominator denominator-away

  s-bound : BoundedByᶜ invLower s
  s-bound =
    reciprocalPositiveᶜ-posInv-bound
      lowerDenominator forward-denominator forward-denominator-away

  unsigned-target =
    (((((1ᶜ +ᶜ 1ᶜ) ·ᶜ r) ·ᶜ r) ·ᶜ s) ·ᶜ h) ·ᶜ h

  target =
    -ᶜ unsigned-target

  unsigned-target-bound :
    BoundedByᶜ ((remainderScale *⁺ η) *⁺ η) unsigned-target
  unsigned-target-bound =
    bounded-byᶜ-mul
      (remainderScale *⁺ η)
      η
      (((((1ᶜ +ᶜ 1ᶜ) ·ᶜ r) ·ᶜ r) ·ᶜ s) ·ᶜ h)
      h
      (bounded-byᶜ-mul
        remainderScale
        η
        ((((1ᶜ +ᶜ 1ᶜ) ·ᶜ r) ·ᶜ r) ·ᶜ s)
        h
        (bounded-byᶜ-mul
          ((twoBound *⁺ invLower) *⁺ invLower)
          invLower
          (((1ᶜ +ᶜ 1ᶜ) ·ᶜ r) ·ᶜ r)
          s
          (bounded-byᶜ-mul
            (twoBound *⁺ invLower)
            invLower
            ((1ᶜ +ᶜ 1ᶜ) ·ᶜ r)
            r
            (bounded-byᶜ-mul
              twoBound
              invLower
              (1ᶜ +ᶜ 1ᶜ)
              r
              (bounded-byᶜ-add 1⁺ 1⁺ 1ᶜ 1ᶜ oneBoundedᶜ oneBoundedᶜ)
              r-bound)
            r-bound)
          s-bound)
        h-bound)
      h-bound

  target-raw-bound :
    BoundedByᶜ ((remainderScale *⁺ η) *⁺ η) target
  target-raw-bound =
    bounded-byᶜ-neg
      ((remainderScale *⁺ η) *⁺ η)
      unsigned-target
      unsigned-target-bound

  scale-times-η≤ε :
    radius (remainderScale *⁺ η) ℚOrder.≤ radius ε
  scale-times-η≤ε =
    subst
      (λ θ → radius (remainderScale *⁺ η) ℚOrder.≤ radius θ)
      (scale-precision-cancel remainderScale ε)
      (multiply-positive-left-≤ {c = remainderScale} η≤modulus)

  target-bound : BoundedByᶜ (ε *⁺ η) target
  target-bound =
    bounded-byᶜ-monotone
      (multiply-positive-right-≤
        {a = remainderScale *⁺ η}
        {b = ε}
        {c = η}
        scale-times-η≤ε)
      target-raw-bound

  error₁ =
    (denominator ·ᶜ r) +ᶜ (-ᶜ 1ᶜ)

  error₂ =
    (forward-denominator ·ᶜ s) +ᶜ (-ᶜ 1ᶜ)

  error₁-zero : error₁ ≡ 0ᶜ
  error₁-zero =
    cong (_+ᶜ (-ᶜ 1ᶜ))
      (reciprocalPositiveᶜ-right lowerDenominator denominator denominator-away) ∙
    SolverHelpers.one-minus-one CauchyRealsCommRing

  error₂-zero : error₂ ≡ 0ᶜ
  error₂-zero =
    cong (_+ᶜ (-ᶜ 1ᶜ))
      (reciprocalPositiveᶜ-right
        lowerDenominator forward-denominator forward-denominator-away) ∙
    SolverHelpers.one-minus-one CauchyRealsCommRing

  coefficient₁ =
    (-ᶜ 1ᶜ) +ᶜ (((1ᶜ +ᶜ 1ᶜ) ·ᶜ s) +ᶜ
      (-ᶜ ((((1ᶜ +ᶜ 1ᶜ) ·ᶜ r) ·ᶜ s) ·ᶜ h)))

  coefficient₂ =
    1ᶜ +ᶜ
      ((-ᶜ ((1ᶜ +ᶜ 1ᶜ) ·ᶜ r)) +ᶜ
       ((((1ᶜ +ᶜ 1ᶜ) ·ᶜ r) ·ᶜ r) ·ᶜ h))

  error-terms-zero :
    target +ᶜ ((error₁ ·ᶜ coefficient₁) +ᶜ (error₂ ·ᶜ coefficient₂)) ≡
    target
  error-terms-zero =
    cong₂
      (λ E₁ E₂ →
        target +ᶜ ((E₁ ·ᶜ coefficient₁) +ᶜ (E₂ ·ᶜ coefficient₂)))
      error₁-zero
      error₂-zero ∙
    SolverHelpers.remove-errors
      CauchyRealsCommRing target coefficient₁ coefficient₂

  remainder-path :
    withinDomainLinearRemainder
      (logTransformWindow lo hi)
      x
      window
      (logTransformWindowDerivativeValue lo hi x window)
      h
      forward-window
    ≡ target
  remainder-path =
    SolverHelpers.transform-remainder CauchyRealsCommRing x h r s ∙
    error-terms-zero


private
  windowTransformRadius :
    ℚ⁺ →
    ℚ⁺ →
    ℚ⁺
  windowTransformRadius =
    logTransformSubunitRadiusFromWindow

  windowTransformRadius<1 :
    (lo hi : ℚ⁺) →
    radius (windowTransformRadius lo hi) ℚOrder.< Rational.1ℚ
  windowTransformRadius<1 =
    logTransformSubunitRadiusFromWindow<1

  windowTransformSquaredRadius :
    ℚ⁺ →
    ℚ⁺ →
    ℚ⁺
  windowTransformSquaredRadius lo hi =
    windowTransformRadius lo hi *⁺ windowTransformRadius lo hi

  windowTransformSquaredRadius<1 :
    (lo hi : ℚ⁺) →
    radius (windowTransformSquaredRadius lo hi) ℚOrder.< Rational.1ℚ
  windowTransformSquaredRadius<1 lo hi =
    ℚOrder.isTrans<
      (radius qRadius ℚ.· radius qRadius)
      (radius qRadius)
      Rational.1ℚ
      square<radius
      qRadius<1
    where
    qRadius =
      windowTransformRadius lo hi

    qRadius<1 =
      windowTransformRadius<1 lo hi

    square<radius :
      radius qRadius ℚ.· radius qRadius ℚOrder.< radius qRadius
    square<radius =
      subst
        (λ t → radius qRadius ℚ.· radius qRadius ℚOrder.< t)
        (ℚ.·IdL (radius qRadius))
        (ℚOrder.<-·o
          (radius qRadius)
          Rational.1ℚ
          (radius qRadius)
          (qRadius .snd)
          qRadius<1)

  windowTransformFactorLower :
    ℚ⁺ →
    ℚ⁺ →
    ℚ⁺
  windowTransformFactorLower lo hi =
    1⁺ ⊖
    windowTransformSquaredRadius lo hi
    [ windowTransformSquaredRadius<1 lo hi ]

  windowTransformFactorDomain :
    (lo hi : ℚ⁺) →
    (x : ℝᶜ) →
    (window : PositiveWindowᶜ lo hi x) →
    PositiveBoundedDomainᶜ
      (1ᶜ +ᶜ
        (-ᶜ
          (logTransformWindow lo hi x window ·ᶜ
           logTransformWindow lo hi x window)))
  windowTransformFactorDomain lo hi x window =
    onePlusStrictSubunitDomain
      (windowTransformSquaredRadius lo hi)
      (windowTransformSquaredRadius<1 lo hi)
      (-ᶜ (transform ·ᶜ transform))
      (bounded-byᶜ-neg
        (windowTransformSquaredRadius lo hi)
        (transform ·ᶜ transform)
        (bounded-byᶜ-mul
          qRadius
          qRadius
          transform
          transform
          transform-bound
          transform-bound))
    where
    qRadius =
      windowTransformRadius lo hi

    transform =
      logTransformWindow lo hi x window

    transform-bound =
      logTransformWindowBound lo hi x window

  windowAtanhDerivativeValue :
    (lo hi : ℚ⁺) →
    (x : ℝᶜ) →
    (window : PositiveWindowᶜ lo hi x) →
    ℝᶜ
  windowAtanhDerivativeValue lo hi x window =
    reciprocalPositiveᶜ
      (lower factorDomain)
      factor
      (lowerBound factorDomain)
    where
    transform =
      logTransformWindow lo hi x window

    factor =
      1ᶜ +ᶜ (-ᶜ (transform ·ᶜ transform))

    factorDomain =
      windowTransformFactorDomain lo hi x window

  windowAtanhDerivative :
    (lo hi : ℚ⁺) →
    (x : ℝᶜ) →
    (window : PositiveWindowᶜ lo hi x) →
    let
      qRadius = windowTransformRadius lo hi
      qRadius<1 = windowTransformRadius<1 lo hi
      transform = logTransformWindow lo hi x window
      transform-bound = logTransformWindowBound lo hi x window
    in
    HasDerivativeWithinDomainAtWith
      (atanhᶜFromSubunitBound qRadius qRadius<1)
      transform
      transform-bound
      (windowAtanhDerivativeValue lo hi x window)
      (atanhWithinDerivativeModulus qRadius qRadius<1)
  windowAtanhDerivative lo hi x window =
    subst
      (λ d →
        HasDerivativeWithinDomainAtWith
          (atanhᶜFromSubunitBound qRadius qRadius<1)
          transform
          transform-bound
          d
          (atanhWithinDerivativeModulus qRadius qRadius<1))
      derivative-value-path
      (atanhᶜFromSubunitBoundHasDerivativeWithinDomainAtWith
        qRadius qRadius<1 transform transform-bound)
    where
    qRadius =
      windowTransformRadius lo hi

    qRadius<1 =
      windowTransformRadius<1 lo hi

    transform =
      logTransformWindow lo hi x window

    transform-bound =
      logTransformWindowBound lo hi x window

    factorDomain =
      windowTransformFactorDomain lo hi x window

    derivative-value-path =
      atanhDerivativePowerSeriesReciprocalOnBall
        qRadius
        qRadius<1
        transform
        transform-bound
        (lower factorDomain)
        (upper factorDomain)
        (lowerBound factorDomain)
        (upperBound factorDomain)

  logᶜ-positive-window-rawDerivativeModulus :
    (lo hi : ℚ⁺) →
    PrecisionModulus
  logᶜ-positive-window-rawDerivativeModulus lo hi ε =
    chainModulus (posInv⁺ two⁺ *⁺ ε)
    where
    qRadius =
      windowTransformRadius lo hi

    qRadius<1 =
      windowTransformRadius<1 lo hi

    chainModulus =
      domainChainDerivativeModulus
        (logTransformWindowDerivativeBoundRadius lo)
        (posInv⁺ (windowTransformFactorLower lo hi))
        (logTransformWindowDerivativeModulus lo)
        (atanhWithinDerivativeModulus qRadius qRadius<1)

  logᶜ-positive-window-rawDerivativeValue :
    (lo hi : ℚ⁺) →
    (x : ℝᶜ) →
    (window : PositiveWindowᶜ lo hi x) →
    ℝᶜ
  logᶜ-positive-window-rawDerivativeValue lo hi x window =
    twoᶜ ·ᶜ
      (windowAtanhDerivativeValue lo hi x window ·ᶜ
       logTransformWindowDerivativeValue lo hi x window)

  logᶜ-positive-window-rawDerivative :
    (lo hi : ℚ⁺) →
    (x : ℝᶜ) →
    (window : PositiveWindowᶜ lo hi x) →
    HasDerivativeWithinDomainAtWith
      (logᶜ-positive-window lo hi)
      x
      window
      (logᶜ-positive-window-rawDerivativeValue lo hi x window)
      (logᶜ-positive-window-rawDerivativeModulus lo hi)
  logᶜ-positive-window-rawDerivative lo hi x window =
    derivativeWithinDomainMulConstantLeftAtWith
      two⁺
      twoᶜ
      twoᶜ-bound
      (derivativeWithinDomainChainAtWith
        atanh-independent
        transform-domain
        (logTransformWindowDerivativeBoundRadius lo)
        (posInv⁺ factorLower)
        (logTransformWindowDerivativeBound lo hi x window)
        (reciprocalPositiveᶜ-posInv-bound
          factorLower
          factor
          factor-away)
        (logTransformWindowHasDerivativeWithinDomainAtWith lo hi x window)
        (windowAtanhDerivative lo hi x window))
    where
    qRadius =
      windowTransformRadius lo hi

    qRadius<1 =
      windowTransformRadius<1 lo hi

    transform =
      logTransformWindow lo hi x window

    factorDomain =
      windowTransformFactorDomain lo hi x window

    factorLower =
      lower factorDomain

    factor =
      1ᶜ +ᶜ (-ᶜ (transform ·ᶜ transform))

    factor-away =
      lowerBound factorDomain

    atanh-independent :
      DomainValueIndependent
        (atanhᶜFromSubunitBound qRadius qRadius<1)
    atanh-independent z left right =
      atanhᶜFromSubunitBound-data-independent
        qRadius qRadius qRadius<1 qRadius<1 z left right

    transform-domain :
      (y : ℝᶜ) →
      (y-window : PositiveWindowᶜ lo hi y) →
      BoundedByᶜ qRadius (logTransformWindow lo hi y y-window)
    transform-domain =
      logTransformWindowBound lo hi

  logᶜ-positive-window-rawDerivativeRightInverse :
    (lo hi : ℚ⁺) →
    (x : ℝᶜ) →
    (window : PositiveWindowᶜ lo hi x) →
    x ·ᶜ logᶜ-positive-window-rawDerivativeValue lo hi x window ≡ 1ᶜ
  logᶜ-positive-window-rawDerivativeRightInverse lo hi x window =
    SolverHelpers.normalized-product CauchyRealsCommRing x p r ∙
    cong (_·ᶜ p) (sym factor-path) ∙
    reciprocalPositiveᶜ-right factorLower factor factor-away
    where
    denominator =
      x +ᶜ 1ᶜ

    denominator-away =
      lowerBound
        (positiveBoundedDomain-add-one
          (positiveWindowDomain lo hi x window))

    r =
      reciprocalPositiveᶜ (lo +⁺ 1⁺) denominator denominator-away

    denominator-square-path :
      (denominator ·ᶜ r) ·ᶜ (denominator ·ᶜ r) ≡ 1ᶜ
    denominator-square-path =
      cong₂
        _·ᶜ_
        (reciprocalPositiveᶜ-right (lo +⁺ 1⁺) denominator denominator-away)
        (reciprocalPositiveᶜ-right (lo +⁺ 1⁺) denominator denominator-away) ∙
      mulᶜ-one-left 1ᶜ

    transform =
      logTransformWindow lo hi x window

    factorDomain =
      windowTransformFactorDomain lo hi x window

    factorLower =
      lower factorDomain

    factor =
      1ᶜ +ᶜ (-ᶜ (transform ·ᶜ transform))

    factor-away =
      lowerBound factorDomain

    factor-path :
      factor ≡
      ((((1ᶜ +ᶜ 1ᶜ) ·ᶜ ((1ᶜ +ᶜ 1ᶜ) ·ᶜ x)) ·ᶜ r) ·ᶜ r)
    factor-path =
      cong
        (λ one →
          one +ᶜ
          (-ᶜ (((x +ᶜ (-ᶜ 1ᶜ)) ·ᶜ r) ·ᶜ
                 ((x +ᶜ (-ᶜ 1ᶜ)) ·ᶜ r))))
        (sym denominator-square-path) ∙
      SolverHelpers.factor-from-denominator CauchyRealsCommRing x r

    p =
      reciprocalPositiveᶜ factorLower factor factor-away

  logᶜ-positive-window-rawDerivativeValuePath :
    (lo hi : ℚ⁺) →
    (x : ℝᶜ) →
    (window : PositiveWindowᶜ lo hi x) →
    logᶜ-positive-window-rawDerivativeValue lo hi x window ≡
    reciprocalPositiveᶜ lo x (window .fst)
  logᶜ-positive-window-rawDerivativeValuePath lo hi x window =
    right-inverse-uniqueᶜ
      (logᶜ-positive-window-rawDerivativeRightInverse lo hi x window)
      (reciprocalPositiveᶜ-right lo x (window .fst))


logᶜ-positive-windowDerivativeModulus :
  (lo hi : ℚ⁺) →
  PrecisionModulus
logᶜ-positive-windowDerivativeModulus =
  logᶜ-positive-window-rawDerivativeModulus


logᶜ-positive-windowHasDerivativeWithinDomainAtWith :
  (lo hi : ℚ⁺) →
  (x : ℝᶜ) →
  (window : PositiveWindowᶜ lo hi x) →
  HasDerivativeWithinDomainAtWith
    (logᶜ-positive-window lo hi)
    x
    window
    (reciprocalPositiveᶜ lo x (window .fst))
    (logᶜ-positive-windowDerivativeModulus lo hi)
logᶜ-positive-windowHasDerivativeWithinDomainAtWith lo hi x window =
  subst
    (λ d →
      HasDerivativeWithinDomainAtWith
        (logᶜ-positive-window lo hi)
        x
        window
        d
        (logᶜ-positive-windowDerivativeModulus lo hi))
    (logᶜ-positive-window-rawDerivativeValuePath lo hi x window)
    (logᶜ-positive-window-rawDerivative lo hi x window)
