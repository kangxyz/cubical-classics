{-

Uniform derivative of the logarithmic transform quotient x/(2+x)

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.FunctionalEquation.QuotientDerivative where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.DomainDerivative
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedDivision
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Structures
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.DomainScaling
  using
    ( divideByPositiveStrictSubunitRadius
    ; divideByPositiveStrictSubunitRadius<1
    ; divideByPositiveᶜ-strictSubunitBound
    )
open import Constructive.Analysis.Reals.PowerSeries.Elementary.Logarithm.FunctionalEquation.Algebra
  using (onePlusStrictSubunitDomain)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


private
  module SolverHelpers {ℓ : Level} (𝒩 : CommRing ℓ) where
    open CommRingStr (𝒩 .snd)

    quotient-remainder-decomposition :
      (x h r s : 𝒩 .fst) →
      let
        two = 1r + 1r
        A = (1r + x) + 1r
        B = (1r + (x + h)) + 1r
        E₁ = (A · r) + (- 1r)
        E₂ = (B · s) + (- 1r)
        target = - (((((two · r) · r) · s) · h) · h)
      in
      ((((x + h) · s) + (- (x · r))) +
        (- (((two · r) · r) · h))) ≡
      target +
        ((E₁ · ((- 1r) + ((two · s) +
          (- (((two · r) · s) · h))))) +
         (E₂ · (1r + ((- (two · r)) +
          (((two · r) · r) · h)))))
    quotient-remainder-decomposition _ _ _ _ =
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

logTransformQuotientDenominatorLower :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  ℚ⁺
logTransformQuotientDenominatorLower ρ ρ<1 =
  (1⁺ ⊖ ρ [ ρ<1 ]) +⁺ 1⁺


logTransformQuotientRadius :
  (ρ : ℚ⁺) →
  (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  ℚ⁺
logTransformQuotientRadius ρ rho<1 =
  divideByPositiveStrictSubunitRadius
    ρ
    (logTransformQuotientDenominatorLower ρ rho<1)


private
  radius<denominatorLower :
    (ρ : ℚ⁺) →
    (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
    radius ρ ℚOrder.<
    radius (logTransformQuotientDenominatorLower ρ rho<1)
  radius<denominatorLower ρ rho<1 =
    ℚOrder.isTrans<
      (radius ρ)
      Rational.1ℚ
      (radius (logTransformQuotientDenominatorLower ρ rho<1))
      rho<1
      (summand-right<sum (1⁺ ⊖ ρ [ rho<1 ]) 1⁺)


logTransformQuotientRadius<1 :
  (ρ : ℚ⁺) →
  (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  radius (logTransformQuotientRadius ρ rho<1) ℚOrder.< Rational.1ℚ
logTransformQuotientRadius<1 ρ rho<1 =
  divideByPositiveStrictSubunitRadius<1
    ρ
    (logTransformQuotientDenominatorLower ρ rho<1)
    (radius<denominatorLower ρ rho<1)


logTransformQuotientDenominatorDomain :
  (ρ : ℚ⁺) →
  (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (x : ℝᶜ) →
  BoundedByᶜ ρ x →
  PositiveBoundedDomainᶜ ((1ᶜ +ᶜ x) +ᶜ 1ᶜ)
logTransformQuotientDenominatorDomain ρ rho<1 x x-bound =
  positiveBoundedDomain-add-one
    (onePlusStrictSubunitDomain ρ rho<1 x x-bound)


logTransformQuotientDenominatorAway :
  (ρ : ℚ⁺) →
  (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (x : ℝᶜ) →
  (x-bound : BoundedByᶜ ρ x) →
  BoundedAwayPositiveᶜ
    (logTransformQuotientDenominatorLower ρ rho<1)
    ((1ᶜ +ᶜ x) +ᶜ 1ᶜ)
logTransformQuotientDenominatorAway ρ rho<1 x x-bound =
  lowerBound (logTransformQuotientDenominatorDomain ρ rho<1 x x-bound)


logTransformQuotient :
  (ρ : ℚ⁺) →
  (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (x : ℝᶜ) →
  BoundedByᶜ ρ x →
  ℝᶜ
logTransformQuotient ρ rho<1 x x-bound =
  divideByPositiveᶜ
    x
    (logTransformQuotientDenominatorLower ρ rho<1)
    ((1ᶜ +ᶜ x) +ᶜ 1ᶜ)
    (logTransformQuotientDenominatorAway ρ rho<1 x x-bound)




logTransformQuotient-zero :
  (ρ : ℚ⁺) →
  (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (zero-bound : BoundedByᶜ ρ 0ᶜ) →
  logTransformQuotient ρ rho<1 0ᶜ zero-bound ≡ 0ᶜ
logTransformQuotient-zero ρ rho<1 zero-bound =
  mulᶜ-zero-left
    (reciprocalPositiveᶜ
      (logTransformQuotientDenominatorLower ρ rho<1)
      ((1ᶜ +ᶜ 0ᶜ) +ᶜ 1ᶜ)
      (logTransformQuotientDenominatorAway ρ rho<1 0ᶜ zero-bound))


logTransformQuotientBound :
  (ρ : ℚ⁺) →
  (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (x : ℝᶜ) →
  (x-bound : BoundedByᶜ ρ x) →
  BoundedByᶜ
    (logTransformQuotientRadius ρ rho<1)
    (logTransformQuotient ρ rho<1 x x-bound)
logTransformQuotientBound ρ rho<1 x x-bound =
  divideByPositiveᶜ-strictSubunitBound
    ρ
    (logTransformQuotientDenominatorLower ρ rho<1)
    (radius<denominatorLower ρ rho<1)
    x
    ((1ᶜ +ᶜ x) +ᶜ 1ᶜ)
    x-bound
    (logTransformQuotientDenominatorAway ρ rho<1 x x-bound)


logTransformQuotientDerivativeValue :
  (ρ : ℚ⁺) →
  (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (x : ℝᶜ) →
  (x-bound : BoundedByᶜ ρ x) →
  ℝᶜ
logTransformQuotientDerivativeValue ρ rho<1 x x-bound =
  (1ᶜ +ᶜ 1ᶜ) ·ᶜ reciprocal ·ᶜ reciprocal
  where
  reciprocal : ℝᶜ
  reciprocal =
    reciprocalPositiveᶜ
      (logTransformQuotientDenominatorLower ρ rho<1)
      ((1ᶜ +ᶜ x) +ᶜ 1ᶜ)
      (logTransformQuotientDenominatorAway ρ rho<1 x x-bound)


logTransformQuotientDerivativeBoundRadius :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  ℚ⁺
logTransformQuotientDerivativeBoundRadius ρ rho<1 =
  ((1⁺ +⁺ 1⁺) *⁺ posInv⁺ denominatorLower) *⁺ posInv⁺ denominatorLower
  where
  denominatorLower : ℚ⁺
  denominatorLower =
    logTransformQuotientDenominatorLower ρ rho<1


logTransformQuotientDerivativeBound :
  (ρ : ℚ⁺) →
  (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (x : ℝᶜ) →
  (x-bound : BoundedByᶜ ρ x) →
  BoundedByᶜ
    (logTransformQuotientDerivativeBoundRadius ρ rho<1)
    (logTransformQuotientDerivativeValue ρ rho<1 x x-bound)
logTransformQuotientDerivativeBound ρ rho<1 x x-bound =
  bounded-byᶜ-mul
    ((1⁺ +⁺ 1⁺) *⁺ posInv⁺ denominatorLower)
    (posInv⁺ denominatorLower)
    ((1ᶜ +ᶜ 1ᶜ) ·ᶜ reciprocal)
    reciprocal
    (bounded-byᶜ-mul
      (1⁺ +⁺ 1⁺)
      (posInv⁺ denominatorLower)
      (1ᶜ +ᶜ 1ᶜ)
      reciprocal
      (bounded-byᶜ-add 1⁺ 1⁺ 1ᶜ 1ᶜ oneBoundedᶜ oneBoundedᶜ)
      reciprocal-bound)
    reciprocal-bound
  where
  denominatorLower : ℚ⁺
  denominatorLower =
    logTransformQuotientDenominatorLower ρ rho<1

  reciprocal =
    reciprocalPositiveᶜ
      denominatorLower
      ((1ᶜ +ᶜ x) +ᶜ 1ᶜ)
      (logTransformQuotientDenominatorAway ρ rho<1 x x-bound)

  reciprocal-bound : BoundedByᶜ (posInv⁺ denominatorLower) reciprocal
  reciprocal-bound =
    reciprocalPositiveᶜ-posInv-bound
      denominatorLower
      ((1ᶜ +ᶜ x) +ᶜ 1ᶜ)
      (logTransformQuotientDenominatorAway ρ rho<1 x x-bound)


logTransformQuotientDerivativeModulus :
  (ρ : ℚ⁺) →
  radius ρ ℚOrder.< Rational.1ℚ →
  PrecisionModulus
logTransformQuotientDerivativeModulus ρ rho<1 ε =
  posInv⁺ remainderScale *⁺ ε
  where
  denominatorLower : ℚ⁺
  denominatorLower =
    logTransformQuotientDenominatorLower ρ rho<1

  remainderScale : ℚ⁺
  remainderScale =
    (((1⁺ +⁺ 1⁺) *⁺ posInv⁺ denominatorLower) *⁺ posInv⁺ denominatorLower) *⁺
    posInv⁺ denominatorLower


logTransformQuotientHasDerivativeWithinDomainAtWith :
  (ρ : ℚ⁺) →
  (rho<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (x : ℝᶜ) →
  (x-bound : BoundedByᶜ ρ x) →
  HasDerivativeWithinDomainAtWith
    {D = BoundedByᶜ ρ}
    (logTransformQuotient ρ rho<1)
    x
    x-bound
    (logTransformQuotientDerivativeValue ρ rho<1 x x-bound)
    (logTransformQuotientDerivativeModulus ρ rho<1)
logTransformQuotientHasDerivativeWithinDomainAtWith
  ρ
  rho<1
  x
  x-bound
  ε
  η
  η≤modulus
  h
  h-bound
  forward-bound =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (sym remainder-path)
    target-bound
  where
  denominatorLower : ℚ⁺
  denominatorLower =
    logTransformQuotientDenominatorLower ρ rho<1

  invLower : ℚ⁺
  invLower =
    posInv⁺ denominatorLower

  twoBound : ℚ⁺
  twoBound =
    1⁺ +⁺ 1⁺

  remainderScale : ℚ⁺
  remainderScale =
    ((twoBound *⁺ invLower) *⁺ invLower) *⁺ invLower

  denominator =
    (1ᶜ +ᶜ x) +ᶜ 1ᶜ

  forward-denominator =
    (1ᶜ +ᶜ (x +ᶜ h)) +ᶜ 1ᶜ

  denominator-away =
    logTransformQuotientDenominatorAway ρ rho<1 x x-bound

  forward-denominator-away =
    logTransformQuotientDenominatorAway
      ρ rho<1 (x +ᶜ h) forward-bound

  r =
    reciprocalPositiveᶜ denominatorLower denominator denominator-away

  s =
    reciprocalPositiveᶜ denominatorLower forward-denominator forward-denominator-away

  r-bound : BoundedByᶜ invLower r
  r-bound =
    reciprocalPositiveᶜ-posInv-bound denominatorLower denominator denominator-away

  s-bound : BoundedByᶜ invLower s
  s-bound =
    reciprocalPositiveᶜ-posInv-bound
      denominatorLower forward-denominator forward-denominator-away

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
              (bounded-byᶜ-add
                1⁺ 1⁺ 1ᶜ 1ᶜ oneBoundedᶜ oneBoundedᶜ)
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
      (scale-posInv-cancel remainderScale ε)
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
      (reciprocalPositiveᶜ-right denominatorLower denominator denominator-away) ∙
    SolverHelpers.one-minus-one CauchyRealsCommRing

  error₂-zero : error₂ ≡ 0ᶜ
  error₂-zero =
    cong (_+ᶜ (-ᶜ 1ᶜ))
      (reciprocalPositiveᶜ-right
        denominatorLower forward-denominator forward-denominator-away) ∙
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
      (logTransformQuotient ρ rho<1)
      x
      x-bound
      (logTransformQuotientDerivativeValue ρ rho<1 x x-bound)
      h
      forward-bound
    ≡ target
  remainder-path =
    SolverHelpers.quotient-remainder-decomposition
      CauchyRealsCommRing x h r s ∙
    error-terms-zero
