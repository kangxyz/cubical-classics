{-

Local algebra needed for logarithm functional equations

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.Core where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedDivision
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.CommRing
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
  using (≤ᶜ-add ; negᶜ-pres≤ᶜ)
open import
  Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.FunctionalEquation.AtanhTransport
  using (atanhᶜFromSubunitBound-argument-path)
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.DomainScaling
open import Constructive.Analysis.Reals.PowerSeries.Instances.Logarithm.Global
  using
    ( LogDomainᶜ
    ; atanhᶜFromSubunitBound
    ; denominatorBound
    ; denominatorLower
    ; log-domain-from-positive-boundedᶜ
    ; logTransformᶜ
    ; logᶜ-positive-bounded
    ; twoᶜ
    ; transformBound
    ; transformRadius
    ; transformRadius<1
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius
  using
    ( InPowerSeriesBall
    ; inPowerSeriesBallAtZeroFromBound
    )
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    denominator-one-plus-quotient :
      (c h r : 𝓡 .fst) →
      c · (1r + h · r) ≡ c + h · (c · r)
    denominator-one-plus-quotient _ _ _ =
      solve! 𝓡

    divide-add-numerator :
      (c h r : 𝓡 .fst) →
      (c + h) · r ≡ (c · r) + (h · r)
    divide-add-numerator _ _ _ =
      solve! 𝓡

    log-transform-one-plus-numerator :
      (u : 𝓡 .fst) →
      (1r + u) + (- 1r) ≡ u
    log-transform-one-plus-numerator _ =
      solve! 𝓡

    log-transform-one-plus-denominator :
      (u : 𝓡 .fst) →
      (1r + u) + 1r ≡ (1r + 1r) + u
    log-transform-one-plus-denominator _ =
      solve! 𝓡

    one-minus-one :
      1r + (- 1r) ≡ 0r
    one-minus-one =
      solve! 𝓡

  divideByPositiveᶜ-denominator-path :
    (x : ℝᶜ) →
    (ε : ℚ⁺) →
    (y z : ℝᶜ) →
    (p : y ≡ z) →
    (y-bound : BoundedAwayPositiveᶜ ε y) →
    divideByPositiveᶜ x ε y y-bound ≡
    divideByPositiveᶜ x ε z (subst (BoundedAwayPositiveᶜ ε) p y-bound)
  divideByPositiveᶜ-denominator-path x ε y z p y-bound =
    subst
      (λ t →
        (t-bound : BoundedAwayPositiveᶜ ε t) →
        divideByPositiveᶜ x ε y y-bound ≡
        divideByPositiveᶜ x ε t t-bound)
      p
      (λ _ → refl)
      (subst (BoundedAwayPositiveᶜ ε) p y-bound)

  divideByPositiveᶜ-zero-left :
    (ε : ℚ⁺) →
    (y : ℝᶜ) →
    (y-bound : BoundedAwayPositiveᶜ ε y) →
    divideByPositiveᶜ 0ᶜ ε y y-bound ≡ 0ᶜ
  divideByPositiveᶜ-zero-left ε y y-bound =
    mulᶜ-zero-left (reciprocalPositiveᶜ ε y y-bound)

  rational-subunit-path :
    (α : ℚ⁺) →
    (α<1 : radius α ℚOrder.< Rational.1ℚ) →
    rational (radius (1⁺ ⊖ α [ α<1 ])) ≡
    1ᶜ +ᶜ (-ᶜ rational (radius α))
  rational-subunit-path α α<1 =
    add-rational Rational.1ℚ (ℚ.- radius α) ∙
    cong (1ᶜ +ᶜ_) (sym (neg-rational (radius α)))


boundedAwayPositiveOneMinusFromSubunitBound :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (x : ℝᶜ) →
  BoundedByᶜ ρ x →
  BoundedAwayPositiveᶜ
    (1⁺ ⊖ ρ [ ρ<1 ])
    (1ᶜ +ᶜ (-ᶜ x))
boundedAwayPositiveOneMinusFromSubunitBound ρ ρ<1 x x-bound =
  bounded-away-positiveᶜ
    (subst
      (λ y → y ≤ᶜ 1ᶜ +ᶜ (-ᶜ x))
      (rational-subunit-path ρ ρ<1)
      (≤ᶜ-add
        {a = 1ᶜ}
        {b = 1ᶜ}
        {c = -ᶜ rational (radius ρ)}
        {d = -ᶜ x}
        (≤ᶜ-refl 1ᶜ)
        (negᶜ-pres≤ᶜ
          {x = x}
          {y = rational (radius ρ)}
          (upperᶜ x-bound))))


onePlusStrictSubunitDomain :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (u : ℝᶜ) →
  BoundedByᶜ ρ u →
  PositiveBoundedDomainᶜ (1ᶜ +ᶜ u)
onePlusStrictSubunitDomain ρ ρ<1 u u-bound =
  positive-bounded-domainᶜ
    (1⁺ ⊖ ρ [ ρ<1 ])
    (1⁺ +⁺ ρ)
    lower'
    upper'
  where
  lower₀ :
    BoundedAwayPositiveᶜ
      (1⁺ ⊖ ρ [ ρ<1 ])
      (1ᶜ +ᶜ (-ᶜ (-ᶜ u)))
  lower₀ =
    boundedAwayPositiveOneMinusFromSubunitBound
      ρ
      ρ<1
      (-ᶜ u)
      (bounded-byᶜ-neg ρ u u-bound)

  lower' :
    BoundedAwayPositiveᶜ
      (1⁺ ⊖ ρ [ ρ<1 ])
      (1ᶜ +ᶜ u)
  lower' =
    subst
      (BoundedAwayPositiveᶜ (1⁺ ⊖ ρ [ ρ<1 ]))
      (cong (1ᶜ +ᶜ_) (neg-involutive u))
      lower₀

  upper' :
    BoundedByᶜ (1⁺ +⁺ ρ) (1ᶜ +ᶜ u)
  upper' =
    bounded-byᶜ-add
      1⁺
      ρ
      1ᶜ
      u
      oneBoundedᶜ
      u-bound


divideByPositiveᶜ-strictSubunitInBallZero :
  (ρ cLower : ℚ⁺) →
  radius ρ ℚOrder.< radius cLower →
  (h c : ℝᶜ) →
  BoundedByᶜ ρ h →
  (c-bound : BoundedAwayPositiveᶜ cLower c) →
  InPowerSeriesBall
    0ᶜ
    (divideByPositiveStrictSubunitRadius ρ cLower)
    (divideByPositiveᶜ h cLower c c-bound)
divideByPositiveᶜ-strictSubunitInBallZero
    ρ
    cLower
    ρ<cLower
    h
    c
    h-bound
    c-bound =
  inPowerSeriesBallAtZeroFromBound
    (divideByPositiveᶜ-strictSubunitBound
      ρ
      cLower
      ρ<cLower
      h
      c
      h-bound
      c-bound)


onePlusDivideByPositiveᶜ-domain :
  (ρ cLower : ℚ⁺) →
  radius ρ ℚOrder.< radius cLower →
  (h c : ℝᶜ) →
  BoundedByᶜ ρ h →
  (c-bound : BoundedAwayPositiveᶜ cLower c) →
  PositiveBoundedDomainᶜ
    (1ᶜ +ᶜ divideByPositiveᶜ h cLower c c-bound)
onePlusDivideByPositiveᶜ-domain
    ρ
    cLower
    ρ<cLower
    h
    c
    h-bound
    c-bound =
  onePlusStrictSubunitDomain
    (divideByPositiveStrictSubunitRadius ρ cLower)
    (divideByPositiveStrictSubunitRadius<1 ρ cLower ρ<cLower)
    (divideByPositiveᶜ h cLower c c-bound)
    (divideByPositiveᶜ-strictSubunitBound
      ρ
      cLower
      ρ<cLower
      h
      c
      h-bound
      c-bound)


positiveDivision-denominatorMulOnePlus-path :
  (cLower : ℚ⁺) →
  (c h : ℝᶜ) →
  (c-bound : BoundedAwayPositiveᶜ cLower c) →
  c ·ᶜ (1ᶜ +ᶜ divideByPositiveᶜ h cLower c c-bound) ≡
  c +ᶜ h
positiveDivision-denominatorMulOnePlus-path cLower c h c-bound =
  SolverHelpers.denominator-one-plus-quotient
    CauchyRealsCommRing
    c
    h
    r ∙
  cong (c +ᶜ_)
    (cong (h ·ᶜ_)
      (reciprocalPositiveᶜ-right cLower c c-bound) ∙
     mulᶜ-one-right h)
  where
  r : ℝᶜ
  r =
    reciprocalPositiveᶜ cLower c c-bound


positiveDivision-add-numerator-path :
  (cLower : ℚ⁺) →
  (c h : ℝᶜ) →
  (c-bound : BoundedAwayPositiveᶜ cLower c) →
  divideByPositiveᶜ (c +ᶜ h) cLower c c-bound ≡
  1ᶜ +ᶜ divideByPositiveᶜ h cLower c c-bound
positiveDivision-add-numerator-path cLower c h c-bound =
  SolverHelpers.divide-add-numerator
    CauchyRealsCommRing
    c
    h
    r ∙
  cong (_+ᶜ (h ·ᶜ r))
    (reciprocalPositiveᶜ-right cLower c c-bound)
  where
  r : ℝᶜ
  r =
    reciprocalPositiveᶜ cLower c c-bound


positiveDivision-onePlusQuotient-path :
  (cLower : ℚ⁺) →
  (c h : ℝᶜ) →
  (c-bound : BoundedAwayPositiveᶜ cLower c) →
  1ᶜ +ᶜ divideByPositiveᶜ h cLower c c-bound ≡
  divideByPositiveᶜ (c +ᶜ h) cLower c c-bound
positiveDivision-onePlusQuotient-path cLower c h c-bound =
  sym (positiveDivision-add-numerator-path cLower c h c-bound)


logTransformᶜ-onePlus-path :
  (u : ℝᶜ) →
  (denomLower : ℚ⁺) →
  (denomBound :
    BoundedAwayPositiveᶜ denomLower ((1ᶜ +ᶜ u) +ᶜ 1ᶜ)) →
  logTransformᶜ
    (1ᶜ +ᶜ u)
    denomLower
    denomBound
  ≡
  divideByPositiveᶜ
    u
    denomLower
    ((1ᶜ +ᶜ u) +ᶜ 1ᶜ)
    denomBound
logTransformᶜ-onePlus-path u denomLower denomBound =
  cong
    (λ numerator →
      divideByPositiveᶜ
        numerator
        denomLower
        ((1ᶜ +ᶜ u) +ᶜ 1ᶜ)
        denomBound)
    (SolverHelpers.log-transform-one-plus-numerator
      CauchyRealsCommRing
      u)


logTransformᶜ-onePlus-denominator-path :
  (u : ℝᶜ) →
  ((1ᶜ +ᶜ u) +ᶜ 1ᶜ) ≡ twoᶜ +ᶜ u
logTransformᶜ-onePlus-denominator-path u =
  SolverHelpers.log-transform-one-plus-denominator
    CauchyRealsCommRing
    u ∙
  cong (_+ᶜ u) (add-rational Rational.1ℚ Rational.1ℚ)


logTransformᶜ-onePlus-twoPlus-path :
  (u : ℝᶜ) →
  (denomLower : ℚ⁺) →
  (denomBound :
    BoundedAwayPositiveᶜ denomLower ((1ᶜ +ᶜ u) +ᶜ 1ᶜ)) →
  logTransformᶜ
    (1ᶜ +ᶜ u)
    denomLower
    denomBound
  ≡
  divideByPositiveᶜ
    u
    denomLower
    (twoᶜ +ᶜ u)
    (subst
      (BoundedAwayPositiveᶜ denomLower)
      (logTransformᶜ-onePlus-denominator-path u)
      denomBound)
logTransformᶜ-onePlus-twoPlus-path u denomLower denomBound =
  logTransformᶜ-onePlus-path u denomLower denomBound ∙
  divideByPositiveᶜ-denominator-path
    u
    denomLower
    ((1ᶜ +ᶜ u) +ᶜ 1ᶜ)
    (twoᶜ +ᶜ u)
    (logTransformᶜ-onePlus-denominator-path u)
    denomBound


logOnePlusᶜWithinSubunitBall-global :
  (ρ : ℚ⁺) →
  (ρ<1 : radius ρ ℚOrder.< Rational.1ℚ) →
  (u : ℝᶜ) →
  (u-bound : BoundedByᶜ ρ u) →
  let
    domain =
      log-domain-from-positive-boundedᶜ
        (1ᶜ +ᶜ u)
        (onePlusStrictSubunitDomain ρ ρ<1 u u-bound)
  in
  logᶜ-positive-bounded
    (1ᶜ +ᶜ u)
    (onePlusStrictSubunitDomain ρ ρ<1 u u-bound)
  ≡
  twoᶜ ·ᶜ
  atanhᶜFromSubunitBound
    (transformRadius domain)
    (transformRadius<1 domain)
    (divideByPositiveᶜ
      u
      (denominatorLower domain)
      ((1ᶜ +ᶜ u) +ᶜ 1ᶜ)
      (denominatorBound domain))
    (subst
      (BoundedByᶜ (transformRadius domain))
      (logTransformᶜ-onePlus-path
        u
        (denominatorLower domain)
        (denominatorBound domain))
      (transformBound domain))
logOnePlusᶜWithinSubunitBall-global ρ ρ<1 u u-bound =
  cong (twoᶜ ·ᶜ_)
    (atanhᶜFromSubunitBound-argument-path
      (transformRadius domain)
      (transformRadius<1 domain)
      (logTransformᶜ-onePlus-path
        u
        (denominatorLower domain)
        (denominatorBound domain))
      (transformBound domain))
  where
  domain : LogDomainᶜ (1ᶜ +ᶜ u)
  domain =
    log-domain-from-positive-boundedᶜ
      (1ᶜ +ᶜ u)
      (onePlusStrictSubunitDomain ρ ρ<1 u u-bound)


logTransformᶜ-one-path :
  (denomLower : ℚ⁺) →
  (denomBound : BoundedAwayPositiveᶜ denomLower (1ᶜ +ᶜ 1ᶜ)) →
  logTransformᶜ 1ᶜ denomLower denomBound ≡ 0ᶜ
logTransformᶜ-one-path denomLower denomBound =
  cong
    (λ numerator →
      divideByPositiveᶜ numerator denomLower (1ᶜ +ᶜ 1ᶜ) denomBound)
    (SolverHelpers.one-minus-one CauchyRealsCommRing) ∙
  divideByPositiveᶜ-zero-left denomLower (1ᶜ +ᶜ 1ᶜ) denomBound
