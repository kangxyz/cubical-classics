{-

Algebraic and chain rules for domain-indexed derivatives

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Calculus.Derivative.Domain.Rules where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.Derivative.Domain.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.CommRing
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


private
  module SolverHelpers {ℓ : Level} (𝒩 : CommRing ℓ) where
    open CommRingStr (𝒩 .snd)

    remainder-add :
      (fh fx gh gx df dg h : 𝒩 .fst) →
      (((fh + gh) + (- (fx + gx))) + (- ((df + dg) · h))) ≡
      (((fh + (- fx)) + (- (df · h))) +
        ((gh + (- gx)) + (- (dg · h))))
    remainder-add _ _ _ _ _ _ _ =
      solve! 𝒩

    remainder-neg :
      (fh fx d h : 𝒩 .fst) →
      (((- fh) + (- (- fx))) + (- ((- d) · h))) ≡
      (- ((fh + (- fx)) + (- (d · h))))
    remainder-neg _ _ _ _ =
      solve! 𝒩

    remainder-scale :
      (c fh fx d h : 𝒩 .fst) →
      (((c · fh) + (- (c · fx))) + (- ((c · d) · h))) ≡
      c · ((fh + (- fx)) + (- (d · h)))
    remainder-scale _ _ _ _ _ =
      solve! 𝒩

    increment-from-remainder :
      (gh gx dg h : 𝒩 .fst) →
      gh + (- gx) ≡
      ((gh + (- gx)) + (- (dg · h))) + (dg · h)
    increment-from-remainder _ _ _ _ =
      solve! 𝒩

    add-increment :
      (gx gh : 𝒩 .fst) →
      gx + (gh + (- gx)) ≡ gh
    add-increment _ _ =
      solve! 𝒩

    chain-remainder :
      (fgh fg gh gx df dg h : 𝒩 .fst) →
      ((fgh + (- fg)) + (- ((df · dg) · h))) ≡
      (((fgh + (- fg)) + (- (df · (gh + (- gx))))) +
        (df · ((gh + (- gx)) + (- (dg · h)))))
    chain-remainder _ _ _ _ _ _ _ =
      solve! 𝒩

  half-product≡ :
    (ε η : ℚ⁺) →
    half⁺ ε *⁺ η ≡ half⁺ (ε *⁺ η)
  half-product≡ ε η =
    ℚ⁺Path
      (sym (ℚ.·Assoc (radius ε) Rational.1/2 (radius η)) ∙
       cong (radius ε ℚ.·_) (ℚ.·Comm Rational.1/2 (radius η)) ∙
       ℚ.·Assoc (radius ε) (radius η) Rational.1/2)

  two-half-products≡ :
    (ε η : ℚ⁺) →
    (half⁺ ε *⁺ η) +⁺ (half⁺ ε *⁺ η) ≡ ε *⁺ η
  two-half-products≡ ε η =
    cong₂ _+⁺_ (half-product≡ ε η) (half-product≡ ε η) ∙
    half⁺+half⁺≡ (ε *⁺ η)

  scale-product≡ :
    (κ ε η : ℚ⁺) →
    κ *⁺ ((posInv⁺ κ *⁺ ε) *⁺ η) ≡ ε *⁺ η
  scale-product≡ κ ε η =
    cong
      (κ *⁺_)
      (*⁺-assoc (posInv⁺ κ) ε η) ∙
    sym (*⁺-assoc κ (posInv⁺ κ) (ε *⁺ η)) ∙
    cong (λ θ → θ *⁺ (ε *⁺ η)) (*⁺-posInv-right κ) ∙
    *⁺-identity-left (ε *⁺ η)

  outer-scale-product≡ :
    (κ ε η : ℚ⁺) →
    (posInv⁺ κ *⁺ ε) *⁺ (κ *⁺ η) ≡ ε *⁺ η
  outer-scale-product≡ κ ε η =
    *⁺-assoc (posInv⁺ κ) ε (κ *⁺ η) ∙
    cong
      (posInv⁺ κ *⁺_)
      (sym (*⁺-assoc ε κ η) ∙
       cong (_*⁺ η) (*⁺-comm ε κ) ∙
       *⁺-assoc κ ε η) ∙
    sym (*⁺-assoc (posInv⁺ κ) κ (ε *⁺ η)) ∙
    cong (λ θ → θ *⁺ (ε *⁺ η)) (*⁺-posInv-left κ) ∙
    *⁺-identity-left (ε *⁺ η)

  multiply-positive-≤ :
    {a b c : ℚ⁺} →
    radius a ℚOrder.≤ radius b →
    radius (c *⁺ a) ℚOrder.≤ radius (c *⁺ b)
  multiply-positive-≤ {a = a} {b = b} {c = c} a≤b =
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


derivativeWithinDomainAddAtWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f g : (x : ℝᶜ) → D x → ℝᶜ} →
  {x df dg : ℝᶜ} →
  {x-domain : D x} →
  {μ ν : PrecisionModulus} →
  HasDerivativeWithinDomainAtWith f x x-domain df μ →
  HasDerivativeWithinDomainAtWith g x x-domain dg ν →
  HasDerivativeWithinDomainAtWith
    (λ y y-domain → f y y-domain +ᶜ g y y-domain)
    x
    x-domain
    (df +ᶜ dg)
    (λ ε → min⁺ (μ (half⁺ ε)) (ν (half⁺ ε)))
derivativeWithinDomainAddAtWith
  {f = f}
  {g = g}
  {x = x}
  {df = df}
  {dg = dg}
  {μ = μ}
  {ν = ν}
  f-derivative
  g-derivative
  ε
  η
  η≤min
  h
  h-bound
  forward-domain =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (sym remainder-path)
    (subst
      (λ κ → BoundedByᶜ κ (f-remainder +ᶜ g-remainder))
      (two-half-products≡ ε η)
      (bounded-byᶜ-add
        (half⁺ ε *⁺ η)
        (half⁺ ε *⁺ η)
        f-remainder
        g-remainder
        (f-derivative (half⁺ ε) η η≤μ h h-bound forward-domain)
        (g-derivative (half⁺ ε) η η≤ν h h-bound forward-domain)))
  where
  η≤μ : radius η ℚOrder.≤ radius (μ (half⁺ ε))
  η≤μ =
    ℚOrder.isTrans≤ _ _ _ η≤min (min⁺≤left _ _)

  η≤ν : radius η ℚOrder.≤ radius (ν (half⁺ ε))
  η≤ν =
    ℚOrder.isTrans≤
      (radius η)
      (radius (min⁺ (μ (half⁺ ε)) (ν (half⁺ ε))))
      (radius (ν (half⁺ ε)))
      η≤min
      (min⁺≤right (μ (half⁺ ε)) (ν (half⁺ ε)))

  f-remainder =
    withinDomainLinearRemainder f x _ df h forward-domain

  g-remainder =
    withinDomainLinearRemainder g x _ dg h forward-domain

  remainder-path =
    SolverHelpers.remainder-add
      CauchyRealsCommRing
      (f (x +ᶜ h) forward-domain)
      (f x _)
      (g (x +ᶜ h) forward-domain)
      (g x _)
      df
      dg
      h


derivativeWithinDomainNegAtWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {x d : ℝᶜ} →
  {x-domain : D x} →
  {μ : PrecisionModulus} →
  HasDerivativeWithinDomainAtWith f x x-domain d μ →
  HasDerivativeWithinDomainAtWith
    (λ y y-domain → -ᶜ f y y-domain)
    x
    x-domain
    (-ᶜ d)
    μ
derivativeWithinDomainNegAtWith
  {f = f}
  {x = x}
  {d = d}
  derivative
  ε
  η
  η≤με
  h
  h-bound
  forward-domain =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (sym
      (SolverHelpers.remainder-neg
        CauchyRealsCommRing
        (f (x +ᶜ h) forward-domain)
        (f x _)
        d
        h))
    (bounded-byᶜ-neg
      (ε *⁺ η)
      (withinDomainLinearRemainder f x _ d h forward-domain)
      (derivative ε η η≤με h h-bound forward-domain))


derivativeWithinDomainMulConstantLeftAtWith :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  (κ : ℚ⁺) →
  (c : ℝᶜ) →
  BoundedByᶜ κ c →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  {x d : ℝᶜ} →
  {x-domain : D x} →
  {μ : PrecisionModulus} →
  HasDerivativeWithinDomainAtWith f x x-domain d μ →
  HasDerivativeWithinDomainAtWith
    (λ y y-domain → c ·ᶜ f y y-domain)
    x
    x-domain
    (c ·ᶜ d)
    (λ ε → μ (posInv⁺ κ *⁺ ε))
derivativeWithinDomainMulConstantLeftAtWith
  κ
  c
  c-bound
  {f = f}
  {x = x}
  {d = d}
  derivative
  ε
  η
  η≤μ
  h
  h-bound
  forward-domain =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (sym
      (SolverHelpers.remainder-scale
        CauchyRealsCommRing
        c
        (f (x +ᶜ h) forward-domain)
        (f x _)
        d
        h))
    (subst
      (λ θ → BoundedByᶜ θ (c ·ᶜ remainder))
      (scale-product≡ κ ε η)
      (bounded-byᶜ-mul
        κ
        ((posInv⁺ κ *⁺ ε) *⁺ η)
        c
        remainder
        c-bound
        (derivative
          (posInv⁺ κ *⁺ ε)
          η
          η≤μ
          h
          h-bound
          forward-domain)))
  where
  remainder =
    withinDomainLinearRemainder f x _ d h forward-domain


domainChainDerivativeModulus :
  ℚ⁺ →
  ℚ⁺ →
  PrecisionModulus →
  PrecisionModulus →
  PrecisionModulus
domainChainDerivativeModulus δ κ μ ν ε =
  min⁺
    (μ (min⁺ 1⁺ (posInv⁺ κ *⁺ half⁺ ε)))
    (posInv⁺ (δ +⁺ 1⁺) *⁺
      ν (posInv⁺ (δ +⁺ 1⁺) *⁺ half⁺ ε))


derivativeWithinDomainChainAtWith :
  {ℓD ℓE : Level} →
  {D : ℝᶜ → Type ℓD} →
  {E : ℝᶜ → Type ℓE} →
  {f : (y : ℝᶜ) → E y → ℝᶜ} →
  {g : (x : ℝᶜ) → D x → ℝᶜ} →
  (f-independent : DomainValueIndependent f) →
  (g-domain : (y : ℝᶜ) → (y-domain : D y) → E (g y y-domain)) →
  (δ κ : ℚ⁺) →
  {x dg df : ℝᶜ} →
  {x-domain : D x} →
  {μ ν : PrecisionModulus} →
  BoundedByᶜ δ dg →
  BoundedByᶜ κ df →
  HasDerivativeWithinDomainAtWith g x x-domain dg μ →
  HasDerivativeWithinDomainAtWith
    f
    (g x x-domain)
    (g-domain x x-domain)
    df
    ν →
  HasDerivativeWithinDomainAtWith
    (λ y y-domain → f (g y y-domain) (g-domain y y-domain))
    x
    x-domain
    (df ·ᶜ dg)
    (domainChainDerivativeModulus δ κ μ ν)
derivativeWithinDomainChainAtWith
  {D = D}
  {E = E}
  {f = f}
  {g = g}
  f-independent
  g-domain
  δ
  κ
  {x = x}
  {dg = dg}
  {df = df}
  {x-domain = x-domain}
  {μ = μ}
  {ν = ν}
  dg-bound
  df-bound
  g-derivative
  f-derivative
  ε
  η
  η≤target
  h
  h-bound
  forward-domain =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (sym composition-remainder-path)
    (subst
      (λ θ → BoundedByᶜ θ (outer-remainder +ᶜ scaled-inner-remainder))
      (two-half-products≡ ε η)
      (bounded-byᶜ-add
        (half⁺ ε *⁺ η)
        (half⁺ ε *⁺ η)
        outer-remainder
        scaled-inner-remainder
        outer-remainder-bound
        scaled-inner-remainder-bound))
  where
  halfε : ℚ⁺
  halfε =
    half⁺ ε

  innerPrecision : ℚ⁺
  innerPrecision =
    min⁺ 1⁺ (posInv⁺ κ *⁺ halfε)

  incrementScale : ℚ⁺
  incrementScale =
    δ +⁺ 1⁺

  outerPrecision : ℚ⁺
  outerPrecision =
    posInv⁺ incrementScale *⁺ halfε

  gx =
    g x x-domain

  gxh =
    g (x +ᶜ h) forward-domain

  increment =
    gxh +ᶜ (-ᶜ gx)

  inner-remainder =
    withinDomainLinearRemainder g x x-domain dg h forward-domain

  η≤μ : radius η ℚOrder.≤ radius (μ innerPrecision)
  η≤μ =
    ℚOrder.isTrans≤ _ _ _ η≤target (min⁺≤left _ _)

  η≤scaledν :
    radius η ℚOrder.≤
    radius (posInv⁺ incrementScale *⁺ ν outerPrecision)
  η≤scaledν =
    ℚOrder.isTrans≤
      (radius η)
      (radius
        (domainChainDerivativeModulus δ κ μ ν ε))
      (radius (posInv⁺ incrementScale *⁺ ν outerPrecision))
      η≤target
      (min⁺≤right
        (μ innerPrecision)
        (posInv⁺ incrementScale *⁺ ν outerPrecision))

  inner-remainder-bound :
    BoundedByᶜ (innerPrecision *⁺ η) inner-remainder
  inner-remainder-bound =
    g-derivative innerPrecision η η≤μ h h-bound forward-domain

  innerPrecision≤1 : radius innerPrecision ℚOrder.≤ radius 1⁺
  innerPrecision≤1 =
    min⁺≤left 1⁺ (posInv⁺ κ *⁺ halfε)

  innerPrecision≤scaled :
    radius innerPrecision ℚOrder.≤
    radius (posInv⁺ κ *⁺ halfε)
  innerPrecision≤scaled =
    min⁺≤right 1⁺ (posInv⁺ κ *⁺ halfε)

  inner-remainder-unit-bound :
    BoundedByᶜ (1⁺ *⁺ η) inner-remainder
  inner-remainder-unit-bound =
    bounded-byᶜ-monotone
      (multiply-positive-right-≤
        {a = innerPrecision}
        {b = 1⁺}
        {c = η}
        innerPrecision≤1)
      inner-remainder-bound

  linear-bound :
    BoundedByᶜ (δ *⁺ η) (dg ·ᶜ h)
  linear-bound =
    bounded-byᶜ-mul δ η dg h dg-bound h-bound

  increment-bound-raw :
    BoundedByᶜ
      ((1⁺ *⁺ η) +⁺ (δ *⁺ η))
      (inner-remainder +ᶜ (dg ·ᶜ h))
  increment-bound-raw =
    bounded-byᶜ-add
      (1⁺ *⁺ η)
      (δ *⁺ η)
      inner-remainder
      (dg ·ᶜ h)
      inner-remainder-unit-bound
      linear-bound

  incrementPrecisionPath :
    ((1⁺ *⁺ η) +⁺ (δ *⁺ η)) ≡
    incrementScale *⁺ η
  incrementPrecisionPath =
    ℚ⁺Path
      (sym (ℚ.·DistR+ Rational.1ℚ (radius δ) (radius η)) ∙
       cong (ℚ._· radius η) (ℚ.+Comm Rational.1ℚ (radius δ)))

  increment-bound :
    BoundedByᶜ (incrementScale *⁺ η) increment
  increment-bound =
    subst
      (BoundedByᶜ (incrementScale *⁺ η))
      (sym
        (SolverHelpers.increment-from-remainder
          CauchyRealsCommRing
          gxh
          gx
          dg
          h))
      (subst
        (λ θ →
          BoundedByᶜ θ (inner-remainder +ᶜ (dg ·ᶜ h)))
        incrementPrecisionPath
        increment-bound-raw)

  scaledν≤ :
    radius (incrementScale *⁺ η) ℚOrder.≤
    radius (ν outerPrecision)
  scaledν≤ =
    subst
      (λ θ → radius (incrementScale *⁺ η) ℚOrder.≤ radius θ)
      (scale-precision-cancel incrementScale (ν outerPrecision))
      (multiply-positive-≤ {c = incrementScale} η≤scaledν)
    where
    scale-precision-cancel :
      (a b : ℚ⁺) →
      a *⁺ (posInv⁺ a *⁺ b) ≡ b
    scale-precision-cancel a b =
      sym (*⁺-assoc a (posInv⁺ a) b) ∙
      cong (λ θ → θ *⁺ b) (*⁺-posInv-right a) ∙
      *⁺-identity-left b

  addIncrementPath : gx +ᶜ increment ≡ gxh
  addIncrementPath =
    SolverHelpers.add-increment CauchyRealsCommRing gx gxh

  outer-forward-domain : E (gx +ᶜ increment)
  outer-forward-domain =
    subst E (sym addIncrementPath) (g-domain (x +ᶜ h) forward-domain)

  outer-forward-value-path :
    f (gx +ᶜ increment) outer-forward-domain ≡
    f gxh (g-domain (x +ᶜ h) forward-domain)
  outer-forward-value-path =
    domainValueAlongPath
      f-independent
      addIncrementPath
      outer-forward-domain
      (g-domain (x +ᶜ h) forward-domain)

  outer-remainder =
    (f gxh (g-domain (x +ᶜ h) forward-domain) +ᶜ
      (-ᶜ f gx (g-domain x x-domain))) +ᶜ
    (-ᶜ (df ·ᶜ increment))

  outer-remainder-bound :
    BoundedByᶜ (halfε *⁺ η) outer-remainder
  outer-remainder-bound =
    subst
      (BoundedByᶜ (halfε *⁺ η))
      (cong
        (λ value →
          (value +ᶜ (-ᶜ f gx (g-domain x x-domain))) +ᶜ
          (-ᶜ (df ·ᶜ increment)))
        outer-forward-value-path)
      (subst
        (λ θ →
          BoundedByᶜ θ
            (withinDomainLinearRemainder
              f
              gx
              (g-domain x x-domain)
              df
              increment
              outer-forward-domain))
        (outer-scale-product≡ incrementScale halfε η)
        (f-derivative
          outerPrecision
          (incrementScale *⁺ η)
          scaledν≤
          increment
          increment-bound
          outer-forward-domain))

  inner-remainder-scaled-bound :
    BoundedByᶜ
      ((posInv⁺ κ *⁺ halfε) *⁺ η)
      inner-remainder
  inner-remainder-scaled-bound =
    bounded-byᶜ-monotone
      (multiply-positive-right-≤
        {a = innerPrecision}
        {b = posInv⁺ κ *⁺ halfε}
        {c = η}
        innerPrecision≤scaled)
      inner-remainder-bound

  scaled-inner-remainder =
    df ·ᶜ inner-remainder

  scaled-inner-remainder-bound :
    BoundedByᶜ (halfε *⁺ η) scaled-inner-remainder
  scaled-inner-remainder-bound =
    subst
      (λ θ → BoundedByᶜ θ scaled-inner-remainder)
      (scale-product≡ κ halfε η)
      (bounded-byᶜ-mul
        κ
        ((posInv⁺ κ *⁺ halfε) *⁺ η)
        df
        inner-remainder
        df-bound
        inner-remainder-scaled-bound)

  composition-remainder-path =
    SolverHelpers.chain-remainder
      CauchyRealsCommRing
      (f gxh (g-domain (x +ᶜ h) forward-domain))
      (f gx (g-domain x x-domain))
      gxh
      gx
      df
      dg
      h
