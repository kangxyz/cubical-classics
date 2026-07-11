{-

Algebraic rules for one-dimensional derivatives

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Calculus.DerivativeRules where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.DerivativeData
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Structures
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using (bounded-byᶜ-mul)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    linear-remainder-add :
      (Fh Fx Gh Gx df dg h : 𝓡 .fst) →
      (((Fh + Gh) + (- (Fx + Gx))) + (- ((df + dg) · h))) ≡
      (((Fh + (- Fx)) + (- (df · h))) +
        ((Gh + (- Gx)) + (- (dg · h))))
    linear-remainder-add _ _ _ _ _ _ _ =
      solve! 𝓡

    linear-remainder-neg :
      (Fh Fx d h : 𝓡 .fst) →
      ((- Fh) + (- (- Fx))) + (- ((- d) · h)) ≡
      - ((Fh + (- Fx)) + (- (d · h)))
    linear-remainder-neg _ _ _ _ =
      solve! 𝓡

    linear-remainder-rational-scale :
      (q Fh Fx d h : 𝓡 .fst) →
      ((q · Fh) + (- (q · Fx))) + (- ((q · d) · h)) ≡
      q · ((Fh + (- Fx)) + (- (d · h)))
    linear-remainder-rational-scale _ _ _ _ _ =
      solve! 𝓡

    linear-remainder-left-scale :
      (c Fh Fx d h : 𝓡 .fst) →
      ((c · Fh) + (- (c · Fx))) + (- ((c · d) · h)) ≡
      c · ((Fh + (- Fx)) + (- (d · h)))
    linear-remainder-left-scale _ _ _ _ _ =
      solve! 𝓡

    identity-product-remainder-decomposition :
      (x h fh fx d : 𝓡 .fst) →
      (((x + h) · fh) + (- (x · fx))) +
        (- ((fx + (x · d)) · h))
      ≡
      ((x + h) · ((fh + (- fx)) + (- (d · h)))) +
      ((d · h) · h)
    identity-product-remainder-decomposition _ _ _ _ _ =
      solve! 𝓡

    identity-linear-remainder-zero :
      (x h : 𝓡 .fst) →
      ((x + h) + (- x)) + (- (1r · h)) ≡ 0r
    identity-linear-remainder-zero _ _ =
      solve! 𝓡

    constant-linear-remainder-zero :
      (c h : 𝓡 .fst) →
      (c + (- c)) + (- (0r · h)) ≡ 0r
    constant-linear-remainder-zero _ _ =
      solve! 𝓡

  zeroBound :
    (ε : ℚ⁺) →
    BoundedByᶜ ε 0ᶜ
  zeroBound ε =
    rational-closed-bound→boundedᶜ
      ε
      Rational.0ℚ
      (rational-closed-boundᶜ
        0≤ε
        (subst
          (λ q → q ℚOrder.≤ radius ε)
          (sym Rational.neg-zero)
          0≤ε))
    where
    0≤ε : Rational.0ℚ ℚOrder.≤ radius ε
    0≤ε =
      ℚOrder.<Weaken≤ Rational.0ℚ (radius ε) (ε .snd)

derivativeConstantAtWith :
  {c x : ℝᶜ} →
  {μ : PrecisionModulus} →
  HasDerivativeAtWith (λ _ → c) x 0ᶜ μ
derivativeConstantAtWith
  {c = c}
  ε
  η
  _
  h
  _ =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (sym
      (SolverHelpers.constant-linear-remainder-zero
        CauchyRealsCommRing
        c
        h))
    (zeroBound (ε *⁺ η))


derivativeIdentityAtWith :
  {x : ℝᶜ} →
  {μ : PrecisionModulus} →
  HasDerivativeAtWith (λ y → y) x 1ᶜ μ
derivativeIdentityAtWith
  {x = x}
  ε
  η
  _
  h
  _ =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (sym
      (SolverHelpers.identity-linear-remainder-zero
        CauchyRealsCommRing
        x
        h))
    (zeroBound (ε *⁺ η))


hasDerivativeAtWith-cong :
  {f g : ℝᶜ → ℝᶜ} →
  {x d e : ℝᶜ} →
  {μ : PrecisionModulus} →
  ((y : ℝᶜ) → f y ≡ g y) →
  d ≡ e →
  HasDerivativeAtWith f x d μ →
  HasDerivativeAtWith g x e μ
hasDerivativeAtWith-cong {x = x} {μ = μ} f≡g d≡e =
  subst2
    (λ F D → HasDerivativeAtWith F x D μ)
    (funExt f≡g)
    d≡e


derivativeAddAtWith :
  {f g : ℝᶜ → ℝᶜ} →
  {x df dg : ℝᶜ} →
  {μ ν : PrecisionModulus} →
  HasDerivativeAtWith f x df μ →
  HasDerivativeAtWith g x dg ν →
  HasDerivativeAtWith
    (λ y → f y +ᶜ g y)
    x
    (df +ᶜ dg)
    (λ ε → min⁺ (μ (half⁺ ε)) (ν (half⁺ ε)))
derivativeAddAtWith
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
  h-bound =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (sym remainder-add)
    (subst
      (λ κ → BoundedByᶜ κ (f-remainder +ᶜ g-remainder))
      (two-half⁺-products≡ ε η)
      sum-bound)
  where
  halfε : ℚ⁺
  halfε =
    half⁺ ε

  η≤μ : radius η ℚOrder.≤ radius (μ halfε)
  η≤μ =
    Rational.≤-trans
      {p = radius η}
      {q = radius (min⁺ (μ halfε) (ν halfε))}
      {r = radius (μ halfε)}
      η≤min
      (min⁺≤left (μ halfε) (ν halfε))

  η≤ν : radius η ℚOrder.≤ radius (ν halfε)
  η≤ν =
    Rational.≤-trans
      {p = radius η}
      {q = radius (min⁺ (μ halfε) (ν halfε))}
      {r = radius (ν halfε)}
      η≤min
      (min⁺≤right (μ halfε) (ν halfε))

  f-remainder : ℝᶜ
  f-remainder =
    linearRemainder f x df h

  g-remainder : ℝᶜ
  g-remainder =
    linearRemainder g x dg h

  f-bound : BoundedByᶜ (halfε *⁺ η) f-remainder
  f-bound =
    f-derivative halfε η η≤μ h h-bound

  g-bound : BoundedByᶜ (halfε *⁺ η) g-remainder
  g-bound =
    g-derivative halfε η η≤ν h h-bound

  sum-bound :
    BoundedByᶜ
      ((halfε *⁺ η) +⁺ (halfε *⁺ η))
      (f-remainder +ᶜ g-remainder)
  sum-bound =
    bounded-byᶜ-add
      (halfε *⁺ η)
      (halfε *⁺ η)
      f-remainder
      g-remainder
      f-bound
      g-bound

  remainder-add :
    linearRemainder (λ y → f y +ᶜ g y) x (df +ᶜ dg) h ≡
    f-remainder +ᶜ g-remainder
  remainder-add =
    SolverHelpers.linear-remainder-add
      CauchyRealsCommRing
      (f (x +ᶜ h))
      (f x)
      (g (x +ᶜ h))
      (g x)
      df
      dg
      h


derivativeNegAtWith :
  {f : ℝᶜ → ℝᶜ} →
  {x d : ℝᶜ} →
  {μ : PrecisionModulus} →
  HasDerivativeAtWith f x d μ →
  HasDerivativeAtWith (λ y → -ᶜ f y) x (-ᶜ d) μ
derivativeNegAtWith
  {f = f}
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
    (sym remainder-neg)
    (bounded-byᶜ-neg
      (ε *⁺ η)
      (linearRemainder f x d h)
      (derivative ε η η≤με h h-bound))
  where
  remainder-neg :
    linearRemainder (λ y → -ᶜ f y) x (-ᶜ d) h ≡
    -ᶜ linearRemainder f x d h
  remainder-neg =
    SolverHelpers.linear-remainder-neg
      CauchyRealsCommRing
      (f (x +ᶜ h))
      (f x)
      d
      h


derivativeSubAtWith :
  {f g : ℝᶜ → ℝᶜ} →
  {x df dg : ℝᶜ} →
  {μ ν : PrecisionModulus} →
  HasDerivativeAtWith f x df μ →
  HasDerivativeAtWith g x dg ν →
  HasDerivativeAtWith
    (λ y → f y +ᶜ (-ᶜ g y))
    x
    (df +ᶜ (-ᶜ dg))
    (λ ε → min⁺ (μ (half⁺ ε)) (ν (half⁺ ε)))
derivativeSubAtWith f-derivative g-derivative =
  derivativeAddAtWith
    f-derivative
    (derivativeNegAtWith g-derivative)


derivativeRationalScaleAtWith :
  (q : ℚ) →
  {f : ℝᶜ → ℝᶜ} →
  {x d : ℝᶜ} →
  {μ : PrecisionModulus} →
  HasDerivativeAtWith f x d μ →
  HasDerivativeAtWith
    (λ y → rational q ·ᶜ f y)
    x
    (rational q ·ᶜ d)
    (λ ε → μ (posInv⁺ (scalar-bound q) *⁺ ε))
derivativeRationalScaleAtWith
  q
  {f = f}
  {x = x}
  {d = d}
  {μ = μ}
  derivative
  ε
  η
  η≤μ
  h
  h-bound =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (sym remainder-scale)
    (subst
      (λ κ → BoundedByᶜ κ (rational q ·ᶜ f-remainder))
      (scale-posInv-product-cancel q-bound ε η)
      scaled-bound)
  where
  q-bound : ℚ⁺
  q-bound =
    scalar-bound q

  scaledPrecision : ℚ⁺
  scaledPrecision =
    posInv⁺ q-bound *⁺ ε

  f-remainder : ℝᶜ
  f-remainder =
    linearRemainder f x d h

  f-bound :
    BoundedByᶜ (scaledPrecision *⁺ η) f-remainder
  f-bound =
    derivative scaledPrecision η η≤μ h h-bound

  rational-bound : BoundedByᶜ q-bound (rational q)
  rational-bound =
    rational-bound→boundedᶜ
      q-bound
      q
      (scalar-bound-rational-boundᶜ q)

  scaled-bound :
    BoundedByᶜ
      (q-bound *⁺ (scaledPrecision *⁺ η))
      (rational q ·ᶜ f-remainder)
  scaled-bound =
    bounded-byᶜ-mul
      q-bound
      (scaledPrecision *⁺ η)
      (rational q)
      f-remainder
      rational-bound
      f-bound

  remainder-scale :
    linearRemainder
      (λ y → rational q ·ᶜ f y)
      x
      (rational q ·ᶜ d)
      h
    ≡ rational q ·ᶜ f-remainder
  remainder-scale =
    SolverHelpers.linear-remainder-rational-scale
      CauchyRealsCommRing
      (rational q)
      (f (x +ᶜ h))
      (f x)
      d
      h


derivativeMulConstantLeftAtWith :
  (κ : ℚ⁺) →
  (c : ℝᶜ) →
  BoundedByᶜ κ c →
  {f : ℝᶜ → ℝᶜ} →
  {x d : ℝᶜ} →
  {μ : PrecisionModulus} →
  HasDerivativeAtWith f x d μ →
  HasDerivativeAtWith
    (λ y → c ·ᶜ f y)
    x
    (c ·ᶜ d)
    (λ ε → μ (posInv⁺ κ *⁺ ε))
derivativeMulConstantLeftAtWith
  κ
  c
  c-bound
  {f = f}
  {x = x}
  {d = d}
  {μ = μ}
  derivative
  ε
  η
  η≤μ
  h
  h-bound =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (sym remainder-scale)
    (subst
      (λ θ → BoundedByᶜ θ (c ·ᶜ f-remainder))
      (scale-posInv-product-cancel κ ε η)
      scaled-bound)
  where
  scaledPrecision : ℚ⁺
  scaledPrecision =
    posInv⁺ κ *⁺ ε

  f-remainder : ℝᶜ
  f-remainder =
    linearRemainder f x d h

  f-bound :
    BoundedByᶜ (scaledPrecision *⁺ η) f-remainder
  f-bound =
    derivative scaledPrecision η η≤μ h h-bound

  scaled-bound :
    BoundedByᶜ
      (κ *⁺ (scaledPrecision *⁺ η))
      (c ·ᶜ f-remainder)
  scaled-bound =
    bounded-byᶜ-mul
      κ
      (scaledPrecision *⁺ η)
      c
      f-remainder
      c-bound
      f-bound

  remainder-scale :
    linearRemainder (λ y → c ·ᶜ f y) x (c ·ᶜ d) h ≡
    c ·ᶜ f-remainder
  remainder-scale =
    SolverHelpers.linear-remainder-left-scale
      CauchyRealsCommRing
      c
      (f (x +ᶜ h))
      (f x)
      d
      h


derivativeIdentityMulAtWith :
  (σ δ : ℚ⁺) →
  {f : ℝᶜ → ℝᶜ} →
  {x d : ℝᶜ} →
  {μ : PrecisionModulus} →
  BoundedByᶜ σ x →
  BoundedByᶜ δ d →
  HasDerivativeAtWith f x d μ →
  HasDerivativeAtWith
    (λ y → y ·ᶜ f y)
    x
    (f x +ᶜ x ·ᶜ d)
    (λ ε →
      min⁺
        (min⁺
          (μ (posInv⁺ (σ +⁺ 1⁺) *⁺ half⁺ ε))
          1⁺)
        (posInv⁺ δ *⁺ half⁺ ε))
derivativeIdentityMulAtWith
  σ
  δ
  {f = f}
  {x = x}
  {d = d}
  {μ = μ}
  x-bound
  d-bound
  derivative
  ε
  η
  η≤productModulus
  h
  h-bound =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (sym remainder-decomposition)
    (subst
      (λ κ → BoundedByᶜ κ (firstTerm +ᶜ secondTerm))
      (two-half⁺-products≡ ε η)
      combinedBound)
  where
  halfε : ℚ⁺
  halfε =
    half⁺ ε

  xhBoundPrecision : ℚ⁺
  xhBoundPrecision =
    σ +⁺ 1⁺

  remainderPrecision : ℚ⁺
  remainderPrecision =
    posInv⁺ xhBoundPrecision *⁺ halfε

  quadraticPrecision : ℚ⁺
  quadraticPrecision =
    posInv⁺ δ *⁺ halfε

  innerModulus : ℚ⁺
  innerModulus =
    min⁺ (μ remainderPrecision) 1⁺

  η≤inner : radius η ℚOrder.≤ radius innerModulus
  η≤inner =
    Rational.≤-trans
      {p = radius η}
      {q = radius (min⁺ innerModulus quadraticPrecision)}
      {r = radius innerModulus}
      η≤productModulus
      (min⁺≤left innerModulus quadraticPrecision)

  η≤μ : radius η ℚOrder.≤ radius (μ remainderPrecision)
  η≤μ =
    Rational.≤-trans
      {p = radius η}
      {q = radius innerModulus}
      {r = radius (μ remainderPrecision)}
      η≤inner
      (min⁺≤left (μ remainderPrecision) 1⁺)

  η≤1 : radius η ℚOrder.≤ radius 1⁺
  η≤1 =
    Rational.≤-trans
      {p = radius η}
      {q = radius innerModulus}
      {r = radius 1⁺}
      η≤inner
      (min⁺≤right (μ remainderPrecision) 1⁺)

  η≤quadratic :
    radius η ℚOrder.≤ radius quadraticPrecision
  η≤quadratic =
    Rational.≤-trans
      {p = radius η}
      {q = radius (min⁺ innerModulus quadraticPrecision)}
      {r = radius quadraticPrecision}
      η≤productModulus
      (min⁺≤right innerModulus quadraticPrecision)

  σ+η≤σ+1 :
    radius (σ +⁺ η) ℚOrder.≤ radius xhBoundPrecision
  σ+η≤σ+1 =
    subst2
      ℚOrder._≤_
      (ℚ.+Comm (radius η) (radius σ))
      (ℚ.+Comm (radius 1⁺) (radius σ))
      (ℚOrder.≤-+o
        (radius η)
        (radius 1⁺)
        (radius σ)
        η≤1)

  xh-bound :
    BoundedByᶜ xhBoundPrecision (x +ᶜ h)
  xh-bound =
    bounded-byᶜ-monotone
      σ+η≤σ+1
      (bounded-byᶜ-add σ η x h x-bound h-bound)

  f-remainder : ℝᶜ
  f-remainder =
    linearRemainder f x d h

  firstTerm : ℝᶜ
  firstTerm =
    (x +ᶜ h) ·ᶜ f-remainder

  secondTerm : ℝᶜ
  secondTerm =
    (d ·ᶜ h) ·ᶜ h

  f-remainder-bound :
    BoundedByᶜ (remainderPrecision *⁺ η) f-remainder
  f-remainder-bound =
    derivative remainderPrecision η η≤μ h h-bound

  firstTermBoundRaw :
    BoundedByᶜ
      (xhBoundPrecision *⁺ (remainderPrecision *⁺ η))
      firstTerm
  firstTermBoundRaw =
    bounded-byᶜ-mul
      xhBoundPrecision
      (remainderPrecision *⁺ η)
      (x +ᶜ h)
      f-remainder
      xh-bound
      f-remainder-bound

  firstTermBound :
    BoundedByᶜ (halfε *⁺ η) firstTerm
  firstTermBound =
    subst
      (λ κ → BoundedByᶜ κ firstTerm)
      (scale-posInv-product-cancel xhBoundPrecision halfε η)
      firstTermBoundRaw

  dh-bound :
    BoundedByᶜ (δ *⁺ η) (d ·ᶜ h)
  dh-bound =
    bounded-byᶜ-mul
      δ
      η
      d
      h
      d-bound
      h-bound

  secondTermBoundRaw :
    BoundedByᶜ ((δ *⁺ η) *⁺ η) secondTerm
  secondTermBoundRaw =
    bounded-byᶜ-mul
      (δ *⁺ η)
      η
      (d ·ᶜ h)
      h
      dh-bound
      h-bound

  δη≤δquadratic :
    radius (δ *⁺ η) ℚOrder.≤ radius (δ *⁺ quadraticPrecision)
  δη≤δquadratic =
    subst2
      ℚOrder._≤_
      (ℚ.·Comm (radius η) (radius δ))
      (ℚ.·Comm (radius quadraticPrecision) (radius δ))
      (ℚOrder.≤-·o
        (radius η)
        (radius quadraticPrecision)
        (radius δ)
        (ℚOrder.<Weaken≤
          Rational.0ℚ
          (radius δ)
          (δ .snd))
        η≤quadratic)

  δη≤halfε :
    radius (δ *⁺ η) ℚOrder.≤ radius halfε
  δη≤halfε =
    subst
      (λ κ → radius (δ *⁺ η) ℚOrder.≤ radius κ)
      (scale-posInv-cancel δ halfε)
      δη≤δquadratic

  quadraticTerm≤half :
    radius ((δ *⁺ η) *⁺ η) ℚOrder.≤ radius (halfε *⁺ η)
  quadraticTerm≤half =
    ℚOrder.≤-·o
      (radius (δ *⁺ η))
      (radius halfε)
      (radius η)
      (ℚOrder.<Weaken≤
        Rational.0ℚ
        (radius η)
        (η .snd))
      δη≤halfε

  secondTermBound :
    BoundedByᶜ (halfε *⁺ η) secondTerm
  secondTermBound =
    bounded-byᶜ-monotone
      quadraticTerm≤half
      secondTermBoundRaw

  combinedBound :
    BoundedByᶜ
      ((halfε *⁺ η) +⁺ (halfε *⁺ η))
      (firstTerm +ᶜ secondTerm)
  combinedBound =
    bounded-byᶜ-add
      (halfε *⁺ η)
      (halfε *⁺ η)
      firstTerm
      secondTerm
      firstTermBound
      secondTermBound

  remainder-decomposition :
    linearRemainder
      (λ y → y ·ᶜ f y)
      x
      (f x +ᶜ x ·ᶜ d)
      h
    ≡ firstTerm +ᶜ secondTerm
  remainder-decomposition =
    SolverHelpers.identity-product-remainder-decomposition
      CauchyRealsCommRing
      x
      h
      (f (x +ᶜ h))
      (f x)
      d


identityProductDerivativeModulus :
  ℚ⁺ →
  ℚ⁺ →
  PrecisionModulus →
  PrecisionModulus
identityProductDerivativeModulus σ δ μ ε =
  min⁺
    (min⁺
      (μ (posInv⁺ (σ +⁺ 1⁺) *⁺ half⁺ ε))
      1⁺)
    (posInv⁺ δ *⁺ half⁺ ε)
