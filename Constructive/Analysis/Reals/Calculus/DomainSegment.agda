{-

Zero derivatives on explicitly witnessed segments

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Calculus.DomainSegment where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Nat using (ℕ ; suc ; zero)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Reals.CauchyReals.Metric
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Reals.Calculus.SegmentEstimates
  using
    ( gridPointFrom
    ; gridPointFrom-displacement
    ; gridPointFrom-scalarMul
    ; gridDisplacement-unitFraction
    ; incrementCompose-path
    ; natMul-unitFraction-nonnegative
    ; natMul-unitFraction≤1
    ; repeatPositive
    ; repeatPositive-suc-radius
    ; segmentPoint
    ; unitFractionRepeat-path
    ; unitFractionStepBound
    ; unitFractionTimes≤
    )
open import Constructive.Analysis.Reals.Calculus.DomainDerivative
open import Constructive.Analysis.Reals.Calculus.DomainDerivativeRules
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Structures
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational
import Constructive.Data.Rationals.Archimedean as RationalArch


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    zero-linear-increment :
      (forward base step : 𝓡 .fst) →
      (forward + (- base)) + (- (0r · step)) ≡ forward + (- base)
    zero-linear-increment _ _ _ =
      solve! 𝓡

  dependentFunction-path :
    {ℓ : Level} →
    {D : ℝᶜ → Type ℓ} →
    (f : (x : ℝᶜ) → D x → ℝᶜ) →
    {x y : ℝᶜ} →
    (p : x ≡ y) →
    (x-domain : D x) →
    f x x-domain ≡ f y (subst D p x-domain)
  dependentFunction-path {D = D} f p x-domain i =
    f (p i) (subst-filler D p x-domain i)

  zeroDerivativeGridBound :
    {ℓ : Level} →
    {D : ℝᶜ → Type ℓ} →
    {f : (x : ℝᶜ) → D x → ℝᶜ} →
    {μ : PrecisionModulus} →
    DomainValueIndependent f →
    ((y : ℝᶜ) →
      (y-domain : D y) →
      HasDerivativeWithinDomainAtWith f y y-domain 0ᶜ μ) →
    (α δ : ℚ⁺) →
    (step : ℝᶜ) →
    BoundedByᶜ δ step →
    radius δ ℚOrder.≤ radius (μ α) →
    (m : ℕ) →
    (p : ℝᶜ) →
    (p-domain : D p) →
    (endpoint-domain : D (gridPointFrom p step m)) →
    (pointDomain : (k : ℕ) →
      NatOrder._≤_ k m →
      D (gridPointFrom p step k)) →
    BoundedByᶜ
      (repeatPositive (α *⁺ δ) m)
      (f (gridPointFrom p step m)
          endpoint-domain +ᶜ (-ᶜ f p p-domain))
  zeroDerivativeGridBound
    {D = D}
    {f = f}
    {μ = μ}
    independent
    derivative
    α
    δ
    step
    step-bound
    δ≤μα
    m
    p
    p-domain
    endpoint-domain
    pointDomain =
    go m p p-domain endpoint-domain pointDomain
    where
    localBound : ℚ⁺
    localBound =
      α *⁺ δ

    go :
      (m : ℕ) →
      (p : ℝᶜ) →
      (p-domain : D p) →
      (endpoint-domain : D (gridPointFrom p step m)) →
      (pointDomain : (k : ℕ) →
        NatOrder._≤_ k m →
        D (gridPointFrom p step k)) →
      BoundedByᶜ
        (repeatPositive localBound m)
        (f (gridPointFrom p step m)
            endpoint-domain +ᶜ (-ᶜ f p p-domain))
    go zero p p-domain endpoint-domain pointDomain =
      subst
        (BoundedByᶜ 1⁺)
        (sym (add-inverse-right (f p endpoint-domain)) ∙
         cong
           (f p endpoint-domain +ᶜ_)
           (cong -ᶜ_ (independent p endpoint-domain p-domain)))
        (bounded-byᶜ-zero 1⁺)
    go (suc zero) p p-domain endpoint-domain pointDomain =
      subst
        (BoundedByᶜ localBound)
        (SolverHelpers.zero-linear-increment
          CauchyRealsCommRing
          (f (p +ᶜ step) endpoint-domain)
          (f p p-domain)
          step)
        (derivative p p-domain
          α
          δ
          δ≤μα
          step
          step-bound
          endpoint-domain)
    go (suc (suc n)) p p-domain endpoint-domain pointDomain =
      subst
        (BoundedByᶜ
          (localBound +⁺ repeatPositive localBound (suc n)))
        (incrementCompose-path
          (f p p-domain)
          (f (p +ᶜ step) forward-domain)
          (f (gridPointFrom (p +ᶜ step) step (suc n))
            endpoint-domain))
        (bounded-byᶜ-add
          localBound
          (repeatPositive localBound (suc n))
          (f (p +ᶜ step) forward-domain +ᶜ (-ᶜ f p p-domain))
          (f (gridPointFrom (p +ᶜ step) step (suc n))
              endpoint-domain +ᶜ
            (-ᶜ f (p +ᶜ step) forward-domain))
          oneStep
          (go
            (suc n)
            (p +ᶜ step)
            forward-domain
            endpoint-domain
            (λ k k≤sucn →
              pointDomain (suc k) (NatOrder.suc-≤-suc k≤sucn))))
      where
      forward-domain : D (p +ᶜ step)
      forward-domain =
        pointDomain (suc zero) (NatOrder.suc-≤-suc NatOrder.zero-≤)

      oneStep :
        BoundedByᶜ
          localBound
          (f (p +ᶜ step) forward-domain +ᶜ (-ᶜ f p p-domain))
      oneStep =
        subst
          (BoundedByᶜ localBound)
          (SolverHelpers.zero-linear-increment
            CauchyRealsCommRing
            (f (p +ᶜ step) forward-domain)
            (f p p-domain)
            step)
          (derivative p p-domain
            α
            δ
            δ≤μα
            step
            step-bound
            forward-domain)


zeroDerivativeWithinDomainSegment :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f : (x : ℝᶜ) → D x → ℝᶜ} →
  DomainValueIndependent f →
  {μ : PrecisionModulus} →
  ((y : ℝᶜ) →
    (y-domain : D y) →
    HasDerivativeWithinDomainAtWith f y y-domain 0ᶜ μ) →
  (x h : ℝᶜ) →
  (x-domain : D x) →
  (forward-domain : D (x +ᶜ h)) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ h →
  ((q : ℚ) →
    Rational.0ℚ ℚOrder.≤ q →
    q ℚOrder.≤ Rational.1ℚ →
    D (segmentPoint x h q)) →
  f (x +ᶜ h) forward-domain ≡ f x x-domain
zeroDerivativeWithinDomainSegment
  {D = D}
  {f = f}
  independent
  {μ = μ}
  derivative
  x
  h
  x-domain
  forward-domain
  κ
  h-bound
  segment-domain =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    (f (x +ᶜ h) forward-domain)
    (f x x-domain)
    closeAt
  where
  closeAt :
    (ε : ℚ⁺) →
    f (x +ᶜ h) forward-domain ∼[ ε ] f x x-domain
  closeAt ε =
    subst2
      (λ left right → left ∼[ ε ] right)
      endpointValuePath
      (independent x x-domain x-domain)
      (diff-close-zero→close
        (bounded-byᶜ-close-zero
          (half⁺ ε)
          ε
          (f gridEndpoint gridEndpointDomain +ᶜ (-ᶜ f x x-domain))
          endpointDifferenceBound
          (half< ε)))
    where
    α : ℚ⁺
    α =
      posInv⁺ κ *⁺ half⁺ ε

    stepTarget : ℚ⁺
    stepTarget =
      posInv⁺ κ *⁺ μ α

    stepSearch :
      Σ[ n ∈ ℕ ] RationalArch.unitFraction n ℚOrder.< radius stepTarget
    stepSearch =
      RationalArch.archimedean-unit-fraction
        (radius stepTarget)
        (stepTarget .snd)

    n : ℕ
    n =
      stepSearch .fst

    δ : ℚ⁺
    δ =
      unitFraction⁺ n *⁺ κ

    step : ℝᶜ
    step =
      scalarMulᶜ (RationalArch.unitFraction n) h

    δ≤μα : radius δ ℚOrder.≤ radius (μ α)
    δ≤μα =
      Rational.<→≤
        {p = radius δ}
        {q = radius (μ α)}
        (subst
          (λ q → radius δ ℚOrder.< q)
          stepTargetTimesκ
          (Rational.mul-right-positive-<
            {a = radius κ}
            {b = RationalArch.unitFraction n}
            {c = radius stepTarget}
            (κ .snd)
            (stepSearch .snd)))
      where
      stepTargetTimesκ :
        radius stepTarget ℚ.· radius κ ≡ radius (μ α)
      stepTargetTimesκ =
        cong radius
          (*⁺-assoc (posInv⁺ κ) (μ α) κ ∙
           cong
             (posInv⁺ κ *⁺_)
             (*⁺-comm (μ α) κ) ∙
           sym (*⁺-assoc (posInv⁺ κ) κ (μ α)) ∙
           cong
             (_*⁺ (μ α))
             (*⁺-posInv-left κ) ∙
           *⁺-identity-left (μ α))

    pointDomain :
      (k : ℕ) →
      NatOrder._≤_ k (suc n) →
      D (gridPointFrom x step k)
    pointDomain k k≤sucn =
      subst
        D
        (sym
          (gridPointFrom-scalarMul
            x
            h
            (RationalArch.unitFraction n)
            k))
        (segment-domain
          q
          (natMul-unitFraction-nonnegative n k)
          (natMul-unitFraction≤1 n k k≤sucn))
      where
      q : ℚ
      q =
        RationalArch.natMul k (RationalArch.unitFraction n)

    gridEndpoint : ℝᶜ
    gridEndpoint =
      gridPointFrom x step (suc n)

    gridEndpointDomain : D gridEndpoint
    gridEndpointDomain =
      pointDomain (suc n) NatOrder.≤-refl

    endpointPath : gridEndpoint ≡ x +ᶜ h
    endpointPath =
      gridPointFrom-displacement x step (suc n) ∙
      cong (x +ᶜ_) (gridDisplacement-unitFraction h n)

    endpointValuePath :
      f gridEndpoint gridEndpointDomain ≡
      f (x +ᶜ h) forward-domain
    endpointValuePath =
      dependentFunction-path f endpointPath gridEndpointDomain ∙
      independent
        (x +ᶜ h)
        (subst D endpointPath gridEndpointDomain)
        forward-domain

    rawBound :
      BoundedByᶜ
        (repeatPositive (α *⁺ δ) (suc n))
        (f gridEndpoint gridEndpointDomain +ᶜ (-ᶜ f x x-domain))
    rawBound =
      zeroDerivativeGridBound
        independent
        derivative
        α
        δ
        step
        (unitFractionStepBound n h-bound)
        δ≤μα
        (suc n)
        x
        x-domain
        gridEndpointDomain
        pointDomain

    totalRadiusPath :
      radius (repeatPositive (α *⁺ δ) (suc n)) ≡ radius (half⁺ ε)
    totalRadiusPath =
      repeatPositive-suc-radius (α *⁺ δ) n ∙
      cong
        (RationalArch.natMul (suc n))
        (cong radius
          (sym (*⁺-assoc α (unitFraction⁺ n) κ) ∙
           cong
             (_*⁺ κ)
             (*⁺-comm α (unitFraction⁺ n)) ∙
           *⁺-assoc (unitFraction⁺ n) α κ)) ∙
      unitFractionRepeat-path (α *⁺ κ) n ∙
      cong radius
        (*⁺-assoc (posInv⁺ κ) (half⁺ ε) κ ∙
         cong
           (posInv⁺ κ *⁺_)
           (*⁺-comm (half⁺ ε) κ) ∙
         sym (*⁺-assoc (posInv⁺ κ) κ (half⁺ ε)) ∙
         cong
           (_*⁺ (half⁺ ε))
           (*⁺-posInv-left κ) ∙
         *⁺-identity-left (half⁺ ε))

    endpointDifferenceBound :
      BoundedByᶜ
        (half⁺ ε)
        (f gridEndpoint gridEndpointDomain +ᶜ (-ᶜ f x x-domain))
    endpointDifferenceBound =
      subst
        (λ θ →
          BoundedByᶜ
            θ
            (f gridEndpoint gridEndpointDomain +ᶜ (-ᶜ f x x-domain)))
        (ℚ⁺Path totalRadiusPath)
        rawBound


equalDerivativesWithinDomainSegment :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f g df dg : (x : ℝᶜ) → D x → ℝᶜ} →
  DomainValueIndependent f →
  DomainValueIndependent g →
  {μ ν : PrecisionModulus} →
  ((y : ℝᶜ) →
    (y-domain : D y) →
    HasDerivativeWithinDomainAtWith f y y-domain (df y y-domain) μ) →
  ((y : ℝᶜ) →
    (y-domain : D y) →
    HasDerivativeWithinDomainAtWith g y y-domain (dg y y-domain) ν) →
  ((y : ℝᶜ) → (y-domain : D y) → df y y-domain ≡ dg y y-domain) →
  (x h : ℝᶜ) →
  (x-domain : D x) →
  (forward-domain : D (x +ᶜ h)) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ h →
  ((q : ℚ) →
    Rational.0ℚ ℚOrder.≤ q →
    q ℚOrder.≤ Rational.1ℚ →
    D (segmentPoint x h q)) →
  f x x-domain ≡ g x x-domain →
  f (x +ᶜ h) forward-domain ≡ g (x +ᶜ h) forward-domain
equalDerivativesWithinDomainSegment
  {D = D}
  {f = f}
  {g = g}
  {df = df}
  {dg = dg}
  f-independent
  g-independent
  {μ = μ}
  {ν = ν}
  f-derivative
  g-derivative
  derivatives-equal
  x
  h
  x-domain
  forward-domain
  κ
  h-bound
  segment-domain
  base-equal =
  sym (minus-plus-cancel-right forward-f forward-g) ∙
  cong (_+ᶜ forward-g) difference-zero ∙
  add-zero-left forward-g
  where
  difference :
    (y : ℝᶜ) →
    D y →
    ℝᶜ
  difference y y-domain =
    f y y-domain +ᶜ (-ᶜ g y y-domain)

  difference-independent :
    DomainValueIndependent difference
  difference-independent y left right =
    cong₂
      (λ f-value g-value → f-value +ᶜ (-ᶜ g-value))
      (f-independent y left right)
      (g-independent y left right)

  difference-modulus : PrecisionModulus
  difference-modulus ε =
    min⁺ (μ (half⁺ ε)) (ν (half⁺ ε))

  difference-derivative :
    (y : ℝᶜ) →
    (y-domain : D y) →
    HasDerivativeWithinDomainAtWith
      difference
      y
      y-domain
      0ᶜ
      difference-modulus
  difference-derivative y y-domain =
    subst
      (λ d →
        HasDerivativeWithinDomainAtWith
          difference
          y
          y-domain
          d
          difference-modulus)
      derivative-zero
      (derivativeWithinDomainAddAtWith
        (f-derivative y y-domain)
        (derivativeWithinDomainNegAtWith (g-derivative y y-domain)))
    where
    derivative-zero :
      df y y-domain +ᶜ (-ᶜ dg y y-domain) ≡ 0ᶜ
    derivative-zero =
      cong
        (df y y-domain +ᶜ_)
        (cong -ᶜ_ (sym (derivatives-equal y y-domain))) ∙
      add-inverse-right (df y y-domain)

  difference-constant :
    difference (x +ᶜ h) forward-domain ≡ difference x x-domain
  difference-constant =
    zeroDerivativeWithinDomainSegment
      difference-independent
      difference-derivative
      x
      h
      x-domain
      forward-domain
      κ
      h-bound
      segment-domain

  base-difference-zero :
    difference x x-domain ≡ 0ᶜ
  base-difference-zero =
    cong (λ value → value +ᶜ (-ᶜ g x x-domain)) base-equal ∙
    add-inverse-right (g x x-domain)

  difference-zero :
    difference (x +ᶜ h) forward-domain ≡ 0ᶜ
  difference-zero =
    difference-constant ∙
    base-difference-zero

  forward-f : ℝᶜ
  forward-f =
    f (x +ᶜ h) forward-domain

  forward-g : ℝᶜ
  forward-g =
    g (x +ᶜ h) forward-domain
