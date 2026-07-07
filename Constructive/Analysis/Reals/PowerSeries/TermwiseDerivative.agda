{-

Termwise derivative criterion for power-series sums

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; max ; suc ; zero)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Map using (PrecisionModulus)
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.Calculus.Derivative
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.CommRing
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base using (_≤ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.Series
  using
    ( partialSum
    ; partialSum-add
    ; seriesSumFromFiniteTailBoundConvergesAt
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower ; realPowerBoundsFromBound)
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Positive
  using (positivePower)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( addPowerSeries
    ; addPowerSeriesTerm
    ; bounded-byᶜ-zero
    ; powerSeriesPartialSum-add
    ; powerSeriesPartialSum-shift
    ; shiftPowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.Analytic
  using
    ( HasPowerSeriesAtWith
    ; centeredPowerSeriesSumEverywhereHasPowerSeriesAtWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Analysis.Reals.PowerSeries.Differentiation
  using
    ( derivativePowerSeries
    ; derivativePrimitivePowerSeries
    ; naturalReal
    ; primitivePowerSeries
    )
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence
  using (derivativePrimitivePowerSeriesInfiniteRadius)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open ClosenessOf RationalsMetricSpace


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    linear-remainder-decomposition :
      (Fh Fx Ph Px d p' h : 𝓡 .fst) →
      (Fh + (- Fx)) + (- (d · h)) ≡
      ((((Fh + (- Ph)) + ((Ph + (- Px)) + (- (p' · h)))) +
        (Px + (- Fx))) +
        (- ((d + (- p')) · h)))
    linear-remainder-decomposition _ _ _ _ _ _ _ =
      solve! 𝓡

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

    linear-partial-sum-remainder-zero :
      (a₀ a₁ x h : 𝓡 .fst) →
      ((a₀ + ((x + h) · a₁)) + (- (a₀ + (x · a₁)))) +
        (- (a₁ · h))
      ≡ 0r
    linear-partial-sum-remainder-zero _ _ _ _ =
      solve! 𝓡

  four-quarter-sum≡ :
    (ε : ℚ⁺) →
    (quarter⁺ ε +⁺ quarter⁺ ε) +⁺
      (quarter⁺ ε +⁺ quarter⁺ ε)
    ≡ ε
  four-quarter-sum≡ ε =
    cong₂
      _+⁺_
      (ℚ⁺Path (quarter-sum≡half ε))
      (ℚ⁺Path (quarter-sum≡half ε)) ∙
    half⁺+half⁺≡ ε

  four-quarters≡ :
    (ε : ℚ⁺) →
    ((quarter⁺ ε +⁺ quarter⁺ ε) +⁺ quarter⁺ ε) +⁺ quarter⁺ ε
    ≡ ε
  four-quarters≡ ε =
    +⁺-assoc
      (quarter⁺ ε +⁺ quarter⁺ ε)
      (quarter⁺ ε)
      (quarter⁺ ε) ∙
    four-quarter-sum≡ ε

  half-product≡ :
    (ε η : ℚ⁺) →
    half⁺ ε *⁺ η ≡ half⁺ (ε *⁺ η)
  half-product≡ ε η =
    ℚ⁺Path
      (sym (ℚ.·Assoc (radius ε) Rational.1/2 (radius η)) ∙
       cong
        (radius ε ℚ.·_)
        (ℚ.·Comm Rational.1/2 (radius η)) ∙
       ℚ.·Assoc (radius ε) (radius η) Rational.1/2)

  quarter-product≡ :
    (ε η : ℚ⁺) →
    quarter⁺ ε *⁺ η ≡ quarter⁺ (ε *⁺ η)
  quarter-product≡ ε η =
    half-product≡ (half⁺ ε) η ∙
    cong half⁺ (half-product≡ ε η)

  two-half-products≡ :
    (ε η : ℚ⁺) →
    (half⁺ ε *⁺ η) +⁺ (half⁺ ε *⁺ η) ≡ ε *⁺ η
  two-half-products≡ ε η =
    cong₂
      _+⁺_
      (half-product≡ ε η)
      (half-product≡ ε η) ∙
    half⁺+half⁺≡ (ε *⁺ η)

  scale-product≡ :
    (κ ε η : ℚ⁺) →
    κ *⁺ ((posInv⁺ κ *⁺ ε) *⁺ η) ≡ ε *⁺ η
  scale-product≡ κ ε η =
    cong
      (κ *⁺_)
      (*⁺-assoc (posInv⁺ κ) ε η) ∙
    sym (*⁺-assoc κ (posInv⁺ κ) (ε *⁺ η)) ∙
    cong
      (λ θ → θ *⁺ (ε *⁺ η))
      (*⁺-posInv-right κ) ∙
    *⁺-identity-left (ε *⁺ η)

  scale-precision-cancel :
    (κ ε : ℚ⁺) →
    κ *⁺ (posInv⁺ κ *⁺ ε) ≡ ε
  scale-precision-cancel κ ε =
    sym (*⁺-assoc κ (posInv⁺ κ) ε) ∙
    cong
      (λ θ → θ *⁺ ε)
      (*⁺-posInv-right κ) ∙
    *⁺-identity-left ε

  close-zero→bounded-byᶜ :
    {δ ε : ℚ⁺} →
    (x : ℝᶜ) →
    δ <⁺ ε →
    x ∼[ δ ] 0ᶜ →
    BoundedByᶜ ε x
  close-zero→bounded-byᶜ {δ = δ} {ε = ε} x δ<ε x∼0 =
    bounded-byᶜ upperBound lowerBound
    where
    normalizeUpper :
      rational (Rational.0ℚ ℚ.+ radius ε) ≡ rational (radius ε)
    normalizeUpper =
      cong rational (ℚ.+IdL (radius ε))

    upperBound :
      x ≤ᶜ rational (radius ε)
    upperBound =
      subst
        (x ≤ᶜ_)
        normalizeUpper
        (close-rational-upper-bound
          x
          Rational.0ℚ
          δ
          ε
          δ<ε
          x∼0)

    -x∼0 :
      (-ᶜ x) ∼[ δ ] 0ᶜ
    -x∼0 =
      subst
        (λ y → (-ᶜ x) ∼[ δ ] y)
        (cong rational Rational.neg-zero)
        (neg-close x∼0)

    lowerBound :
      (-ᶜ x) ≤ᶜ rational (radius ε)
    lowerBound =
      subst
        ((-ᶜ x) ≤ᶜ_)
        normalizeUpper
        (close-rational-upper-bound
          (-ᶜ x)
          Rational.0ℚ
          δ
          ε
          δ<ε
          -x∼0)

  close→difference-bounded-byᶜ :
    {δ ε : ℚ⁺} →
    (x y : ℝᶜ) →
    δ <⁺ ε →
    x ∼[ δ ] y →
    BoundedByᶜ ε (x +ᶜ (-ᶜ y))
  close→difference-bounded-byᶜ {δ = δ} x y δ<ε x∼y =
    close-zero→bounded-byᶜ (x +ᶜ (-ᶜ y)) δ<ε diff∼0
    where
    diff∼0 :
      (x +ᶜ (-ᶜ y)) ∼[ δ ] 0ᶜ
    diff∼0 =
      subst
        (λ z → (x +ᶜ (-ᶜ y)) ∼[ δ ] z)
        (add-inverse-right y)
        (add-close-left x∼y (-ᶜ y))

  n≤sucn : (n : ℕ) → NatOrder._≤_ n (suc n)
  n≤sucn n =
    suc zero , refl

  summand-left≤sum :
    (ε δ : ℚ⁺) →
    radius ε ℚOrder.≤ radius (ε +⁺ δ)
  summand-left≤sum ε δ =
    Rational.<→≤
      {p = radius ε}
      {q = radius (ε +⁺ δ)}
      (summand-left<sum ε δ)


TermwiseDerivativeIndex : Type₀
TermwiseDerivativeIndex =
  ℚ⁺ → ℚ⁺ → ℕ


powerSeriesTermwiseBoundIndex :
  (ℚ⁺ → ℕ) →
  ℚ⁺ →
  ℕ
powerSeriesTermwiseBoundIndex ν θ =
  ν (quarter⁺ (half⁺ (half⁺ θ)))


PowerSeriesTermwiseSumBoundIndexLarge :
  (ℚ⁺ → ℕ) →
  TermwiseDerivativeIndex →
  Type₀
PowerSeriesTermwiseSumBoundIndexLarge ν χ =
  (ε η : ℚ⁺) →
  NatOrder._≤_
    (powerSeriesTermwiseBoundIndex ν (quarter⁺ (ε *⁺ η)))
    (χ ε η)


PowerSeriesTermwiseDerivativeValueIndexLarge :
  (ℚ⁺ → ℕ) →
  TermwiseDerivativeIndex →
  Type₀
PowerSeriesTermwiseDerivativeValueIndexLarge ν χ =
  (ε η : ℚ⁺) →
  NatOrder._≤_
    (powerSeriesTermwiseBoundIndex ν (quarter⁺ ε))
    (χ ε η)


termwiseConvergenceIndex :
  (ℚ⁺ → ℕ) →
  (ℚ⁺ → ℕ) →
  TermwiseDerivativeIndex
termwiseConvergenceIndex ν τ ε η =
  max
    (powerSeriesTermwiseBoundIndex ν (quarter⁺ (ε *⁺ η)))
    (powerSeriesTermwiseBoundIndex τ (quarter⁺ ε))


termwiseConvergenceIndex-sumLarge :
  {ν τ : ℚ⁺ → ℕ} →
  PowerSeriesTermwiseSumBoundIndexLarge
    ν
    (termwiseConvergenceIndex ν τ)
termwiseConvergenceIndex-sumLarge {ν = ν} {τ = τ} ε η =
  NatOrder.left-≤-max
    {m = powerSeriesTermwiseBoundIndex ν (quarter⁺ (ε *⁺ η))}
    {n = powerSeriesTermwiseBoundIndex τ (quarter⁺ ε)}


termwiseConvergenceIndex-derivativeValueLarge :
  {ν τ : ℚ⁺ → ℕ} →
  PowerSeriesTermwiseDerivativeValueIndexLarge
    τ
    (termwiseConvergenceIndex ν τ)
termwiseConvergenceIndex-derivativeValueLarge {ν = ν} {τ = τ} ε η =
  NatOrder.right-≤-max
    {n = powerSeriesTermwiseBoundIndex τ (quarter⁺ ε)}
    {m = powerSeriesTermwiseBoundIndex ν (quarter⁺ (ε *⁺ η))}


powerSeriesForwardInBallFromCenterMargin :
  {x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  BoundedByᶜ σ x →
  ((ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  (ε η : ℚ⁺) →
  radius η ℚOrder.≤ radius (μ ε) →
  (h : ℝᶜ) →
  BoundedByᶜ η h →
  BoundedByᶜ ρ (x +ᶜ h)
powerSeriesForwardInBallFromCenterMargin
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  x-bound
  margin
  ε
  η
  η≤με
  h
  h-bound =
  bounded-byᶜ-monotone
    σ+η≤ρ
    (bounded-byᶜ-add σ η x h x-bound h-bound)
  where
  η+σ≤με+σ :
    radius η ℚ.+ radius σ ℚOrder.≤
    radius (μ ε) ℚ.+ radius σ
  η+σ≤με+σ =
    ℚOrder.≤-+o
      (radius η)
      (radius (μ ε))
      (radius σ)
      η≤με

  σ+η≤σ+με :
    radius (σ +⁺ η) ℚOrder.≤ radius (σ +⁺ μ ε)
  σ+η≤σ+με =
    subst2
      ℚOrder._≤_
      (ℚ.+Comm (radius η) (radius σ))
      (ℚ.+Comm (radius (μ ε)) (radius σ))
      η+σ≤με+σ

  σ+η≤ρ :
    radius (σ +⁺ η) ℚOrder.≤ radius ρ
  σ+η≤ρ =
    Rational.≤-trans
      {p = radius (σ +⁺ η)}
      {q = radius (σ +⁺ μ ε)}
      {r = radius ρ}
      σ+η≤σ+με
      (margin ε)


powerSeriesCenterInBallFromMargin :
  {x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  BoundedByᶜ σ x →
  ((ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  BoundedByᶜ ρ x
powerSeriesCenterInBallFromMargin
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  x-bound
  margin =
  bounded-byᶜ-monotone
    σ≤ρ
    x-bound
  where
  σ≤ρ : radius σ ℚOrder.≤ radius ρ
  σ≤ρ =
    Rational.≤-trans
      {p = radius σ}
      {q = radius (σ +⁺ μ 1⁺)}
      {r = radius ρ}
      (summand-left≤sum σ (μ 1⁺))
      (margin 1⁺)


powerSeriesApproximationForwardErrorBoundFromConvergence :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {ν : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a ρ ν) →
  (θ : ℚ⁺) →
  (y : ℝᶜ) →
  (y-bound : BoundedByᶜ ρ y) →
  (n : ℕ) →
  NatOrder._≤_ (powerSeriesTermwiseBoundIndex ν θ) n →
  BoundedByᶜ
    θ
    (powerSeriesSumOnBall a ρ ν convergence y y-bound +ᶜ
      (-ᶜ powerSeriesPartialSum a y n))
powerSeriesApproximationForwardErrorBoundFromConvergence
  {a = a}
  {ρ = ρ}
  {ν = ν}
  convergence
  θ
  y
  y-bound
  n
  index-large =
  close→difference-bounded-byᶜ
    (powerSeriesSumOnBall a ρ ν convergence y y-bound)
    (powerSeriesPartialSum a y n)
    (half< θ)
    sum∼partial
  where
  sum∼partial :
    powerSeriesSumOnBall a ρ ν convergence y y-bound
    ∼[ half⁺ θ ]
    powerSeriesPartialSum a y n
  sum∼partial =
    seriesSumFromFiniteTailBoundConvergesAt
      (powerSeriesTerm a y)
      ν
      (HasPowerSeriesOnBallWith.tailBound convergence y y-bound)
      (HasPowerSeriesOnBallWith.antitoneModulus convergence)
      (half⁺ θ)
      n
      index-large


powerSeriesApproximationReverseErrorBoundFromConvergence :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {ν : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a ρ ν) →
  (θ : ℚ⁺) →
  (y : ℝᶜ) →
  (y-bound : BoundedByᶜ ρ y) →
  (n : ℕ) →
  NatOrder._≤_ (powerSeriesTermwiseBoundIndex ν θ) n →
  BoundedByᶜ
    θ
    (powerSeriesPartialSum a y n +ᶜ
      (-ᶜ powerSeriesSumOnBall a ρ ν convergence y y-bound))
powerSeriesApproximationReverseErrorBoundFromConvergence
  {a = a}
  {ρ = ρ}
  {ν = ν}
  convergence
  θ
  y
  y-bound
  n
  index-large =
  close→difference-bounded-byᶜ
    (powerSeriesPartialSum a y n)
    (powerSeriesSumOnBall a ρ ν convergence y y-bound)
    (half< θ)
    (close-sym sum∼partial)
  where
  sum∼partial :
    powerSeriesSumOnBall a ρ ν convergence y y-bound
    ∼[ half⁺ θ ]
    powerSeriesPartialSum a y n
  sum∼partial =
    seriesSumFromFiniteTailBoundConvergesAt
      (powerSeriesTerm a y)
      ν
      (HasPowerSeriesOnBallWith.tailBound convergence y y-bound)
      (HasPowerSeriesOnBallWith.antitoneModulus convergence)
      (half⁺ θ)
      n
      index-large


powerSeriesPartialSum-one :
  (a : PowerSeries) →
  (y : ℝᶜ) →
  powerSeriesPartialSum a y (suc zero) ≡ a zero
powerSeriesPartialSum-one a y =
  powerSeriesPartialSum-shift a y zero ∙
  cong (a zero +ᶜ_) (mulᶜ-zero-right y) ∙
  add-zero-right (a zero)


powerSeriesConstantPartialSumRemainder-zero :
  (a da : PowerSeries) →
  (x h : ℝᶜ) →
  linearRemainder
    (λ y → powerSeriesPartialSum a y (suc zero))
    x
    (powerSeriesPartialSum da x zero)
    h
  ≡ 0ᶜ
powerSeriesConstantPartialSumRemainder-zero a da x h =
  cong₂
    (λ u v →
      (u +ᶜ (-ᶜ v)) +ᶜ
      (-ᶜ (powerSeriesPartialSum da x zero ·ᶜ h)))
    (powerSeriesPartialSum-one a (x +ᶜ h))
    (powerSeriesPartialSum-one a x) ∙
  SolverHelpers.constant-linear-remainder-zero
    CauchyRealsCommRing
    (a zero)
    h


powerSeriesConstantPartialSumHasDerivativeAtWith :
  {a da : PowerSeries} →
  {x : ℝᶜ} →
  {μ : PrecisionModulus} →
  HasDerivativeAtWith
    (λ y → powerSeriesPartialSum a y (suc zero))
    x
    (powerSeriesPartialSum da x zero)
    μ
powerSeriesConstantPartialSumHasDerivativeAtWith
  {a = a}
  {da = da}
  {x = x}
  ε
  η
  _
  h
  _ =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (sym (powerSeriesConstantPartialSumRemainder-zero a da x h))
    (bounded-byᶜ-zero (ε *⁺ η))


powerSeriesPartialSum-two :
  (a : PowerSeries) →
  (y : ℝᶜ) →
  powerSeriesPartialSum a y (suc (suc zero)) ≡
  a zero +ᶜ y ·ᶜ a (suc zero)
powerSeriesPartialSum-two a y =
  powerSeriesPartialSum-shift a y (suc zero) ∙
  cong
    (λ tail → a zero +ᶜ y ·ᶜ tail)
    (powerSeriesPartialSum-one (shiftPowerSeries a) y)


formalDerivativePartialSum-one :
  (a : PowerSeries) →
  (x : ℝᶜ) →
  powerSeriesPartialSum (derivativePowerSeries a) x (suc zero) ≡
  a (suc zero)
formalDerivativePartialSum-one a x =
  powerSeriesPartialSum-one (derivativePowerSeries a) x ∙
  mulᶜ-one-left (a (suc zero))


naturalReal-suc :
  (n : ℕ) →
  naturalReal (suc n) ≡ naturalReal n +ᶜ 1ᶜ
naturalReal-suc n =
  cong rational (Rational.natMul-suc n Rational.1ℚ) ∙
  sym (add-rational (Rational.natMul n Rational.1ℚ) Rational.1ℚ)


derivativePowerSeries-shift-coefficient :
  (a : PowerSeries) →
  (n : ℕ) →
  shiftPowerSeries (derivativePowerSeries a) n ≡
  addPowerSeries
    (shiftPowerSeries (shiftPowerSeries a))
    (derivativePowerSeries (shiftPowerSeries a))
    n
derivativePowerSeries-shift-coefficient a n =
  cong
    (_·ᶜ a (suc (suc n)))
    (naturalReal-suc (suc n)) ∙
  mulᶜ-distrib-left
    (naturalReal (suc n))
    1ᶜ
    (a (suc (suc n))) ∙
  cong
    (naturalReal (suc n) ·ᶜ a (suc (suc n)) +ᶜ_)
    (mulᶜ-one-left (a (suc (suc n)))) ∙
  add-comm
    (naturalReal (suc n) ·ᶜ a (suc (suc n)))
    (a (suc (suc n)))


powerSeriesDerivativeShiftPartialSum-decomposition :
  (a : PowerSeries) →
  (x : ℝᶜ) →
  (n : ℕ) →
  powerSeriesPartialSum (shiftPowerSeries (derivativePowerSeries a)) x n ≡
  powerSeriesPartialSum (shiftPowerSeries (shiftPowerSeries a)) x n +ᶜ
  powerSeriesPartialSum (derivativePowerSeries (shiftPowerSeries a)) x n
powerSeriesDerivativeShiftPartialSum-decomposition a x n =
  powerSeriesPartialSum-cong
    (derivativePowerSeries-shift-coefficient a)
    refl
    n ∙
  powerSeriesPartialSum-add
    (shiftPowerSeries (shiftPowerSeries a))
    (derivativePowerSeries (shiftPowerSeries a))
    x
    n


powerSeriesFormalDerivativePartialSum-step-value :
  (a : PowerSeries) →
  (x : ℝᶜ) →
  (n : ℕ) →
  powerSeriesPartialSum (derivativePowerSeries a) x (suc n) ≡
  powerSeriesPartialSum (shiftPowerSeries a) x (suc n) +ᶜ
  x ·ᶜ powerSeriesPartialSum (derivativePowerSeries (shiftPowerSeries a)) x n
powerSeriesFormalDerivativePartialSum-step-value a x n =
  powerSeriesPartialSum-shift (derivativePowerSeries a) x n ∙
  cong₂
    _+ᶜ_
    (mulᶜ-one-left (a (suc zero)))
    (cong
      (x ·ᶜ_)
      (powerSeriesDerivativeShiftPartialSum-decomposition a x n)) ∙
  cong
    (a (suc zero) +ᶜ_)
    (mulᶜ-distrib-right x shiftSum derivativeShiftSum) ∙
  add-assoc
    (a (suc zero))
    (x ·ᶜ shiftSum)
    (x ·ᶜ derivativeShiftSum) ∙
  cong
    (_+ᶜ (x ·ᶜ derivativeShiftSum))
    (sym (powerSeriesPartialSum-shift (shiftPowerSeries a) x n))
  where
  shiftSum : ℝᶜ
  shiftSum =
    powerSeriesPartialSum (shiftPowerSeries (shiftPowerSeries a)) x n

  derivativeShiftSum : ℝᶜ
  derivativeShiftSum =
    powerSeriesPartialSum (derivativePowerSeries (shiftPowerSeries a)) x n


powerSeriesLinearPartialSumRemainder-zero :
  (a : PowerSeries) →
  (x h : ℝᶜ) →
  linearRemainder
    (λ y → powerSeriesPartialSum a y (suc (suc zero)))
    x
    (powerSeriesPartialSum (derivativePowerSeries a) x (suc zero))
    h
  ≡ 0ᶜ
powerSeriesLinearPartialSumRemainder-zero a x h =
  cong₂
    (λ u v →
      (u +ᶜ (-ᶜ v)) +ᶜ
      (-ᶜ
        (powerSeriesPartialSum (derivativePowerSeries a) x (suc zero)
          ·ᶜ h)))
    (powerSeriesPartialSum-two a (x +ᶜ h))
    (powerSeriesPartialSum-two a x) ∙
  cong
    (λ d →
      ((a zero +ᶜ (x +ᶜ h) ·ᶜ a (suc zero)) +ᶜ
        (-ᶜ (a zero +ᶜ x ·ᶜ a (suc zero)))) +ᶜ
      (-ᶜ (d ·ᶜ h)))
    (formalDerivativePartialSum-one a x) ∙
  SolverHelpers.linear-partial-sum-remainder-zero
    CauchyRealsCommRing
    (a zero)
    (a (suc zero))
    x
    h


powerSeriesLinearPartialSumHasDerivativeAtWith :
  {a : PowerSeries} →
  {x : ℝᶜ} →
  {μ : PrecisionModulus} →
  HasDerivativeAtWith
    (λ y → powerSeriesPartialSum a y (suc (suc zero)))
    x
    (powerSeriesPartialSum (derivativePowerSeries a) x (suc zero))
    μ
powerSeriesLinearPartialSumHasDerivativeAtWith
  {a = a}
  {x = x}
  ε
  η
  _
  h
  _ =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (sym (powerSeriesLinearPartialSumRemainder-zero a x h))
    (bounded-byᶜ-zero (ε *⁺ η))


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
    (bounded-byᶜ-zero (ε *⁺ η))


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
    (bounded-byᶜ-zero (ε *⁺ η))


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
      (two-half-products≡ ε η)
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
      (scale-product≡ q-bound ε η)
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
      (scale-product≡ κ ε η)
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
      (two-half-products≡ ε η)
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
      (scale-product≡ xhBoundPrecision halfε η)
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
      (scale-precision-cancel δ halfε)
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


powerSeriesPartialSumShiftDerivativeStepModulus :
  ℚ⁺ →
  ℚ⁺ →
  PrecisionModulus →
  PrecisionModulus
powerSeriesPartialSumShiftDerivativeStepModulus σ δ μ ε =
  min⁺
    (identityProductDerivativeModulus σ δ μ (half⁺ ε))
    (identityProductDerivativeModulus σ δ μ (half⁺ ε))


powerSeriesPartialSumShiftDerivativeStepAtWith :
  (σ δ : ℚ⁺) →
  {a da : PowerSeries} →
  {x d : ℝᶜ} →
  {n : ℕ} →
  {μ : PrecisionModulus} →
  BoundedByᶜ σ x →
  BoundedByᶜ δ d →
  HasDerivativeAtWith
    (λ y → powerSeriesPartialSum (shiftPowerSeries a) y n)
    x
    d
    μ →
  powerSeriesPartialSum da x n ≡
  powerSeriesPartialSum (shiftPowerSeries a) x n +ᶜ x ·ᶜ d →
  HasDerivativeAtWith
    (λ y → powerSeriesPartialSum a y (suc n))
    x
    (powerSeriesPartialSum da x n)
    (powerSeriesPartialSumShiftDerivativeStepModulus σ δ μ)
powerSeriesPartialSumShiftDerivativeStepAtWith
  σ
  δ
  {a = a}
  {da = da}
  {x = x}
  {d = d}
  {n = n}
  {μ = μ}
  x-bound
  d-bound
  shiftedDerivative
  derivativeValuePath =
  hasDerivativeAtWith-cong
    (λ y → sym (powerSeriesPartialSum-shift a y n))
    derivative-path
    sumDerivative
  where
  shiftedPartialSum : ℝᶜ → ℝᶜ
  shiftedPartialSum y =
    powerSeriesPartialSum (shiftPowerSeries a) y n

  productDerivativeValue : ℝᶜ
  productDerivativeValue =
    shiftedPartialSum x +ᶜ x ·ᶜ d

  productDerivative :
    HasDerivativeAtWith
      (λ y → y ·ᶜ shiftedPartialSum y)
      x
      productDerivativeValue
      (identityProductDerivativeModulus σ δ μ)
  productDerivative =
    derivativeIdentityMulAtWith
      σ
      δ
      x-bound
      d-bound
      shiftedDerivative

  constantDerivative :
    HasDerivativeAtWith
      (λ _ → a zero)
      x
      0ᶜ
      (identityProductDerivativeModulus σ δ μ)
  constantDerivative =
    derivativeConstantAtWith

  sumDerivative :
    HasDerivativeAtWith
      (λ y → a zero +ᶜ y ·ᶜ shiftedPartialSum y)
      x
      (0ᶜ +ᶜ productDerivativeValue)
      (powerSeriesPartialSumShiftDerivativeStepModulus σ δ μ)
  sumDerivative =
    derivativeAddAtWith constantDerivative productDerivative

  derivative-path :
    0ᶜ +ᶜ productDerivativeValue ≡
    powerSeriesPartialSum da x n
  derivative-path =
    add-zero-left productDerivativeValue ∙
    sym derivativeValuePath


powerSeriesTermwiseDecomposedRemainder :
  (ℝᶜ → ℝᶜ) →
  PowerSeries →
  PowerSeries →
  ℝᶜ →
  ℝᶜ →
  TermwiseDerivativeIndex →
  ℚ⁺ →
  ℚ⁺ →
  ℝᶜ →
  ℝᶜ
powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h =
  ((((f (x +ᶜ h) +ᶜ
      (-ᶜ powerSeriesPartialSum a (x +ᶜ h) (suc n))) +ᶜ
      linearRemainder
        (λ y → powerSeriesPartialSum a y (suc n))
        x
        (powerSeriesPartialSum da x n)
        h) +ᶜ
      (powerSeriesPartialSum a x (suc n) +ᶜ (-ᶜ f x))) +ᶜ
      (-ᶜ
        ((d +ᶜ (-ᶜ powerSeriesPartialSum da x n)) ·ᶜ h)))
  where
  n : ℕ
  n =
    χ ε η


powerSeriesTermwiseRemainderDecomposition :
  (f : ℝᶜ → ℝᶜ) →
  (a da : PowerSeries) →
  (x d : ℝᶜ) →
  (χ : TermwiseDerivativeIndex) →
  (ε η : ℚ⁺) →
  (h : ℝᶜ) →
  linearRemainder f x d h ≡
  powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h
powerSeriesTermwiseRemainderDecomposition f a da x d χ ε η h =
  SolverHelpers.linear-remainder-decomposition
    CauchyRealsCommRing
    (f (x +ᶜ h))
    (f x)
    (powerSeriesPartialSum a (x +ᶜ h) (suc n))
    (powerSeriesPartialSum a x (suc n))
    d
    (powerSeriesPartialSum da x n)
    h
  where
  n : ℕ
  n =
    χ ε η


powerSeriesTermwiseForwardError :
  (ℝᶜ → ℝᶜ) →
  PowerSeries →
  ℝᶜ →
  TermwiseDerivativeIndex →
  ℚ⁺ →
  ℚ⁺ →
  ℝᶜ →
  ℝᶜ
powerSeriesTermwiseForwardError f a x χ ε η h =
  f (x +ᶜ h) +ᶜ
  (-ᶜ powerSeriesPartialSum a (x +ᶜ h) (suc (χ ε η)))


powerSeriesTermwisePartialRemainder :
  PowerSeries →
  PowerSeries →
  ℝᶜ →
  TermwiseDerivativeIndex →
  ℚ⁺ →
  ℚ⁺ →
  ℝᶜ →
  ℝᶜ
powerSeriesTermwisePartialRemainder a da x χ ε η h =
  linearRemainder
    (λ y → powerSeriesPartialSum a y (suc (χ ε η)))
    x
    (powerSeriesPartialSum da x (χ ε η))
    h


powerSeriesTermwiseCenterError :
  (ℝᶜ → ℝᶜ) →
  PowerSeries →
  ℝᶜ →
  TermwiseDerivativeIndex →
  ℚ⁺ →
  ℚ⁺ →
  ℝᶜ
powerSeriesTermwiseCenterError f a x χ ε η =
  powerSeriesPartialSum a x (suc (χ ε η)) +ᶜ (-ᶜ f x)


powerSeriesTermwiseDerivativeLinearError :
  PowerSeries →
  ℝᶜ →
  ℝᶜ →
  TermwiseDerivativeIndex →
  ℚ⁺ →
  ℚ⁺ →
  ℝᶜ →
  ℝᶜ
powerSeriesTermwiseDerivativeLinearError da x d χ ε η h =
  -ᶜ ((d +ᶜ (-ᶜ powerSeriesPartialSum da x (χ ε η))) ·ᶜ h)


PowerSeriesTermwiseDerivativeAtWith :
  (f : ℝᶜ → ℝᶜ) →
  PowerSeries →
  PowerSeries →
  (x d : ℝᶜ) →
  TermwiseDerivativeIndex →
  PrecisionModulus →
  Type₀
PowerSeriesTermwiseDerivativeAtWith f a da x d χ μ =
  Σ[ remainderDecomposition ∈
      ((ε η : ℚ⁺) →
      radius η ℚOrder.≤ radius (μ ε) →
      (h : ℝᶜ) →
      BoundedByᶜ η h →
      linearRemainder f x d h ≡
      powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h) ]
    ((ε η : ℚ⁺) →
      radius η ℚOrder.≤ radius (μ ε) →
      (h : ℝᶜ) →
      BoundedByᶜ η h →
      BoundedByᶜ
        (ε *⁺ η)
        (powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h))


module PowerSeriesTermwiseDerivativeAtWith where
  remainderDecomposition :
    {f : ℝᶜ → ℝᶜ} →
    {a : PowerSeries} →
    {da : PowerSeries} →
    {x d : ℝᶜ} →
    {χ : TermwiseDerivativeIndex} →
    {μ : PrecisionModulus} →
    PowerSeriesTermwiseDerivativeAtWith f a da x d χ μ →
    (ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (μ ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    linearRemainder f x d h ≡
    powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h
  remainderDecomposition derivativeData =
    derivativeData .fst

  decomposedRemainderBound :
    {f : ℝᶜ → ℝᶜ} →
    {a : PowerSeries} →
    {da : PowerSeries} →
    {x d : ℝᶜ} →
    {χ : TermwiseDerivativeIndex} →
    {μ : PrecisionModulus} →
    PowerSeriesTermwiseDerivativeAtWith f a da x d χ μ →
    (ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (μ ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    BoundedByᶜ
      (ε *⁺ η)
      (powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h)
  decomposedRemainderBound derivativeData =
    derivativeData .snd


PowerSeriesTermwiseForwardErrorBoundWith :
  (ℝᶜ → ℝᶜ) →
  PowerSeries →
  ℝᶜ →
  TermwiseDerivativeIndex →
  PrecisionModulus →
  Type₀
PowerSeriesTermwiseForwardErrorBoundWith f a x χ μ =
  (ε η : ℚ⁺) →
  radius η ℚOrder.≤ radius (μ ε) →
  (h : ℝᶜ) →
  BoundedByᶜ η h →
  BoundedByᶜ
    (quarter⁺ (ε *⁺ η))
    (powerSeriesTermwiseForwardError f a x χ ε η h)


PowerSeriesPartialDerivativeRemainderBoundWith :
  PowerSeries →
  PowerSeries →
  ℝᶜ →
  TermwiseDerivativeIndex →
  PrecisionModulus →
  Type₀
PowerSeriesPartialDerivativeRemainderBoundWith a da x χ μ =
  (ε η : ℚ⁺) →
  radius η ℚOrder.≤ radius (μ ε) →
  (h : ℝᶜ) →
  BoundedByᶜ η h →
  BoundedByᶜ
    (quarter⁺ (ε *⁺ η))
    (powerSeriesTermwisePartialRemainder a da x χ ε η h)


PowerSeriesPartialSumsDerivativeModulusLarge :
  TermwiseDerivativeIndex →
  PrecisionModulus →
  (ℕ → PrecisionModulus) →
  Type₀
PowerSeriesPartialSumsDerivativeModulusLarge χ μ ω =
  (ε η : ℚ⁺) →
  radius η ℚOrder.≤ radius (μ ε) →
  radius η ℚOrder.≤ radius (ω (χ ε η) (quarter⁺ ε))


PowerSeriesPartialSumsHaveDerivativeWith :
  PowerSeries →
  PowerSeries →
  ℝᶜ →
  (ℕ → PrecisionModulus) →
  Type₀
PowerSeriesPartialSumsHaveDerivativeWith a da x ω =
  (n : ℕ) →
  HasDerivativeAtWith
    (λ y → powerSeriesPartialSum a y (suc n))
    x
    (powerSeriesPartialSum da x n)
    (ω n)


PowerSeriesFormalPartialSumsHaveDerivativeWith :
  PowerSeries →
  ℝᶜ →
  (ℕ → PrecisionModulus) →
  Type₀
PowerSeriesFormalPartialSumsHaveDerivativeWith a =
  PowerSeriesPartialSumsHaveDerivativeWith a (derivativePowerSeries a)


iteratedShiftPowerSeries :
  ℕ →
  PowerSeries →
  PowerSeries
iteratedShiftPowerSeries zero a =
  a
iteratedShiftPowerSeries (suc n) a =
  shiftPowerSeries (iteratedShiftPowerSeries n a)


iteratedShiftPowerSeries-index :
  (s : ℕ) →
  (a : PowerSeries) →
  (n : ℕ) →
  iteratedShiftPowerSeries s a n ≡ a (s Nat.+ n)
iteratedShiftPowerSeries-index zero a n =
  refl
iteratedShiftPowerSeries-index (suc s) a n =
  iteratedShiftPowerSeries-index s a (suc n) ∙
  cong a (Nat.+-suc s n)


iteratedShiftPowerSeriesCoefficientBounds :
  {a : PowerSeries} →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  (s n : ℕ) →
  BoundedByᶜ
    (κ (s Nat.+ n))
    (iteratedShiftPowerSeries s a n)
iteratedShiftPowerSeriesCoefficientBounds {a = a} κ coefficientBounds s n =
  subst
    (BoundedByᶜ (κ (s Nat.+ n)))
    (sym (iteratedShiftPowerSeries-index s a n))
    (coefficientBounds (s Nat.+ n))


naturalRealBound :
  (n : ℕ) →
  BoundedByᶜ
    (scalar-bound (Rational.natMul n Rational.1ℚ))
    (naturalReal n)
naturalRealBound n =
  rational-bound→boundedᶜ
    (scalar-bound natural)
    natural
    (scalar-bound-rational-boundᶜ natural)
  where
  natural : ℚ
  natural =
    Rational.natMul n Rational.1ℚ


iteratedShiftDerivativePowerSeriesCoefficientBounds :
  {a : PowerSeries} →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  (s n : ℕ) →
  BoundedByᶜ
    (scalar-bound (Rational.natMul (suc n) Rational.1ℚ) *⁺
      κ (s Nat.+ suc n))
    (derivativePowerSeries (iteratedShiftPowerSeries s a) n)
iteratedShiftDerivativePowerSeriesCoefficientBounds {a = a}
    κ coefficientBounds s n =
  bounded-byᶜ-mul
    (scalar-bound natural)
    (κ (s Nat.+ suc n))
    (naturalReal (suc n))
    (iteratedShiftPowerSeries s a (suc n))
    (naturalRealBound (suc n))
    (iteratedShiftPowerSeriesCoefficientBounds κ coefficientBounds s (suc n))
  where
  natural : ℚ
  natural =
    Rational.natMul (suc n) Rational.1ℚ


PowerSeriesIteratedFormalPartialDerivativeBounds :
  PowerSeries →
  ℝᶜ →
  (ℕ → ℕ → ℚ⁺) →
  Type₀
PowerSeriesIteratedFormalPartialDerivativeBounds a x δ =
  (s n : ℕ) →
  BoundedByᶜ
    (δ s n)
    (powerSeriesPartialSum
      (derivativePowerSeries (iteratedShiftPowerSeries s a))
      x
      n)


positivePartialSum :
  (ℕ → ℚ⁺) →
  ℕ →
  ℚ⁺
positivePartialSum κ zero =
  1⁺
positivePartialSum κ (suc n) =
  κ zero +⁺ positivePartialSum (λ k → κ (suc k)) n


partialSumBoundFromTermBounds :
  (u : ℕ → ℝᶜ) →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (u n)) →
  (n : ℕ) →
  BoundedByᶜ (positivePartialSum κ n) (partialSum u n)
partialSumBoundFromTermBounds u κ termBounds zero =
  bounded-byᶜ-zero 1⁺
partialSumBoundFromTermBounds u κ termBounds (suc n) =
  bounded-byᶜ-add
    (κ zero)
    (positivePartialSum (λ k → κ (suc k)) n)
    (u zero)
    (partialSum (λ k → u (suc k)) n)
    (termBounds zero)
    (partialSumBoundFromTermBounds
      (λ k → u (suc k))
      (λ k → κ (suc k))
      (λ k → termBounds (suc k))
      n)


powerSeriesPartialSumBoundFromTermBounds :
  (a : PowerSeries) →
  (x : ℝᶜ) →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (powerSeriesTerm a x n)) →
  (n : ℕ) →
  BoundedByᶜ
    (positivePartialSum κ n)
    (powerSeriesPartialSum a x n)
powerSeriesPartialSumBoundFromTermBounds a x κ termBounds =
  partialSumBoundFromTermBounds (powerSeriesTerm a x) κ termBounds


powerSeriesIteratedFormalPartialDerivativeBoundsFromTermBounds :
  {a : PowerSeries} →
  {x : ℝᶜ} →
  (κ : ℕ → ℕ → ℚ⁺) →
  ((s n : ℕ) →
    BoundedByᶜ
      (κ s n)
      (powerSeriesTerm
        (derivativePowerSeries (iteratedShiftPowerSeries s a))
        x
        n)) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    a
    x
    (λ s n → positivePartialSum (κ s) n)
powerSeriesIteratedFormalPartialDerivativeBoundsFromTermBounds
  {a = a}
  {x = x}
  κ
  termBounds
  s =
  powerSeriesPartialSumBoundFromTermBounds
    (derivativePowerSeries (iteratedShiftPowerSeries s a))
    x
    (κ s)
    (termBounds s)


powerSeriesIteratedFormalPartialDerivativeBoundsFromCoefficientBounds :
  (σ : ℚ⁺) →
  {a : PowerSeries} →
  {x : ℝᶜ} →
  BoundedByᶜ σ x →
  (κ : ℕ → ℕ → ℚ⁺) →
  ((s n : ℕ) →
    BoundedByᶜ
      (κ s n)
      (derivativePowerSeries (iteratedShiftPowerSeries s a) n)) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    a
    x
    (λ s n → positivePartialSum (λ k → κ s k *⁺ positivePower σ k) n)
powerSeriesIteratedFormalPartialDerivativeBoundsFromCoefficientBounds
  σ
  {a = a}
  {x = x}
  x-bound
  κ
  coefficientBounds =
  powerSeriesIteratedFormalPartialDerivativeBoundsFromTermBounds
    (λ s n → κ s n *⁺ positivePower σ n)
    termBounds
  where
  termBounds :
    (s n : ℕ) →
    BoundedByᶜ
      (κ s n *⁺ positivePower σ n)
      (powerSeriesTerm
        (derivativePowerSeries (iteratedShiftPowerSeries s a))
        x
        n)
  termBounds s n =
    bounded-byᶜ-mul
      (κ s n)
      (positivePower σ n)
      (derivativePowerSeries (iteratedShiftPowerSeries s a) n)
      (realPower x n)
      (coefficientBounds s n)
      (realPowerBoundsFromBound σ x x-bound n)


powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds :
  (σ : ℚ⁺) →
  {a : PowerSeries} →
  {x : ℝᶜ} →
  BoundedByᶜ σ x →
  (κ : ℕ → ℚ⁺) →
  ((n : ℕ) → BoundedByᶜ (κ n) (a n)) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    a
    x
    (λ s n →
      positivePartialSum
        (λ k →
          scalar-bound (Rational.natMul (suc k) Rational.1ℚ) *⁺
          κ (s Nat.+ suc k) *⁺
          positivePower σ k)
        n)
powerSeriesIteratedFormalPartialDerivativeBoundsFromSeriesCoefficientBounds
  σ
  {a = a}
  {x = x}
  x-bound
  κ
  coefficientBounds =
  powerSeriesIteratedFormalPartialDerivativeBoundsFromCoefficientBounds
    σ
    x-bound
    (λ s n →
      scalar-bound (Rational.natMul (suc n) Rational.1ℚ) *⁺
      κ (s Nat.+ suc n))
    (iteratedShiftDerivativePowerSeriesCoefficientBounds κ coefficientBounds)


powerSeriesIteratedFormalPartialSumsDerivativeModulus :
  ℚ⁺ →
  (ℕ → ℕ → ℚ⁺) →
  ℕ →
  ℕ →
  PrecisionModulus
powerSeriesIteratedFormalPartialSumsDerivativeModulus σ δ zero s =
  λ _ → 1⁺
powerSeriesIteratedFormalPartialSumsDerivativeModulus σ δ (suc n) s =
  powerSeriesPartialSumShiftDerivativeStepModulus
    σ
    (δ (suc s) n)
    (powerSeriesIteratedFormalPartialSumsDerivativeModulus σ δ n (suc s))


powerSeriesFormalPartialSumsDerivativeModulus :
  ℚ⁺ →
  (ℕ → ℕ → ℚ⁺) →
  ℕ →
  PrecisionModulus
powerSeriesFormalPartialSumsDerivativeModulus σ δ n =
  powerSeriesIteratedFormalPartialSumsDerivativeModulus σ δ n zero


powerSeriesIteratedFormalPartialSumsHaveDerivativeWithFromBounds :
  (σ : ℚ⁺) →
  {a : PowerSeries} →
  {x : ℝᶜ} →
  {δ : ℕ → ℕ → ℚ⁺} →
  BoundedByᶜ σ x →
  PowerSeriesIteratedFormalPartialDerivativeBounds a x δ →
  (n s : ℕ) →
  HasDerivativeAtWith
    (λ y →
      powerSeriesPartialSum (iteratedShiftPowerSeries s a) y (suc n))
    x
    (powerSeriesPartialSum
      (derivativePowerSeries (iteratedShiftPowerSeries s a))
      x
      n)
    (powerSeriesIteratedFormalPartialSumsDerivativeModulus σ δ n s)
powerSeriesIteratedFormalPartialSumsHaveDerivativeWithFromBounds
  σ
  {a = a}
  {x = x}
  {δ = δ}
  x-bound
  derivative-bounds
  zero
  s =
  powerSeriesConstantPartialSumHasDerivativeAtWith
powerSeriesIteratedFormalPartialSumsHaveDerivativeWithFromBounds
  σ
  {a = a}
  {x = x}
  {δ = δ}
  x-bound
  derivative-bounds
  (suc n)
  s =
  powerSeriesPartialSumShiftDerivativeStepAtWith
    σ
    (δ (suc s) n)
    x-bound
    (derivative-bounds (suc s) n)
    (powerSeriesIteratedFormalPartialSumsHaveDerivativeWithFromBounds
      σ
      x-bound
      derivative-bounds
      n
      (suc s))
    (powerSeriesFormalDerivativePartialSum-step-value
      (iteratedShiftPowerSeries s a)
      x
      n)


powerSeriesFormalPartialSumsHaveDerivativeWithFromIteratedBounds :
  (σ : ℚ⁺) →
  {a : PowerSeries} →
  {x : ℝᶜ} →
  {δ : ℕ → ℕ → ℚ⁺} →
  BoundedByᶜ σ x →
  PowerSeriesIteratedFormalPartialDerivativeBounds a x δ →
  PowerSeriesFormalPartialSumsHaveDerivativeWith
    a
    x
    (powerSeriesFormalPartialSumsDerivativeModulus σ δ)
powerSeriesFormalPartialSumsHaveDerivativeWithFromIteratedBounds
  σ
  x-bound
  derivative-bounds
  n =
  powerSeriesIteratedFormalPartialSumsHaveDerivativeWithFromBounds
    σ
    x-bound
    derivative-bounds
    n
    zero


powerSeriesPartialDerivativeRemainderBoundFromPartialSumsDerivative :
  {a da : PowerSeries} →
  {x : ℝᶜ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  {ω : ℕ → PrecisionModulus} →
  PowerSeriesPartialSumsHaveDerivativeWith a da x ω →
  PowerSeriesPartialSumsDerivativeModulusLarge χ μ ω →
  PowerSeriesPartialDerivativeRemainderBoundWith a da x χ μ
powerSeriesPartialDerivativeRemainderBoundFromPartialSumsDerivative
  {a = a}
  {da = da}
  {x = x}
  {χ = χ}
  {ω = ω}
  partialDerivative
  modulus-large
  ε
  η
  η≤με
  h
  h-bound =
  subst
    (λ κ →
      BoundedByᶜ
        κ
        (powerSeriesTermwisePartialRemainder a da x χ ε η h))
    (quarter-product≡ ε η)
    (partialDerivative n (quarter⁺ ε) η η≤ω h h-bound)
  where
  n : ℕ
  n =
    χ ε η

  η≤ω : radius η ℚOrder.≤ radius ((ω n) (quarter⁺ ε))
  η≤ω =
    modulus-large ε η η≤με


powerSeriesFormalPartialDerivativeRemainderBoundFromPartialSumsDerivative :
  {a : PowerSeries} →
  {x : ℝᶜ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  {ω : ℕ → PrecisionModulus} →
  PowerSeriesFormalPartialSumsHaveDerivativeWith a x ω →
  PowerSeriesPartialSumsDerivativeModulusLarge χ μ ω →
  PowerSeriesPartialDerivativeRemainderBoundWith
    a
    (derivativePowerSeries a)
    x
    χ
    μ
powerSeriesFormalPartialDerivativeRemainderBoundFromPartialSumsDerivative =
  powerSeriesPartialDerivativeRemainderBoundFromPartialSumsDerivative


powerSeriesFormalPartialDerivativeRemainderBoundFromIteratedBounds :
  (σ : ℚ⁺) →
  {a : PowerSeries} →
  {x : ℝᶜ} →
  {δ : ℕ → ℕ → ℚ⁺} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  BoundedByᶜ σ x →
  PowerSeriesIteratedFormalPartialDerivativeBounds a x δ →
  PowerSeriesPartialSumsDerivativeModulusLarge
    χ
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus σ δ) →
  PowerSeriesPartialDerivativeRemainderBoundWith
    a
    (derivativePowerSeries a)
    x
    χ
    μ
powerSeriesFormalPartialDerivativeRemainderBoundFromIteratedBounds
  σ
  x-bound
  derivative-bounds
  partialModulus-large =
  powerSeriesFormalPartialDerivativeRemainderBoundFromPartialSumsDerivative
    (powerSeriesFormalPartialSumsHaveDerivativeWithFromIteratedBounds
      σ
      x-bound
      derivative-bounds)
    partialModulus-large


PowerSeriesTermwiseCenterErrorBoundWith :
  (ℝᶜ → ℝᶜ) →
  PowerSeries →
  ℝᶜ →
  TermwiseDerivativeIndex →
  PrecisionModulus →
  Type₀
PowerSeriesTermwiseCenterErrorBoundWith f a x χ μ =
  (ε η : ℚ⁺) →
  radius η ℚOrder.≤ radius (μ ε) →
  (h : ℝᶜ) →
  BoundedByᶜ η h →
  BoundedByᶜ
    (quarter⁺ (ε *⁺ η))
    (powerSeriesTermwiseCenterError f a x χ ε η)


PowerSeriesTermwiseDerivativeLinearErrorBoundWith :
  PowerSeries →
  ℝᶜ →
  ℝᶜ →
  TermwiseDerivativeIndex →
  PrecisionModulus →
  Type₀
PowerSeriesTermwiseDerivativeLinearErrorBoundWith da x d χ μ =
  (ε η : ℚ⁺) →
  radius η ℚOrder.≤ radius (μ ε) →
  (h : ℝᶜ) →
  BoundedByᶜ η h →
  BoundedByᶜ
    (quarter⁺ (ε *⁺ η))
    (powerSeriesTermwiseDerivativeLinearError da x d χ ε η h)


PowerSeriesTermwiseDerivativeValueErrorBoundWith :
  PowerSeries →
  ℝᶜ →
  ℝᶜ →
  TermwiseDerivativeIndex →
  PrecisionModulus →
  Type₀
PowerSeriesTermwiseDerivativeValueErrorBoundWith da x d χ μ =
  (ε η : ℚ⁺) →
  radius η ℚOrder.≤ radius (μ ε) →
  (h : ℝᶜ) →
  BoundedByᶜ η h →
  BoundedByᶜ
    (quarter⁺ ε)
    (d +ᶜ (-ᶜ powerSeriesPartialSum da x (χ ε η)))


PowerSeriesFormalDerivativeValueErrorBoundWith :
  PowerSeries →
  ℝᶜ →
  ℝᶜ →
  TermwiseDerivativeIndex →
  PrecisionModulus →
  Type₀
PowerSeriesFormalDerivativeValueErrorBoundWith a =
  PowerSeriesTermwiseDerivativeValueErrorBoundWith (derivativePowerSeries a)


powerSeriesTermwiseForwardErrorBoundFromConvergence :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {x : ℝᶜ} →
  {ρ : ℚ⁺} →
  {ν : ℚ⁺ → ℕ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  (convergence : HasPowerSeriesOnBallWith a ρ ν) →
  (forwardInBall :
    (ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (μ ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    BoundedByᶜ ρ (x +ᶜ h)) →
  ((ε η : ℚ⁺) →
    (η≤με : radius η ℚOrder.≤ radius (μ ε)) →
    (h : ℝᶜ) →
    (h-bound : BoundedByᶜ η h) →
    f (x +ᶜ h) ≡
    powerSeriesSumOnBall
      a
      ρ
      ν
      convergence
      (x +ᶜ h)
      (forwardInBall ε η η≤με h h-bound)) →
  PowerSeriesTermwiseSumBoundIndexLarge ν χ →
  PowerSeriesTermwiseForwardErrorBoundWith f a x χ μ
powerSeriesTermwiseForwardErrorBoundFromConvergence
  {f = f}
  {a = a}
  {x = x}
  {ρ = ρ}
  {ν = ν}
  {χ = χ}
  convergence
  forwardInBall
  expansion
  index-large
  ε
  η
  η≤με
  h
  h-bound =
  subst
    (λ z →
      BoundedByᶜ
        piecePrecision
        (z +ᶜ (-ᶜ powerSeriesPartialSum a (x +ᶜ h) (suc n))))
    (sym (expansion ε η η≤με h h-bound))
    sumErrorBound
  where
  piecePrecision : ℚ⁺
  piecePrecision =
    quarter⁺ (ε *⁺ η)

  n : ℕ
  n =
    χ ε η

  y-bound : BoundedByᶜ ρ (x +ᶜ h)
  y-bound =
    forwardInBall ε η η≤με h h-bound

  sumErrorBound :
    BoundedByᶜ
      piecePrecision
      (powerSeriesSumOnBall a ρ ν convergence (x +ᶜ h) y-bound +ᶜ
        (-ᶜ powerSeriesPartialSum a (x +ᶜ h) (suc n)))
  sumErrorBound =
    powerSeriesApproximationForwardErrorBoundFromConvergence
      convergence
      piecePrecision
      (x +ᶜ h)
      y-bound
      (suc n)
      (NatOrder.≤-trans (index-large ε η) (n≤sucn n))


powerSeriesTermwiseCenterErrorBoundFromConvergence :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {x : ℝᶜ} →
  {ρ : ℚ⁺} →
  {ν : ℚ⁺ → ℕ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  (convergence : HasPowerSeriesOnBallWith a ρ ν) →
  (x-bound : BoundedByᶜ ρ x) →
  f x ≡ powerSeriesSumOnBall a ρ ν convergence x x-bound →
  PowerSeriesTermwiseSumBoundIndexLarge ν χ →
  PowerSeriesTermwiseCenterErrorBoundWith f a x χ μ
powerSeriesTermwiseCenterErrorBoundFromConvergence
  {f = f}
  {a = a}
  {x = x}
  {ρ = ρ}
  {ν = ν}
  {χ = χ}
  convergence
  x-bound
  expansion
  index-large
  ε
  η
  _
  h
  _ =
  subst
    (λ z →
      BoundedByᶜ
        piecePrecision
        (powerSeriesPartialSum a x (suc n) +ᶜ (-ᶜ z)))
    (sym expansion)
    reverseErrorBound
  where
  piecePrecision : ℚ⁺
  piecePrecision =
    quarter⁺ (ε *⁺ η)

  n : ℕ
  n =
    χ ε η

  reverseErrorBound :
    BoundedByᶜ
      piecePrecision
      (powerSeriesPartialSum a x (suc n) +ᶜ
        (-ᶜ powerSeriesSumOnBall a ρ ν convergence x x-bound))
  reverseErrorBound =
    powerSeriesApproximationReverseErrorBoundFromConvergence
      convergence
      piecePrecision
      x
      x-bound
      (suc n)
      (NatOrder.≤-trans (index-large ε η) (n≤sucn n))


powerSeriesTermwiseDerivativeValueErrorBoundFromConvergence :
  {da : PowerSeries} →
  {x d : ℝᶜ} →
  {ρ : ℚ⁺} →
  {ν : ℚ⁺ → ℕ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  (convergence : HasPowerSeriesOnBallWith da ρ ν) →
  (x-bound : BoundedByᶜ ρ x) →
  d ≡ powerSeriesSumOnBall da ρ ν convergence x x-bound →
  PowerSeriesTermwiseDerivativeValueIndexLarge ν χ →
  PowerSeriesTermwiseDerivativeValueErrorBoundWith da x d χ μ
powerSeriesTermwiseDerivativeValueErrorBoundFromConvergence
  {da = da}
  {x = x}
  {d = d}
  {ρ = ρ}
  {ν = ν}
  {χ = χ}
  convergence
  x-bound
  valuePath
  index-large
  ε
  η
  _
  h
  _ =
  subst
    (λ z →
      BoundedByᶜ
        piecePrecision
        (z +ᶜ (-ᶜ powerSeriesPartialSum da x n)))
    (sym valuePath)
    sumErrorBound
  where
  piecePrecision : ℚ⁺
  piecePrecision =
    quarter⁺ ε

  n : ℕ
  n =
    χ ε η

  sumErrorBound :
    BoundedByᶜ
      piecePrecision
      (powerSeriesSumOnBall da ρ ν convergence x x-bound +ᶜ
        (-ᶜ powerSeriesPartialSum da x n))
  sumErrorBound =
    powerSeriesApproximationForwardErrorBoundFromConvergence
      convergence
      piecePrecision
      x
      x-bound
      n
      (index-large ε η)


powerSeriesFormalDerivativeValueErrorBoundFromConvergence :
  {a : PowerSeries} →
  {x d : ℝᶜ} →
  {ρ : ℚ⁺} →
  {ν : ℚ⁺ → ℕ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  (convergence : HasPowerSeriesOnBallWith (derivativePowerSeries a) ρ ν) →
  (x-bound : BoundedByᶜ ρ x) →
  d ≡
  powerSeriesSumOnBall
    (derivativePowerSeries a)
    ρ
    ν
    convergence
    x
    x-bound →
  PowerSeriesTermwiseDerivativeValueIndexLarge ν χ →
  PowerSeriesFormalDerivativeValueErrorBoundWith a x d χ μ
powerSeriesFormalDerivativeValueErrorBoundFromConvergence =
  powerSeriesTermwiseDerivativeValueErrorBoundFromConvergence


derivativeValueErrorBound→linearErrorBound :
  {da : PowerSeries} →
  {x d : ℝᶜ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  PowerSeriesTermwiseDerivativeValueErrorBoundWith da x d χ μ →
  PowerSeriesTermwiseDerivativeLinearErrorBoundWith da x d χ μ
derivativeValueErrorBound→linearErrorBound
  {da = da}
  {x = x}
  {d = d}
  {χ = χ}
  derivativeValueBound
  ε
  η
  η≤με
  h
  h-bound =
  subst
    (λ κ →
      BoundedByᶜ
        κ
        (powerSeriesTermwiseDerivativeLinearError da x d χ ε η h))
    (quarter-product≡ ε η)
    (bounded-byᶜ-neg
      (quarter⁺ ε *⁺ η)
      (derivativeErrorTerm ·ᶜ h)
      (bounded-byᶜ-mul
        (quarter⁺ ε)
        η
        derivativeErrorTerm
        h
        derivativeErrorBound
        h-bound))
  where
  derivativeErrorTerm : ℝᶜ
  derivativeErrorTerm =
    d +ᶜ (-ᶜ powerSeriesPartialSum da x (χ ε η))

  derivativeErrorBound :
    BoundedByᶜ (quarter⁺ ε) derivativeErrorTerm
  derivativeErrorBound =
    derivativeValueBound ε η η≤με h h-bound


abstract
  powerSeriesTermwisePieceBounds→decomposedRemainderBound :
    {f : ℝᶜ → ℝᶜ} →
    {a da : PowerSeries} →
    {x d : ℝᶜ} →
    {χ : TermwiseDerivativeIndex} →
    {μ : PrecisionModulus} →
    PowerSeriesTermwiseForwardErrorBoundWith f a x χ μ →
    PowerSeriesPartialDerivativeRemainderBoundWith a da x χ μ →
    PowerSeriesTermwiseCenterErrorBoundWith f a x χ μ →
    PowerSeriesTermwiseDerivativeLinearErrorBoundWith da x d χ μ →
    (ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (μ ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    BoundedByᶜ
      (ε *⁺ η)
      (powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h)
  powerSeriesTermwisePieceBounds→decomposedRemainderBound
    {f = f}
    {a = a}
    {da = da}
    {x = x}
    {d = d}
    {χ = χ}
    forwardBoundWith
    partialBoundWith
    centerBoundWith
    derivativeLinearBoundWith
    ε
    η
    η≤με
    h
    h-bound =
    subst
      (λ κ →
        BoundedByᶜ
          κ
          (powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h))
      (four-quarters≡ (ε *⁺ η))
      combinedBound
    where
    piecePrecision : ℚ⁺
    piecePrecision =
      quarter⁺ (ε *⁺ η)

    forwardTerm : ℝᶜ
    forwardTerm =
      powerSeriesTermwiseForwardError f a x χ ε η h

    partialTerm : ℝᶜ
    partialTerm =
      powerSeriesTermwisePartialRemainder a da x χ ε η h

    centerTerm : ℝᶜ
    centerTerm =
      powerSeriesTermwiseCenterError f a x χ ε η

    derivativeLinearTerm : ℝᶜ
    derivativeLinearTerm =
      powerSeriesTermwiseDerivativeLinearError da x d χ ε η h

    forwardBound :
      BoundedByᶜ piecePrecision forwardTerm
    forwardBound =
      forwardBoundWith ε η η≤με h h-bound

    partialBound :
      BoundedByᶜ piecePrecision partialTerm
    partialBound =
      partialBoundWith ε η η≤με h h-bound

    centerBound :
      BoundedByᶜ piecePrecision centerTerm
    centerBound =
      centerBoundWith ε η η≤με h h-bound

    derivativeLinearBound :
      BoundedByᶜ piecePrecision derivativeLinearTerm
    derivativeLinearBound =
      derivativeLinearBoundWith ε η η≤με h h-bound

    firstTwoBound :
      BoundedByᶜ
        (piecePrecision +⁺ piecePrecision)
        (forwardTerm +ᶜ partialTerm)
    firstTwoBound =
      bounded-byᶜ-add
        piecePrecision
        piecePrecision
        forwardTerm
        partialTerm
        forwardBound
        partialBound

    firstThreeBound :
      BoundedByᶜ
        ((piecePrecision +⁺ piecePrecision) +⁺ piecePrecision)
        ((forwardTerm +ᶜ partialTerm) +ᶜ centerTerm)
    firstThreeBound =
      bounded-byᶜ-add
        (piecePrecision +⁺ piecePrecision)
        piecePrecision
        (forwardTerm +ᶜ partialTerm)
        centerTerm
        firstTwoBound
        centerBound

    combinedBound :
      BoundedByᶜ
        (((piecePrecision +⁺ piecePrecision) +⁺ piecePrecision) +⁺
          piecePrecision)
        (powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h)
    combinedBound =
      bounded-byᶜ-add
        ((piecePrecision +⁺ piecePrecision) +⁺ piecePrecision)
        piecePrecision
        ((forwardTerm +ᶜ partialTerm) +ᶜ centerTerm)
        derivativeLinearTerm
        firstThreeBound
        derivativeLinearBound


powerSeriesTermwiseDerivativeAtWithFromPieceBounds :
  {f : ℝᶜ → ℝᶜ} →
  {a da : PowerSeries} →
  {x d : ℝᶜ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  ((ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (μ ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    linearRemainder f x d h ≡
    powerSeriesTermwiseDecomposedRemainder f a da x d χ ε η h) →
  PowerSeriesTermwiseForwardErrorBoundWith f a x χ μ →
  PowerSeriesPartialDerivativeRemainderBoundWith a da x χ μ →
  PowerSeriesTermwiseCenterErrorBoundWith f a x χ μ →
  PowerSeriesTermwiseDerivativeLinearErrorBoundWith da x d χ μ →
  PowerSeriesTermwiseDerivativeAtWith f a da x d χ μ
powerSeriesTermwiseDerivativeAtWithFromPieceBounds
  remainderDecomposition
  forwardBound
  partialBound
  centerBound
  derivativeLinearBound =
  remainderDecomposition ,
  powerSeriesTermwisePieceBounds→decomposedRemainderBound
    forwardBound
    partialBound
    centerBound
    derivativeLinearBound


powerSeriesTermwiseDerivativeAtWithFromCanonicalPieceBounds :
  {f : ℝᶜ → ℝᶜ} →
  {a da : PowerSeries} →
  {x d : ℝᶜ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  PowerSeriesTermwiseForwardErrorBoundWith f a x χ μ →
  PowerSeriesPartialDerivativeRemainderBoundWith a da x χ μ →
  PowerSeriesTermwiseCenterErrorBoundWith f a x χ μ →
  PowerSeriesTermwiseDerivativeLinearErrorBoundWith da x d χ μ →
  PowerSeriesTermwiseDerivativeAtWith f a da x d χ μ
powerSeriesTermwiseDerivativeAtWithFromCanonicalPieceBounds
  {f = f}
  {a = a}
  {da = da}
  {x = x}
  {d = d}
  {χ = χ}
  forwardBound
  partialBound
  centerBound
  derivativeLinearBound =
  powerSeriesTermwiseDerivativeAtWithFromPieceBounds
    (λ ε η _ h _ →
      powerSeriesTermwiseRemainderDecomposition f a da x d χ ε η h)
    forwardBound
    partialBound
    centerBound
    derivativeLinearBound


powerSeriesTermwiseDerivativeAtWithFromCanonicalValueBounds :
  {f : ℝᶜ → ℝᶜ} →
  {a da : PowerSeries} →
  {x d : ℝᶜ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  PowerSeriesTermwiseForwardErrorBoundWith f a x χ μ →
  PowerSeriesPartialDerivativeRemainderBoundWith a da x χ μ →
  PowerSeriesTermwiseCenterErrorBoundWith f a x χ μ →
  PowerSeriesTermwiseDerivativeValueErrorBoundWith da x d χ μ →
  PowerSeriesTermwiseDerivativeAtWith f a da x d χ μ
powerSeriesTermwiseDerivativeAtWithFromCanonicalValueBounds
  forwardBound
  partialBound
  centerBound
  derivativeValueBound =
  powerSeriesTermwiseDerivativeAtWithFromCanonicalPieceBounds
    forwardBound
    partialBound
    centerBound
    (derivativeValueErrorBound→linearErrorBound derivativeValueBound)


powerSeriesTermwiseDerivativeAtWith→hasDerivativeAtWith :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {da : PowerSeries} →
  {x d : ℝᶜ} →
  {χ : TermwiseDerivativeIndex} →
  {μ : PrecisionModulus} →
  PowerSeriesTermwiseDerivativeAtWith f a da x d χ μ →
  HasDerivativeAtWith f x d μ
powerSeriesTermwiseDerivativeAtWith→hasDerivativeAtWith
  {f = f}
  {a = a}
  {x = x}
  {d = d}
  {χ = χ}
  derivativeData
  ε
  η
  η≤με
  h
  h-bound =
  subst
    (BoundedByᶜ (ε *⁺ η))
    (sym
      (PowerSeriesTermwiseDerivativeAtWith.remainderDecomposition
        derivativeData
        ε
        η
        η≤με
        h
        h-bound))
    (PowerSeriesTermwiseDerivativeAtWith.decomposedRemainderBound
      derivativeData
      ε
      η
      η≤με
      h
      h-bound)



hasDerivativeAtWith-derivative-path :
  {f : ℝᶜ → ℝᶜ} →
  {x d e : ℝᶜ} →
  {μ : PrecisionModulus} →
  d ≡ e →
  HasDerivativeAtWith f x d μ →
  HasDerivativeAtWith f x e μ
hasDerivativeAtWith-derivative-path {f = f} {x = x} {μ = μ} d≡e =
  subst (λ D → HasDerivativeAtWith f x D μ) d≡e


linearRemainder-center-translate :
  (f : ℝᶜ → ℝᶜ) →
  (c x d h : ℝᶜ) →
  linearRemainder
    (λ y → f (c +ᶜ y))
    (centeredDisplacement c x)
    d
    h
  ≡
  linearRemainder f x d h
linearRemainder-center-translate f c x d h =
  cong₂
    (λ forward base →
      (f forward +ᶜ (-ᶜ f base)) +ᶜ (-ᶜ (d ·ᶜ h)))
    (add-center-centeredDisplacement-forward c x h)
    (add-center-centeredDisplacement c x)


hasDerivativeAtWith-center-translate :
  {f : ℝᶜ → ℝᶜ} →
  {c x d : ℝᶜ} →
  {μ : PrecisionModulus} →
  HasDerivativeAtWith
    (λ y → f (c +ᶜ y))
    (centeredDisplacement c x)
    d
    μ →
  HasDerivativeAtWith f x d μ
hasDerivativeAtWith-center-translate
  {f = f}
  {c = c}
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
    (linearRemainder-center-translate f c x d h)
    (derivative ε η η≤με h h-bound)


centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith :
  {a b : PowerSeries} →
  {c x : ℝᶜ} →
  {ρ σ : ℚ⁺} →
  {μ : PrecisionModulus} →
  {δ : ℕ → ℕ → ℚ⁺} →
  ((n : ℕ) → derivativePowerSeries a n ≡ b n) →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (derivativeRadius :
    HasInfinitePowerSeriesRadius (derivativePowerSeries a)) →
  (targetRadius : HasInfinitePowerSeriesRadius b) →
  (x-displacement-bound : BoundedByᶜ σ (centeredDisplacement c x)) →
  (margin : (ε : ℚ⁺) → radius (σ +⁺ μ ε) ℚOrder.≤ radius ρ) →
  PowerSeriesIteratedFormalPartialDerivativeBounds
    a
    (centeredDisplacement c x)
    δ →
  PowerSeriesPartialSumsDerivativeModulusLarge
    (termwiseConvergenceIndex
      (radiusData ρ .fst)
      (derivativeRadius σ .fst))
    μ
    (powerSeriesFormalPartialSumsDerivativeModulus σ δ) →
  HasDerivativeAtWith
    (centeredPowerSeriesSumEverywhere a c radiusData)
    x
    (centeredPowerSeriesSumEverywhere b c targetRadius x)
    μ
centeredPowerSeriesSumEverywhereFormalTermwiseDerivativeFromCoefficientPathAndIteratedBoundsOnSubballCanonicalIndex→hasDerivativeAtWith
  {a = a}
  {b = b}
  {c = c}
  {x = x}
  {ρ = ρ}
  {σ = σ}
  {μ = μ}
  {δ = δ}
  coeff≡
  radiusData
  derivativeRadius
  targetRadius
  x-displacement-bound
  margin
  derivative-bounds
  partialModulus-large =
  hasDerivativeAtWith-derivative-path
    derivativeValuePath
    (hasDerivativeAtWith-center-translate translatedDerivative)
  where
  ν : ℚ⁺ → ℕ
  ν =
    radiusData ρ .fst

  convergence : HasPowerSeriesOnBallWith a ρ ν
  convergence =
    radiusData ρ .snd

  τ : ℚ⁺ → ℕ
  τ =
    derivativeRadius σ .fst

  derivativeConvergence :
    HasPowerSeriesOnBallWith (derivativePowerSeries a) σ τ
  derivativeConvergence =
    derivativeRadius σ .snd

  χ : TermwiseDerivativeIndex
  χ =
    termwiseConvergenceIndex ν τ

  z : ℝᶜ
  z =
    centeredDisplacement c x

  derivativeLocalValue : ℝᶜ
  derivativeLocalValue =
    centeredPowerSeriesSumOnBall
      (derivativePowerSeries a)
      0ᶜ
      σ
      τ
      derivativeConvergence
      z
      (inPowerSeriesBallAtZeroFromBound x-displacement-bound)

  forwardInBall :
    (ε η : ℚ⁺) →
    radius η ℚOrder.≤ radius (μ ε) →
    (h : ℝᶜ) →
    BoundedByᶜ η h →
    BoundedByᶜ ρ (z +ᶜ h)
  forwardInBall =
    powerSeriesForwardInBallFromCenterMargin x-displacement-bound margin

  centerBound : BoundedByᶜ ρ z
  centerBound =
    powerSeriesCenterInBallFromMargin x-displacement-bound margin

  forwardExpansion :
    (ε η : ℚ⁺) →
    (η≤με : radius η ℚOrder.≤ radius (μ ε)) →
    (h : ℝᶜ) →
    (h-bound : BoundedByᶜ η h) →
    centeredPowerSeriesSumEverywhere a c radiusData (c +ᶜ (z +ᶜ h)) ≡
    powerSeriesSumOnBall
      a
      ρ
      ν
      convergence
      (z +ᶜ h)
      (forwardInBall ε η η≤με h h-bound)
  forwardExpansion ε η η≤με h h-bound =
    centeredPowerSeriesSumEverywhere-bound-path
      a
      c
      radiusData
      ρ
      (c +ᶜ (z +ᶜ h))
      (inPowerSeriesBallAtCenterPlusFromBound c y-bound) ∙
    centeredPowerSeriesSumOnBallAtCenterPlus-path
      convergence
      c
      (z +ᶜ h)
      y-bound
    where
    y-bound : BoundedByᶜ ρ (z +ᶜ h)
    y-bound =
      forwardInBall ε η η≤με h h-bound

  centerExpansion :
    centeredPowerSeriesSumEverywhere a c radiusData (c +ᶜ z) ≡
    powerSeriesSumOnBall a ρ ν convergence z centerBound
  centerExpansion =
    centeredPowerSeriesSumEverywhere-bound-path
      a
      c
      radiusData
      ρ
      (c +ᶜ z)
      (inPowerSeriesBallAtCenterPlusFromBound c centerBound) ∙
    centeredPowerSeriesSumOnBallAtCenterPlus-path
      convergence
      c
      z
      centerBound

  forwardBound :
    PowerSeriesTermwiseForwardErrorBoundWith
      (λ y → centeredPowerSeriesSumEverywhere a c radiusData (c +ᶜ y))
      a
      z
      χ
      μ
  forwardBound =
    powerSeriesTermwiseForwardErrorBoundFromConvergence
      convergence
      forwardInBall
      forwardExpansion
      (termwiseConvergenceIndex-sumLarge {ν = ν} {τ = τ})

  centerErrorBound :
    PowerSeriesTermwiseCenterErrorBoundWith
      (λ y → centeredPowerSeriesSumEverywhere a c radiusData (c +ᶜ y))
      a
      z
      χ
      μ
  centerErrorBound =
    powerSeriesTermwiseCenterErrorBoundFromConvergence
      convergence
      centerBound
      centerExpansion
      (termwiseConvergenceIndex-sumLarge {ν = ν} {τ = τ})

  partialBound :
    PowerSeriesPartialDerivativeRemainderBoundWith
      a
      (derivativePowerSeries a)
      z
      χ
      μ
  partialBound =
    powerSeriesFormalPartialDerivativeRemainderBoundFromIteratedBounds
      σ
      x-displacement-bound
      derivative-bounds
      partialModulus-large

  derivativeValueAtZeroPath :
    derivativeLocalValue ≡
    powerSeriesSumOnBall
      (derivativePowerSeries a)
      σ
      τ
      derivativeConvergence
      z
      x-displacement-bound
  derivativeValueAtZeroPath =
    centeredPowerSeriesSumOnBallAtZero-path
      derivativeConvergence
      z
      x-displacement-bound

  derivativeValueBound :
    PowerSeriesFormalDerivativeValueErrorBoundWith a z derivativeLocalValue χ μ
  derivativeValueBound =
    powerSeriesFormalDerivativeValueErrorBoundFromConvergence
      derivativeConvergence
      x-displacement-bound
      derivativeValueAtZeroPath
      (termwiseConvergenceIndex-derivativeValueLarge {ν = ν} {τ = τ})

  translatedDerivative :
    HasDerivativeAtWith
      (λ y → centeredPowerSeriesSumEverywhere a c radiusData (c +ᶜ y))
      z
      derivativeLocalValue
      μ
  translatedDerivative =
    powerSeriesTermwiseDerivativeAtWith→hasDerivativeAtWith
      (powerSeriesTermwiseDerivativeAtWithFromCanonicalValueBounds
        forwardBound
        partialBound
        centerErrorBound
        derivativeValueBound)

  derivativeValuePath :
    derivativeLocalValue ≡
    centeredPowerSeriesSumEverywhere b c targetRadius x
  derivativeValuePath =
    centeredPowerSeriesSumOnBallAtZero-path
      derivativeConvergence
      z
      x-displacement-bound ∙
    sym
      (centeredPowerSeriesSumEverywhere-bound-path
        (derivativePowerSeries a)
        c
        derivativeRadius
        σ
        x
        (record { displacementBound = x-displacement-bound })) ∙
    centeredPowerSeriesSumEverywhere-coefficients-path
      coeff≡
      derivativeRadius
      targetRadius
      c
      x

PowerSeriesTermwiseDerivativeAt :
  (ℝᶜ → ℝᶜ) →
  PowerSeries →
  PowerSeries →
  ℝᶜ →
  ℝᶜ →
  Type₀
PowerSeriesTermwiseDerivativeAt f a da x d =
  Σ[ χ ∈ TermwiseDerivativeIndex ]
    Σ[ μ ∈ PrecisionModulus ]
      PowerSeriesTermwiseDerivativeAtWith f a da x d χ μ


PowerSeriesFormalTermwiseDerivativeAtWith :
  (ℝᶜ → ℝᶜ) →
  PowerSeries →
  (x d : ℝᶜ) →
  TermwiseDerivativeIndex →
  PrecisionModulus →
  Type₀
PowerSeriesFormalTermwiseDerivativeAtWith f a =
  PowerSeriesTermwiseDerivativeAtWith f a (derivativePowerSeries a)


PowerSeriesFormalTermwiseDerivativeAt :
  (ℝᶜ → ℝᶜ) →
  PowerSeries →
  ℝᶜ →
  ℝᶜ →
  Type₀
PowerSeriesFormalTermwiseDerivativeAt f a =
  PowerSeriesTermwiseDerivativeAt f a (derivativePowerSeries a)


powerSeriesTermwiseDerivativeAt→hasDerivativeAt :
  {f : ℝᶜ → ℝᶜ} →
  {a : PowerSeries} →
  {da : PowerSeries} →
  {x d : ℝᶜ} →
  PowerSeriesTermwiseDerivativeAt f a da x d →
  HasDerivativeAt f x d
powerSeriesTermwiseDerivativeAt→hasDerivativeAt (χ , μ , derivativeData) =
  μ ,
  powerSeriesTermwiseDerivativeAtWith→hasDerivativeAtWith
    {χ = χ}
    derivativeData
