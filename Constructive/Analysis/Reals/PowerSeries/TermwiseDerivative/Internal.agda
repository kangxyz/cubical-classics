{-

Termwise derivative criterion for power-series sums

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.TermwiseDerivative.Internal where

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
