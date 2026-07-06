{-

Algebra of limits for Cauchy-real sequences

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Sequences.Algebra where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Nat.Order as NatOrder
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Base
open import Constructive.Analysis.Metric.Instances.CauchyReals
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Internal.BoundedMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Internal.BoundedReciprocal
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ScalarMultiplication
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.Sequences.Base
open import Constructive.Analysis.Reals.Sequences.Convergence
open import Constructive.Analysis.Reals.Sequences.Map
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open ClosenessOf RationalsMetricSpace

private
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

  scaledHalf< :
    (κ ε : ℚ⁺) →
    κ *⁺ half⁺ (posInv⁺ κ *⁺ ε) <⁺ ε
  scaledHalf< κ ε =
    subst
      (λ ρ → κ *⁺ half⁺ (posInv⁺ κ *⁺ ε) <⁺ ρ)
      (scale-precision-cancel κ ε)
      (scale-precision-mono
        κ
        (half⁺ (posInv⁺ κ *⁺ ε))
        (posInv⁺ κ *⁺ ε)
        (half< (posInv⁺ κ *⁺ ε)))

  scaledHalfModulus :
    ℚ⁺ →
    NatModulus →
    NatModulus
  scaledHalfModulus κ μ ε =
    μ (half⁺ (posInv⁺ κ *⁺ half⁺ ε))


zeroSequence : Sequence
zeroSequence =
  constantSequence 0ᶜ


oneSequence : Sequence
oneSequence =
  constantSequence 1ᶜ


addSequence : Sequence → Sequence → Sequence
addSequence u v n =
  u n +ᶜ v n


negSequence : Sequence → Sequence
negSequence u n =
  -ᶜ u n


subSequence : Sequence → Sequence → Sequence
subSequence u v n =
  u n +ᶜ (-ᶜ v n)


scalarMulSequence : ℚ → Sequence → Sequence
scalarMulSequence q u n =
  scalarMulᶜ q (u n)


mulSequence : Sequence → Sequence → Sequence
mulSequence u v n =
  u n ·ᶜ v n


mulLeftSequence : Sequence → ℝᶜ → Sequence
mulLeftSequence u y n =
  u n ·ᶜ y


mulRightSequence : ℝᶜ → Sequence → Sequence
mulRightSequence x v n =
  x ·ᶜ v n


EventuallyBoundedByWith :
  NatModulus →
  ℚ⁺ →
  Sequence →
  Type₀
EventuallyBoundedByWith μ κ u =
  (ε : ℚ⁺) →
  (n : ℕ) →
  NatOrder._≤_ (μ ε) n →
  BoundedByᶜ κ (u n)


positiveReciprocalSequence :
  (ε : ℚ⁺) →
  (u : Sequence) →
  ((n : ℕ) → BoundedAwayPositiveᶜ ε (u n)) →
  Sequence
positiveReciprocalSequence ε u u-away n =
  boundedAwayReciprocalᶜ ε (u n) (u-away n)


BoundedAwayNegativeᶜ :
  ℚ⁺ →
  ℝᶜ →
  Type₀
BoundedAwayNegativeᶜ ε x =
  BoundedAwayPositiveᶜ ε (-ᶜ x)


EventuallyBoundedAwayPositiveWith :
  NatModulus →
  ℚ⁺ →
  Sequence →
  Type₀
EventuallyBoundedAwayPositiveWith μ ε u =
  (δ : ℚ⁺) →
  (n : ℕ) →
  NatOrder._≤_ (μ δ) n →
  BoundedAwayPositiveᶜ ε (u n)


EventuallyBoundedAwayNegativeWith :
  NatModulus →
  ℚ⁺ →
  Sequence →
  Type₀
EventuallyBoundedAwayNegativeWith μ ε u =
  (δ : ℚ⁺) →
  (n : ℕ) →
  NatOrder._≤_ (μ δ) n →
  BoundedAwayNegativeᶜ ε (u n)


negativeReciprocalSequence :
  (ε : ℚ⁺) →
  (u : Sequence) →
  ((n : ℕ) → BoundedAwayNegativeᶜ ε (u n)) →
  Sequence
negativeReciprocalSequence ε u u-away =
  negSequence (positiveReciprocalSequence ε (negSequence u) u-away)


zeroSequenceConvergesTo :
  ConvergesTo zeroSequence 0ᶜ
zeroSequenceConvergesTo =
  constantConvergesTo 0ᶜ


oneSequenceConvergesTo :
  ConvergesTo oneSequence 1ᶜ
oneSequenceConvergesTo =
  constantConvergesTo 1ᶜ


addConvergesWithModulus :
  {u v : Sequence} →
  {x y : ℝᶜ} →
  {μ ν : NatModulus} →
  ConvergesWithModulus u x μ →
  ConvergesWithModulus v y ν →
  ConvergesWithModulus
    (addSequence u v)
    (x +ᶜ y)
    (λ ε → maxModulus μ ν (half⁺ ε))
addConvergesWithModulus {u = u} {v = v} {x = x} {y = y} {μ = μ} {ν = ν} u→x v→y ε n max≤n =
  subst
    (λ ρ → (u n +ᶜ v n) ∼[ ρ ] (x +ᶜ y))
    (half⁺+half⁺≡ ε)
    (add-close
      (u→x α n μ≤n)
      (v→y α n ν≤n))
  where
  α : ℚ⁺
  α =
    half⁺ ε

  μ≤n : NatOrder._≤_ (μ α) n
  μ≤n =
    NatOrder.≤-trans
      (maxModulus-left≤ μ ν α)
      max≤n

  ν≤n : NatOrder._≤_ (ν α) n
  ν≤n =
    NatOrder.≤-trans
      (maxModulus-right≤ μ ν α)
      max≤n


addConvergesTo :
  {u v : Sequence} →
  {x y : ℝᶜ} →
  ConvergesTo u x →
  ConvergesTo v y →
  ConvergesTo (addSequence u v) (x +ᶜ y)
addConvergesTo (μ , u→x) (ν , v→y) =
  (λ ε → maxModulus μ ν (half⁺ ε)) ,
  addConvergesWithModulus u→x v→y


negConvergesWithModulus :
  {u : Sequence} →
  {x : ℝᶜ} →
  {μ : NatModulus} →
  ConvergesWithModulus u x μ →
  ConvergesWithModulus (negSequence u) (-ᶜ x) μ
negConvergesWithModulus u→x ε n μ≤n =
  neg-close (u→x ε n μ≤n)


negConvergesTo :
  {u : Sequence} →
  {x : ℝᶜ} →
  ConvergesTo u x →
  ConvergesTo (negSequence u) (-ᶜ x)
negConvergesTo (μ , u→x) =
  μ , negConvergesWithModulus u→x


subConvergesTo :
  {u v : Sequence} →
  {x y : ℝᶜ} →
  ConvergesTo u x →
  ConvergesTo v y →
  ConvergesTo (subSequence u v) (x +ᶜ (-ᶜ y))
subConvergesTo u→x v→y =
  addConvergesTo u→x (negConvergesTo v→y)


scalarMulConvergesTo :
  (q : ℚ) →
  {u : Sequence} →
  {x : ℝᶜ} →
  ConvergesTo u x →
  ConvergesTo (scalarMulSequence q u) (scalarMulᶜ q x)
scalarMulConvergesTo q (μ , u→x) =
  mapUniformlyContinuousConverges
    {μu = μ}
    (scalarMulᶜ-continuous q)
    u→x


mulLeftConvergesToWithBound :
  (κ : ℚ⁺) →
  (y : ℝᶜ) →
  BoundedByᶜ κ y →
  {u : Sequence} →
  {x : ℝᶜ} →
  ConvergesTo u x →
  ConvergesTo (mulLeftSequence u y) (x ·ᶜ y)
mulLeftConvergesToWithBound κ y y-bound (μ , u→x) =
  mapUniformlyContinuousConverges
    {μu = μ}
    (mulᶜ-continuous-left-with-bound κ y y-bound)
    u→x


mulRightConvergesToWithBound :
  (κ : ℚ⁺) →
  (x : ℝᶜ) →
  BoundedByᶜ κ x →
  {v : Sequence} →
  {y : ℝᶜ} →
  ConvergesTo v y →
  ConvergesTo (mulRightSequence x v) (x ·ᶜ y)
mulRightConvergesToWithBound κ x x-bound (ν , v→y) =
  mapUniformlyContinuousConverges
    {μu = ν}
    (mulᶜ-continuous-right-with-bound κ x x-bound)
    v→y


mulConvergesWithModulusAndBounds :
  (κ ι : ℚ⁺) →
  {u v : Sequence} →
  {x y : ℝᶜ} →
  {μ ν β : NatModulus} →
  BoundedByᶜ ι x →
  EventuallyBoundedByWith β κ v →
  ConvergesWithModulus u x μ →
  ConvergesWithModulus v y ν →
  ConvergesWithModulus
    (mulSequence u v)
    (x ·ᶜ y)
    (maxModulus
      (maxModulus
        (scaledHalfModulus κ μ)
        (scaledHalfModulus ι ν))
      β)
mulConvergesWithModulusAndBounds
  κ ι {u = u} {v = v} {x = x} {y = y} {μ = μ} {ν = ν} {β = β}
  x-bound v-bound u→x v→y ε n max≤n =
  subst
    (λ ρ → u n ·ᶜ v n ∼[ ρ ] x ·ᶜ y)
    (half⁺+half⁺≡ ε)
    (MetricSpace.close-triangle CauchyRealsMetricSpace term-left term-right)
  where
  α : ℚ⁺
  α =
    half⁺ ε

  δu : ℚ⁺
  δu =
    half⁺ (posInv⁺ κ *⁺ α)

  δv : ℚ⁺
  δv =
    half⁺ (posInv⁺ ι *⁺ α)

  μδu≤n : NatOrder._≤_ (μ δu) n
  μδu≤n =
    NatOrder.≤-trans
      (NatOrder.≤-trans
        (maxModulus-left≤ (scaledHalfModulus κ μ) (scaledHalfModulus ι ν) ε)
        (maxModulus-left≤
          (maxModulus (scaledHalfModulus κ μ) (scaledHalfModulus ι ν))
          β
          ε))
      max≤n

  νδv≤n : NatOrder._≤_ (ν δv) n
  νδv≤n =
    NatOrder.≤-trans
      (NatOrder.≤-trans
        (maxModulus-right≤ (scaledHalfModulus κ μ) (scaledHalfModulus ι ν) ε)
        (maxModulus-left≤
          (maxModulus (scaledHalfModulus κ μ) (scaledHalfModulus ι ν))
          β
          ε))
      max≤n

  β≤n : NatOrder._≤_ (β ε) n
  β≤n =
    NatOrder.≤-trans
      (maxModulus-right≤
        (maxModulus (scaledHalfModulus κ μ) (scaledHalfModulus ι ν))
        β
        ε)
      max≤n

  vn-bound : BoundedByᶜ κ (v n)
  vn-bound =
    v-bound ε n β≤n

  raw-left :
    (v n ·ᶜ u n) ∼[ κ *⁺ δu ] (v n ·ᶜ x)
  raw-left =
    subst2
      (λ a b → a ∼[ κ *⁺ δu ] b)
      (sym (mulᶜ-bound κ (v n) vn-bound (u n)))
      (sym (mulᶜ-bound κ (v n) vn-bound x))
      (boundedMulᶜ-close κ (v n) vn-bound (u→x δu n μδu≤n))

  left-small :
    (v n ·ᶜ u n) ∼[ α ] (v n ·ᶜ x)
  left-small =
    close-mono (scaledHalf< κ α) raw-left

  term-left :
    (u n ·ᶜ v n) ∼[ α ] (x ·ᶜ v n)
  term-left =
    subst2
      (λ a b → a ∼[ α ] b)
      (mulᶜ-comm (v n) (u n))
      (mulᶜ-comm (v n) x)
      left-small

  raw-right :
    (x ·ᶜ v n) ∼[ ι *⁺ δv ] (x ·ᶜ y)
  raw-right =
    subst2
      (λ a b → a ∼[ ι *⁺ δv ] b)
      (sym (mulᶜ-bound ι x x-bound (v n)))
      (sym (mulᶜ-bound ι x x-bound y))
      (boundedMulᶜ-close ι x x-bound (v→y δv n νδv≤n))

  term-right :
    (x ·ᶜ v n) ∼[ α ] (x ·ᶜ y)
  term-right =
    close-mono (scaledHalf< ι α) raw-right


mulConvergesToWithBounds :
  (κ ι : ℚ⁺) →
  {u v : Sequence} →
  {x y : ℝᶜ} →
  {β : NatModulus} →
  BoundedByᶜ ι x →
  EventuallyBoundedByWith β κ v →
  ConvergesTo u x →
  ConvergesTo v y →
  ConvergesTo (mulSequence u v) (x ·ᶜ y)
mulConvergesToWithBounds κ ι {β = β} x-bound v-bound (μ , u→x) (ν , v→y) =
  maxModulus
    (maxModulus
      (scaledHalfModulus κ μ)
      (scaledHalfModulus ι ν))
    β ,
  mulConvergesWithModulusAndBounds
    κ
    ι
    x-bound
    v-bound
    u→x
    v→y


boundedAwayReciprocalConvergesTo :
  (ε : ℚ⁺) →
  {u : Sequence} →
  {x : ℝᶜ} →
  (u-away : (n : ℕ) → BoundedAwayPositiveᶜ ε (u n)) →
  (x-away : BoundedAwayPositiveᶜ ε x) →
  ConvergesTo u x →
  ConvergesTo
    (positiveReciprocalSequence ε u u-away)
    (boundedAwayReciprocalᶜ ε x x-away)
boundedAwayReciprocalConvergesTo ε {u = u} {x = x} u-away x-away (μ , u→x) =
  mapUniformlyContinuousConverges
    {f = boundedReciprocalᶜ (half⁺ ε)}
    {u = u}
    {x = x}
    {μu = μ}
    (boundedReciprocalᶜ-continuous (half⁺ ε))
    u→x


boundedAwayNegativeReciprocalConvergesTo :
  (ε : ℚ⁺) →
  {u : Sequence} →
  {x : ℝᶜ} →
  (u-away : (n : ℕ) → BoundedAwayNegativeᶜ ε (u n)) →
  (x-away : BoundedAwayNegativeᶜ ε x) →
  ConvergesTo u x →
  ConvergesTo
    (negativeReciprocalSequence ε u u-away)
    (-ᶜ boundedAwayReciprocalᶜ ε (-ᶜ x) x-away)
boundedAwayNegativeReciprocalConvergesTo ε {u = u} {x = x} u-away x-away u→x =
  negConvergesTo
    (boundedAwayReciprocalConvergesTo
      ε
      {u = negSequence u}
      {x = -ᶜ x}
      u-away
      x-away
      (negConvergesTo u→x))
