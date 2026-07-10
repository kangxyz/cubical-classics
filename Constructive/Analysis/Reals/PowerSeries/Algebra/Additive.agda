{-

Part of Constructive.Analysis.Reals.PowerSeries.Algebra

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Algebra.Additive where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; max ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.HITs.PropositionalTruncation as Prop

open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Metric
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using (bounded-byᶜ-mul)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.Series
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower)
open import Constructive.Analysis.Modulus
  using
    ( AntitoneNatModulus
    ; maxModulus
    ; maxModulus-antitone
    ; maxModulus-left≤
    ; maxModulus-right≤
    ; splitModulus
    ; half-mono-≤
    )
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open import Constructive.Analysis.Reals.PowerSeries.Algebra.Internal
open import Constructive.Analysis.Reals.PowerSeries.Algebra.Core
open import Constructive.Analysis.Reals.PowerSeries.Algebra.ZeroConstant
open import Constructive.Analysis.Reals.PowerSeries.Algebra.Pointwise
open import Constructive.Analysis.Reals.PowerSeries.Algebra.Sums

addPowerSeriesOnBallWith :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesOnBallWith a ρ μ →
  HasPowerSeriesOnBallWith b ρ μ →
  HasPowerSeriesOnBallWith (addPowerSeries a b) ρ (splitModulus μ)
addPowerSeriesOnBallWith {a = a} {b = b} {μ = μ} left right =
  hasPowerSeriesOnBallWith
    (splitTailModulus-antitone
      (HasPowerSeriesOnBallWith.antitoneModulus left))
    (λ h h-bound →
      subst
        (λ u → TailBound u (splitModulus μ))
        (sym (funExt (addPowerSeriesTerm a b h)))
        (tailBound-add
          (HasPowerSeriesOnBallWith.tailBound left h h-bound)
          (HasPowerSeriesOnBallWith.tailBound right h h-bound)))


addPowerSeriesOnBallWithMax :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν : ℚ⁺ → ℕ} →
  HasPowerSeriesOnBallWith a ρ μ →
  HasPowerSeriesOnBallWith b ρ ν →
  HasPowerSeriesOnBallWith
    (addPowerSeries a b)
    ρ
    (splitModulus (maxModulus μ ν))
addPowerSeriesOnBallWithMax
  {a = a}
  {b = b}
  {μ = μ}
  {ν = ν}
  left
  right =
  addPowerSeriesOnBallWith leftMax rightMax
  where
  maxAntitone : AntitoneNatModulus (maxModulus μ ν)
  maxAntitone =
    maxTailModulus-antitone
      (HasPowerSeriesOnBallWith.antitoneModulus left)
      (HasPowerSeriesOnBallWith.antitoneModulus right)

  leftMax : HasPowerSeriesOnBallWith a _ (maxModulus μ ν)
  leftMax =
    hasPowerSeriesOnBallWith
      maxAntitone
      (λ h h-bound →
        tailBound-max-left
          (HasPowerSeriesOnBallWith.tailBound left h h-bound))

  rightMax : HasPowerSeriesOnBallWith b _ (maxModulus μ ν)
  rightMax =
    hasPowerSeriesOnBallWith
      maxAntitone
      (λ h h-bound →
        tailBound-max-right
          (HasPowerSeriesOnBallWith.tailBound right h h-bound))


addPowerSeriesOnBall :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBall a ρ →
  HasPowerSeriesOnBall b ρ →
  HasPowerSeriesOnBall (addPowerSeries a b) ρ
addPowerSeriesOnBall (μ , left) (ν , right) =
  splitModulus (maxModulus μ ν) ,
  addPowerSeriesOnBallWithMax left right


powerSeriesSumOnBall-addWithMax :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν : ℚ⁺ → ℕ} →
  (left : HasPowerSeriesOnBallWith a ρ μ) →
  (right : HasPowerSeriesOnBallWith b ρ ν) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    (addPowerSeries a b)
    ρ
    (splitModulus (maxModulus μ ν))
    (addPowerSeriesOnBallWithMax left right)
    h
    h-bound
  ≡
  powerSeriesSumOnBall a ρ μ left h h-bound +ᶜ
  powerSeriesSumOnBall b ρ ν right h h-bound
powerSeriesSumOnBall-addWithMax
  {a = a}
  {b = b}
  {ρ = ρ}
  {μ = μ}
  {ν = ν}
  left
  right
  h
  h-bound =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    addSum
    splitSum
    (λ ε →
      subst
        (λ κ → MetricSpace.Close CauchyRealsMetricSpace addSum κ splitSum)
        (half⁺+half⁺≡ ε)
        (MetricSpace.close-triangle
          CauchyRealsMetricSpace
          (addTail ε)
          (MetricSpace.close-sym CauchyRealsMetricSpace (splitTail ε))))
  where
  addConvergence :
    HasPowerSeriesOnBallWith
      (addPowerSeries a b)
      ρ
      (splitModulus (maxModulus μ ν))
  addConvergence =
    addPowerSeriesOnBallWithMax left right

  addSum : ℝᶜ
  addSum =
    powerSeriesSumOnBall
      (addPowerSeries a b)
      ρ
      (splitModulus (maxModulus μ ν))
      addConvergence
      h
      h-bound

  splitSum : ℝᶜ
  splitSum =
    powerSeriesSumOnBall a ρ μ left h h-bound +ᶜ
    powerSeriesSumOnBall b ρ ν right h h-bound

  addIndex :
    ℚ⁺ →
    ℕ
  addIndex ε =
    splitModulus
      (maxModulus μ ν)
      (quarter⁺ (half⁺ (half⁺ ε)))

  leftIndex :
    ℚ⁺ →
    ℕ
  leftIndex ε =
    μ (quarter⁺ (half⁺ (quarter⁺ ε)))

  rightIndex :
    ℚ⁺ →
    ℕ
  rightIndex ε =
    ν (quarter⁺ (half⁺ (quarter⁺ ε)))

  approximationIndex :
    ℚ⁺ →
    ℕ
  approximationIndex ε =
    max (addIndex ε) (max (leftIndex ε) (rightIndex ε))

  addIndex≤approximation :
    (ε : ℚ⁺) →
    NatOrder._≤_ (addIndex ε) (approximationIndex ε)
  addIndex≤approximation ε =
    NatOrder.left-≤-max
      {m = addIndex ε}
      {n = max (leftIndex ε) (rightIndex ε)}

  leftIndex≤approximation :
    (ε : ℚ⁺) →
    NatOrder._≤_ (leftIndex ε) (approximationIndex ε)
  leftIndex≤approximation ε =
    NatOrder.≤-trans
      (NatOrder.left-≤-max
        {m = leftIndex ε}
        {n = rightIndex ε})
      (NatOrder.right-≤-max
        {n = max (leftIndex ε) (rightIndex ε)}
        {m = addIndex ε})

  rightIndex≤approximation :
    (ε : ℚ⁺) →
    NatOrder._≤_ (rightIndex ε) (approximationIndex ε)
  rightIndex≤approximation ε =
    NatOrder.≤-trans
      (NatOrder.right-≤-max
        {n = rightIndex ε}
        {m = leftIndex ε})
      (NatOrder.right-≤-max
        {n = max (leftIndex ε) (rightIndex ε)}
        {m = addIndex ε})

  addPartialSum :
    ℚ⁺ →
    ℝᶜ
  addPartialSum ε =
    powerSeriesPartialSum a h (approximationIndex ε) +ᶜ
    powerSeriesPartialSum b h (approximationIndex ε)

  addTail :
    (ε : ℚ⁺) →
    MetricSpace.Close CauchyRealsMetricSpace
      addSum
      (half⁺ ε)
      (addPartialSum ε)
  addTail ε =
    subst
      (λ partial →
        MetricSpace.Close CauchyRealsMetricSpace
          addSum
          (half⁺ ε)
          partial)
      (powerSeriesPartialSum-add a b h (approximationIndex ε))
      (seriesSumFromFiniteTailBoundConvergesAt
        (powerSeriesTerm (addPowerSeries a b) h)
        (splitModulus (maxModulus μ ν))
        (HasPowerSeriesOnBallWith.tailBound addConvergence h h-bound)
        (HasPowerSeriesOnBallWith.antitoneModulus addConvergence)
        (half⁺ ε)
        (approximationIndex ε)
        (addIndex≤approximation ε))

  splitTail :
    (ε : ℚ⁺) →
    MetricSpace.Close CauchyRealsMetricSpace
      splitSum
      (half⁺ ε)
      (addPartialSum ε)
  splitTail ε =
    subst
      (λ κ →
        MetricSpace.Close CauchyRealsMetricSpace
          splitSum
          κ
          (addPartialSum ε))
      (ℚ⁺Path (quarter-sum≡half ε))
      (add-close leftTail rightTail)
    where
    leftTail :
      powerSeriesSumOnBall a ρ μ left h h-bound
      ∼[ quarter⁺ ε ]
      powerSeriesPartialSum a h (approximationIndex ε)
    leftTail =
      seriesSumFromFiniteTailBoundConvergesAt
        (powerSeriesTerm a h)
        μ
        (HasPowerSeriesOnBallWith.tailBound left h h-bound)
        (HasPowerSeriesOnBallWith.antitoneModulus left)
        (quarter⁺ ε)
        (approximationIndex ε)
        (leftIndex≤approximation ε)

    rightTail :
      powerSeriesSumOnBall b ρ ν right h h-bound
      ∼[ quarter⁺ ε ]
      powerSeriesPartialSum b h (approximationIndex ε)
    rightTail =
      seriesSumFromFiniteTailBoundConvergesAt
        (powerSeriesTerm b h)
        ν
        (HasPowerSeriesOnBallWith.tailBound right h h-bound)
        (HasPowerSeriesOnBallWith.antitoneModulus right)
        (quarter⁺ ε)
        (approximationIndex ε)
        (rightIndex≤approximation ε)


powerSeriesSumOnBallFrom-add :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  (left : HasPowerSeriesOnBall a ρ) →
  (right : HasPowerSeriesOnBall b ρ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBallFrom
    (addPowerSeries a b)
    ρ
    (addPowerSeriesOnBall left right)
    h
    h-bound
  ≡
  powerSeriesSumOnBallFrom a ρ left h h-bound +ᶜ
  powerSeriesSumOnBallFrom b ρ right h h-bound
powerSeriesSumOnBallFrom-add (μ , left) (ν , right) h h-bound =
  powerSeriesSumOnBall-addWithMax left right h h-bound


subPowerSeriesOnBallWith :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesOnBallWith a ρ μ →
  HasPowerSeriesOnBallWith b ρ μ →
  HasPowerSeriesOnBallWith (subPowerSeries a b) ρ (splitModulus μ)
subPowerSeriesOnBallWith left right =
  addPowerSeriesOnBallWith left (negPowerSeriesOnBallWith right)


subPowerSeriesOnBallWithMax :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν : ℚ⁺ → ℕ} →
  HasPowerSeriesOnBallWith a ρ μ →
  HasPowerSeriesOnBallWith b ρ ν →
  HasPowerSeriesOnBallWith
    (subPowerSeries a b)
    ρ
    (splitModulus (maxModulus μ ν))
subPowerSeriesOnBallWithMax left right =
  addPowerSeriesOnBallWithMax left (negPowerSeriesOnBallWith right)


subPowerSeriesOnBall :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBall a ρ →
  HasPowerSeriesOnBall b ρ →
  HasPowerSeriesOnBall (subPowerSeries a b) ρ
subPowerSeriesOnBall (μ , left) (ν , right) =
  splitModulus (maxModulus μ ν) ,
  subPowerSeriesOnBallWithMax left right
