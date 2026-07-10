{-

Part of Constructive.Analysis.Reals.PowerSeries.Algebra

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Algebra.ZeroConstant where

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
    ( maxModulus
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

zeroPowerSeriesTerm :
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesTerm zeroPowerSeries h n ≡ 0ᶜ
zeroPowerSeriesTerm h n =
  mulᶜ-zero-left (realPower h n)


tailSum-zeroPowerSeriesTerm :
  (h : ℝᶜ) →
  (m k : ℕ) →
  tailSum (powerSeriesTerm zeroPowerSeries h) m k ≡ 0ᶜ
tailSum-zeroPowerSeriesTerm h m k =
  cong
    (λ u → tailSum u m k)
    (funExt (zeroPowerSeriesTerm h)) ∙
  tailSum-zero-sequence m k


zeroPowerSeriesTailBound :
  (h : ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  PowerSeriesTailBound zeroPowerSeries h μ
zeroPowerSeriesTailBound h μ ε m k _ =
  subst
    (BoundedByᶜ ε)
    (sym (tailSum-zeroPowerSeriesTerm h m k))
    (bounded-byᶜ-zero ε)


zeroPowerSeriesOnBallWith :
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBallWith zeroPowerSeries ρ (λ _ → zero)
zeroPowerSeriesOnBallWith =
  hasPowerSeriesOnBallWith
    (λ _ → NatOrder.≤-refl)
    (λ h _ → zeroPowerSeriesTailBound h (λ _ → zero))


zeroPowerSeriesOnBall :
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBall zeroPowerSeries ρ
zeroPowerSeriesOnBall =
  (λ _ → zero) , zeroPowerSeriesOnBallWith


zeroPowerSeriesRadius :
  {R : ℚ⁺} →
  HasPowerSeriesRadius zeroPowerSeries R
zeroPowerSeriesRadius =
  hasPowerSeriesRadius
    (λ _ _ →
      zeroPowerSeriesOnBall)


zeroPowerSeriesInfiniteRadius :
  HasInfinitePowerSeriesRadius zeroPowerSeries
zeroPowerSeriesInfiniteRadius _ =
  zeroPowerSeriesOnBall


constantPowerSeriesTerm-zero :
  (c h : ℝᶜ) →
  powerSeriesTerm (constantPowerSeries c) h zero ≡ c
constantPowerSeriesTerm-zero c h =
  mulᶜ-one-right c


constantPowerSeriesTerm-suc :
  (c h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesTerm (constantPowerSeries c) h (suc n) ≡ 0ᶜ
constantPowerSeriesTerm-suc c h n =
  mulᶜ-zero-left (realPower h (suc n))


drop-positive-constantPowerSeriesTerm :
  (c h : ℝᶜ) →
  (m n : ℕ) →
  drop (suc m) (powerSeriesTerm (constantPowerSeries c) h) n ≡ 0ᶜ
drop-positive-constantPowerSeriesTerm c h m n =
  drop-index
    (suc m)
    (powerSeriesTerm (constantPowerSeries c) h)
    n ∙
  constantPowerSeriesTerm-suc c h (m Nat.+ n)


tailSum-constantPowerSeriesTerm :
  (c h : ℝᶜ) →
  (m k : ℕ) →
  NatOrder._≤_ (suc zero) m →
  tailSum (powerSeriesTerm (constantPowerSeries c) h) m k ≡ 0ᶜ
tailSum-constantPowerSeriesTerm c h zero k 1≤0 =
  Empty.rec (NatOrder.¬-<-zero 1≤0)
tailSum-constantPowerSeriesTerm c h (suc m) k _ =
  cong
    (λ u → partialSum u k)
    (funExt (drop-positive-constantPowerSeriesTerm c h m)) ∙
  partialSum-zero-sequence k


constantPowerSeriesTailBound :
  (c h : ℝᶜ) →
  PowerSeriesTailBound (constantPowerSeries c) h (λ _ → suc zero)
constantPowerSeriesTailBound c h ε m k 1≤m =
  subst
    (BoundedByᶜ ε)
    (sym (tailSum-constantPowerSeriesTerm c h m k 1≤m))
    (bounded-byᶜ-zero ε)


constantPowerSeriesOnBallWith :
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBallWith (constantPowerSeries c) ρ (λ _ → suc zero)
constantPowerSeriesOnBallWith c =
  hasPowerSeriesOnBallWith
    (λ _ → NatOrder.≤-refl)
    (λ h _ → constantPowerSeriesTailBound c h)


constantPowerSeriesOnBall :
  (c : ℝᶜ) →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBall (constantPowerSeries c) ρ
constantPowerSeriesOnBall c =
  (λ _ → suc zero) , constantPowerSeriesOnBallWith c


constantPowerSeriesRadius :
  (c : ℝᶜ) →
  {R : ℚ⁺} →
  HasPowerSeriesRadius (constantPowerSeries c) R
constantPowerSeriesRadius c =
  hasPowerSeriesRadius
    (λ _ _ →
      constantPowerSeriesOnBall c)


constantPowerSeriesInfiniteRadius :
  (c : ℝᶜ) →
  HasInfinitePowerSeriesRadius (constantPowerSeries c)
constantPowerSeriesInfiniteRadius c _ =
  constantPowerSeriesOnBall c
