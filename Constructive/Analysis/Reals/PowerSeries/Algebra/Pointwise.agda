{-

Part of Constructive.Analysis.Reals.PowerSeries.Algebra

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Algebra.Pointwise where

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

addPowerSeriesTerm :
  (a b : PowerSeries) →
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesTerm (addPowerSeries a b) h n ≡
  powerSeriesTerm a h n +ᶜ powerSeriesTerm b h n
addPowerSeriesTerm a b h n =
  mulᶜ-distrib-left (a n) (b n) (realPower h n)


negPowerSeriesTerm :
  (a : PowerSeries) →
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesTerm (negPowerSeries a) h n ≡
  -ᶜ powerSeriesTerm a h n
negPowerSeriesTerm a h n =
  mulᶜ-comm (-ᶜ a n) (realPower h n) ∙
  mulᶜ-neg-right (realPower h n) (a n) ∙
  cong -ᶜ_ (mulᶜ-comm (realPower h n) (a n))


powerSeriesPartialSum-neg :
  (a : PowerSeries) →
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesPartialSum (negPowerSeries a) h n ≡
  -ᶜ powerSeriesPartialSum a h n
powerSeriesPartialSum-neg a h n =
  cong
    (λ u → partialSum u n)
    (funExt (negPowerSeriesTerm a h)) ∙
  partialSum-neg (powerSeriesTerm a h) n


powerSeriesPartialSum-add :
  (a b : PowerSeries) →
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesPartialSum (addPowerSeries a b) h n ≡
  powerSeriesPartialSum a h n +ᶜ powerSeriesPartialSum b h n
powerSeriesPartialSum-add a b h n =
  cong
    (λ u → partialSum u n)
    (funExt (addPowerSeriesTerm a b h)) ∙
  partialSum-add
    (powerSeriesTerm a h)
    (powerSeriesTerm b h)
    n


rationalScalePowerSeriesTerm :
  (q : ℚ) →
  (a : PowerSeries) →
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesTerm (rationalScalePowerSeries q a) h n ≡
  rational q ·ᶜ powerSeriesTerm a h n
rationalScalePowerSeriesTerm q a h n =
  sym (mulᶜ-assoc-rational-left q (a n) (realPower h n))


realScalePowerSeriesTerm :
  (x : ℝᶜ) →
  (a : PowerSeries) →
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesTerm (realScalePowerSeries x a) h n ≡
  x ·ᶜ powerSeriesTerm a h n
realScalePowerSeriesTerm x a h n =
  sym (mulᶜ-assoc x (a n) (realPower h n))


drop-rationalMulLeft :
  (q : ℚ) →
  (u : ℕ → ℝᶜ) →
  (m : ℕ) →
  drop m (λ n → rational q ·ᶜ u n) ≡
  (λ n → rational q ·ᶜ drop m u n)
drop-rationalMulLeft q u zero =
  refl
drop-rationalMulLeft q u (suc m) =
  drop-rationalMulLeft q (λ n → u (suc n)) m


drop-mulLeft :
  (x : ℝᶜ) →
  (u : ℕ → ℝᶜ) →
  (m : ℕ) →
  drop m (λ n → x ·ᶜ u n) ≡
  (λ n → x ·ᶜ drop m u n)
drop-mulLeft x u zero =
  refl
drop-mulLeft x u (suc m) =
  drop-mulLeft x (λ n → u (suc n)) m


partialSum-rationalMulLeft :
  (q : ℚ) →
  (u : ℕ → ℝᶜ) →
  (n : ℕ) →
  partialSum (λ k → rational q ·ᶜ u k) n ≡
  rational q ·ᶜ partialSum u n
partialSum-rationalMulLeft q u zero =
  sym (mulᶜ-zero-right (rational q))
partialSum-rationalMulLeft q u (suc n) =
  cong
    ((rational q ·ᶜ u zero) +ᶜ_)
    (partialSum-rationalMulLeft q (λ k → u (suc k)) n) ∙
  sym
    (mulᶜ-distrib-right
      (rational q)
      (u zero)
      (partialSum (λ k → u (suc k)) n))


partialSum-mulLeft :
  (x : ℝᶜ) →
  (u : ℕ → ℝᶜ) →
  (n : ℕ) →
  partialSum (λ k → x ·ᶜ u k) n ≡
  x ·ᶜ partialSum u n
partialSum-mulLeft x u zero =
  sym (mulᶜ-zero-right x)
partialSum-mulLeft x u (suc n) =
  cong
    ((x ·ᶜ u zero) +ᶜ_)
    (partialSum-mulLeft x (λ k → u (suc k)) n) ∙
  sym
    (mulᶜ-distrib-right
      x
      (u zero)
      (partialSum (λ k → u (suc k)) n))


powerSeriesPartialSum-rationalScale :
  (q : ℚ) →
  (a : PowerSeries) →
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesPartialSum (rationalScalePowerSeries q a) h n ≡
  rational q ·ᶜ powerSeriesPartialSum a h n
powerSeriesPartialSum-rationalScale q a h n =
  cong
    (λ u → partialSum u n)
    (funExt (rationalScalePowerSeriesTerm q a h)) ∙
  partialSum-rationalMulLeft
    q
    (powerSeriesTerm a h)
    n


powerSeriesPartialSum-realScale :
  (x : ℝᶜ) →
  (a : PowerSeries) →
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesPartialSum (realScalePowerSeries x a) h n ≡
  x ·ᶜ powerSeriesPartialSum a h n
powerSeriesPartialSum-realScale x a h n =
  cong
    (λ u → partialSum u n)
    (funExt (realScalePowerSeriesTerm x a h)) ∙
  partialSum-mulLeft
    x
    (powerSeriesTerm a h)
    n


tailSum-mulLeft :
  (x : ℝᶜ) →
  (u : ℕ → ℝᶜ) →
  (m k : ℕ) →
  tailSum (λ n → x ·ᶜ u n) m k ≡
  x ·ᶜ tailSum u m k
tailSum-mulLeft x u m k =
  cong
    (λ v → partialSum v k)
    (drop-mulLeft x u m) ∙
  partialSum-mulLeft x (drop m u) k


tailSum-rationalMulLeft :
  (q : ℚ) →
  (u : ℕ → ℝᶜ) →
  (m k : ℕ) →
  tailSum (λ n → rational q ·ᶜ u n) m k ≡
  rational q ·ᶜ tailSum u m k
tailSum-rationalMulLeft q u m k =
  cong
    (λ v → partialSum v k)
    (drop-rationalMulLeft q u m) ∙
  partialSum-rationalMulLeft q (drop m u) k


rationalScalePrecision :
  ℚ →
  ℚ⁺ →
  ℚ⁺
rationalScalePrecision q ε =
  ε *⁺ posInv⁺ (scalar-bound q)


rationalScalePrecision-mono :
  (q : ℚ) →
  {ε δ : ℚ⁺} →
  radius ε ℚOrder.≤ radius δ →
  radius (rationalScalePrecision q ε) ℚOrder.≤
  radius (rationalScalePrecision q δ)
rationalScalePrecision-mono q {ε = ε} {δ = δ} ε≤δ =
  ℚOrder.≤-·o
    (radius ε)
    (radius δ)
    (radius (posInv⁺ κ))
    invκ≥0
    ε≤δ
  where
  κ : ℚ⁺
  κ =
    scalar-bound q

  invκ≥0 : Rational.0ℚ ℚOrder.≤ radius (posInv⁺ κ)
  invκ≥0 =
    Rational.<→≤
      {p = Rational.0ℚ}
      {q = radius (posInv⁺ κ)}
      (posInv⁺ κ .snd)


rationalScalePrecision-cancel :
  (q : ℚ) →
  (ε : ℚ⁺) →
  scalar-bound q *⁺ rationalScalePrecision q ε ≡ ε
rationalScalePrecision-cancel q ε =
  cong (κ *⁺_) (*⁺-comm ε invκ) ∙
  sym (*⁺-assoc κ invκ ε) ∙
  cong (_*⁺ ε) (*⁺-posInv-right κ) ∙
  *⁺-identity-left ε
  where
  κ : ℚ⁺
  κ =
    scalar-bound q

  invκ : ℚ⁺
  invκ =
    posInv⁺ κ


rationalScaleModulus :
  ℚ →
  (ℚ⁺ → ℕ) →
  ℚ⁺ →
  ℕ
rationalScaleModulus q μ ε =
  μ (rationalScalePrecision q ε)


rationalScaleModulus-antitone :
  (q : ℚ) →
  {μ : ℚ⁺ → ℕ} →
  AntitoneNatModulus μ →
  AntitoneNatModulus (rationalScaleModulus q μ)
rationalScaleModulus-antitone q μ-ant {ε = ε} {δ = δ} ε≤δ =
  μ-ant
    {ε = rationalScalePrecision q ε}
    {δ = rationalScalePrecision q δ}
    (rationalScalePrecision-mono q {ε = ε} {δ = δ} ε≤δ)


rationalScaleTailBound :
  (q : ℚ) →
  {u : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  TailBound u μ →
  TailBound
    (λ n → rational q ·ᶜ u n)
    (rationalScaleModulus q μ)
rationalScaleTailBound q {u = u} {μ = μ} tailBound ε m k μ≤m =
  subst2
    BoundedByᶜ
    (rationalScalePrecision-cancel q ε)
    (sym scaledTailPath)
    scaledTailBound
  where
  κ : ℚ⁺
  κ =
    scalar-bound q

  δ : ℚ⁺
  δ =
    rationalScalePrecision q ε

  tail : ℝᶜ
  tail =
    tailSum u m k

  tailBoundδ : BoundedByᶜ δ tail
  tailBoundδ =
    tailBound δ m k μ≤m

  scaledTailPath :
    tailSum (λ n → rational q ·ᶜ u n) m k ≡
    rational q ·ᶜ tail
  scaledTailPath =
    tailSum-rationalMulLeft q u m k

  scaledTailBound :
    BoundedByᶜ (κ *⁺ δ) (rational q ·ᶜ tail)
  scaledTailBound =
    subst
      (BoundedByᶜ (κ *⁺ δ))
      (sym (mulᶜ-rational-left q tail))
      (bounded-byᶜ-scale-rational-bound
        q
        δ
        κ
        tail
        (scalar-bound-rational-boundᶜ q)
        tailBoundδ)


realScalePrecision :
  ℚ⁺ →
  ℚ⁺ →
  ℚ⁺
realScalePrecision κ ε =
  ε *⁺ posInv⁺ κ


realScalePrecision-mono :
  (κ : ℚ⁺) →
  {ε δ : ℚ⁺} →
  radius ε ℚOrder.≤ radius δ →
  radius (realScalePrecision κ ε) ℚOrder.≤
  radius (realScalePrecision κ δ)
realScalePrecision-mono κ {ε = ε} {δ = δ} ε≤δ =
  ℚOrder.≤-·o
    (radius ε)
    (radius δ)
    (radius (posInv⁺ κ))
    invκ≥0
    ε≤δ
  where
  invκ≥0 : Rational.0ℚ ℚOrder.≤ radius (posInv⁺ κ)
  invκ≥0 =
    Rational.<→≤
      {p = Rational.0ℚ}
      {q = radius (posInv⁺ κ)}
      (posInv⁺ κ .snd)


realScalePrecision-cancel :
  (κ : ℚ⁺) →
  (ε : ℚ⁺) →
  κ *⁺ realScalePrecision κ ε ≡ ε
realScalePrecision-cancel κ ε =
  cong (κ *⁺_) (*⁺-comm ε invκ) ∙
  sym (*⁺-assoc κ invκ ε) ∙
  cong (_*⁺ ε) (*⁺-posInv-right κ) ∙
  *⁺-identity-left ε
  where
  invκ : ℚ⁺
  invκ =
    posInv⁺ κ


realScaleModulus :
  ℚ⁺ →
  (ℚ⁺ → ℕ) →
  ℚ⁺ →
  ℕ
realScaleModulus κ μ ε =
  μ (realScalePrecision κ ε)


realScaleModulus-antitone :
  (κ : ℚ⁺) →
  {μ : ℚ⁺ → ℕ} →
  AntitoneNatModulus μ →
  AntitoneNatModulus (realScaleModulus κ μ)
realScaleModulus-antitone κ μ-ant {ε = ε} {δ = δ} ε≤δ =
  μ-ant
    {ε = realScalePrecision κ ε}
    {δ = realScalePrecision κ δ}
    (realScalePrecision-mono κ {ε = ε} {δ = δ} ε≤δ)


realScaleTailBound :
  (x : ℝᶜ) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ x →
  {u : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  TailBound u μ →
  TailBound
    (λ n → x ·ᶜ u n)
    (realScaleModulus κ μ)
realScaleTailBound x κ x-bound {u = u} {μ = μ} tailBound ε m k μ≤m =
  subst2
    BoundedByᶜ
    (realScalePrecision-cancel κ ε)
    (sym scaledTailPath)
    scaledTailBound
  where
  δ : ℚ⁺
  δ =
    realScalePrecision κ ε

  tail : ℝᶜ
  tail =
    tailSum u m k

  tailBoundδ : BoundedByᶜ δ tail
  tailBoundδ =
    tailBound δ m k μ≤m

  scaledTailPath :
    tailSum (λ n → x ·ᶜ u n) m k ≡
    x ·ᶜ tail
  scaledTailPath =
    tailSum-mulLeft x u m k

  scaledTailBound :
    BoundedByᶜ (κ *⁺ δ) (x ·ᶜ tail)
  scaledTailBound =
    bounded-byᶜ-mul
      κ
      δ
      x
      tail
      x-bound
      tailBoundδ


shiftPowerSeriesTerm :
  (a : PowerSeries) →
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesTerm (shiftPowerSeries a) h n ≡
  a (suc n) ·ᶜ realPower h n
shiftPowerSeriesTerm a h n =
  refl


powerSeriesTerm-suc-shift :
  (a : PowerSeries) →
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesTerm a h (suc n) ≡
  h ·ᶜ powerSeriesTerm (shiftPowerSeries a) h n
powerSeriesTerm-suc-shift a h n =
  mulᶜ-assoc (a (suc n)) h (realPower h n) ∙
  cong (_·ᶜ realPower h n) (mulᶜ-comm (a (suc n)) h) ∙
  sym (mulᶜ-assoc h (a (suc n)) (realPower h n))


powerSeriesPartialSum-shift :
  (a : PowerSeries) →
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesPartialSum a h (suc n) ≡
  a zero +ᶜ h ·ᶜ powerSeriesPartialSum (shiftPowerSeries a) h n
powerSeriesPartialSum-shift a h n =
  partialSum-suc (powerSeriesTerm a h) n ∙
  cong₂
    _+ᶜ_
    (mulᶜ-one-right (a zero))
    (cong
      (λ u → partialSum u n)
      (funExt (powerSeriesTerm-suc-shift a h)) ∙
    partialSum-mulLeft
      h
      (powerSeriesTerm (shiftPowerSeries a) h)
      n)


realPower-zero-suc :
  (n : ℕ) →
  realPower 0ᶜ (suc n) ≡ 0ᶜ
realPower-zero-suc n =
  mulᶜ-zero-left (realPower 0ᶜ n)


powerSeriesTerm-at-zero-suc :
  (a : PowerSeries) →
  (n : ℕ) →
  powerSeriesTerm a 0ᶜ (suc n) ≡ 0ᶜ
powerSeriesTerm-at-zero-suc a n =
  cong
    (a (suc n) ·ᶜ_)
    (realPower-zero-suc n) ∙
  mulᶜ-zero-right (a (suc n))


powerSeriesPartialSum-at-zero-suc :
  (a : PowerSeries) →
  (n : ℕ) →
  powerSeriesPartialSum a 0ᶜ (suc n) ≡ a zero
powerSeriesPartialSum-at-zero-suc a n =
  partialSum-suc (powerSeriesTerm a 0ᶜ) n ∙
  cong₂
    _+ᶜ_
    (mulᶜ-one-right (a zero))
    (cong
      (λ u → partialSum u n)
      (funExt (powerSeriesTerm-at-zero-suc a)) ∙
    partialSum-zero-sequence n) ∙
  add-zero-right (a zero)


powerSeriesPartialSum-at-zero-positive :
  (a : PowerSeries) →
  (n : ℕ) →
  NatOrder._≤_ (suc zero) n →
  powerSeriesPartialSum a 0ᶜ n ≡ a zero
powerSeriesPartialSum-at-zero-positive a n (k , k+1≡n) =
  subst
    (λ m → powerSeriesPartialSum a 0ᶜ m ≡ a zero)
    sucK≡n
    (powerSeriesPartialSum-at-zero-suc a k)
  where
  k+1≡sucK : k Nat.+ suc zero ≡ suc k
  k+1≡sucK =
    Nat.+-suc k zero ∙
    cong suc (Nat.+-zero k)

  sucK≡n : suc k ≡ n
  sucK≡n =
    sym k+1≡sucK ∙
    k+1≡n
