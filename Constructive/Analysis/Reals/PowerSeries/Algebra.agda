{-

Algebraic operations on power-series coefficients

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Algebra where

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
open import Constructive.Analysis.Metric.Instances.CauchyReals
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
open import Constructive.Analysis.Reals.Sequences.Base
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


splitTailModulus-antitone :
  {μ : ℚ⁺ → ℕ} →
  AntitoneTailModulus μ →
  AntitoneTailModulus (splitModulus μ)
splitTailModulus-antitone μ-ant {ε = ε} {δ = δ} ε≤δ =
  μ-ant
    {ε = half⁺ ε}
    {δ = half⁺ δ}
    (half-mono-≤ {ε = ε} {δ = δ} ε≤δ)


maxTailModulus-antitone :
  {μ ν : ℚ⁺ → ℕ} →
  AntitoneTailModulus μ →
  AntitoneTailModulus ν →
  AntitoneTailModulus (maxModulus μ ν)
maxTailModulus-antitone =
  maxModulus-antitone


tailBound-weakenModulus :
  {u : ℕ → ℝᶜ} →
  {μ ν : ℚ⁺ → ℕ} →
  ((ε : ℚ⁺) → NatOrder._≤_ (μ ε) (ν ε)) →
  TailBound u μ →
  TailBound u ν
tailBound-weakenModulus μ≤ν tailBound ε m k ν≤m =
  tailBound ε m k (NatOrder.≤-trans (μ≤ν ε) ν≤m)


tailBound-max-left :
  {u : ℕ → ℝᶜ} →
  {μ ν : ℚ⁺ → ℕ} →
  TailBound u μ →
  TailBound u (maxModulus μ ν)
tailBound-max-left {μ = μ} {ν = ν} =
  tailBound-weakenModulus (maxModulus-left≤ μ ν)


tailBound-max-right :
  {u : ℕ → ℝᶜ} →
  {μ ν : ℚ⁺ → ℕ} →
  TailBound u ν →
  TailBound u (maxModulus μ ν)
tailBound-max-right {μ = μ} {ν = ν} =
  tailBound-weakenModulus (maxModulus-right≤ μ ν)


bounded-byᶜ-zero :
  (ε : ℚ⁺) →
  BoundedByᶜ ε 0ᶜ
bounded-byᶜ-zero ε =
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


drop-zero-sequence :
  (m : ℕ) →
  drop m (λ _ → 0ᶜ) ≡ (λ _ → 0ᶜ)
drop-zero-sequence zero =
  refl
drop-zero-sequence (suc m) =
  drop-zero-sequence m


tailSum-zero-sequence :
  (m k : ℕ) →
  tailSum (λ _ → 0ᶜ) m k ≡ 0ᶜ
tailSum-zero-sequence m k =
  cong
    (λ u → partialSum u k)
    (drop-zero-sequence m) ∙
  partialSum-zero-sequence k


zeroPowerSeries :
  PowerSeries
zeroPowerSeries _ =
  0ᶜ


constantPowerSeries :
  ℝᶜ →
  PowerSeries
constantPowerSeries c zero =
  c
constantPowerSeries c (suc _) =
  0ᶜ


addPowerSeries :
  PowerSeries →
  PowerSeries →
  PowerSeries
addPowerSeries a b n =
  a n +ᶜ b n


negPowerSeries :
  PowerSeries →
  PowerSeries
negPowerSeries a n =
  -ᶜ a n


subPowerSeries :
  PowerSeries →
  PowerSeries →
  PowerSeries
subPowerSeries a b =
  addPowerSeries a (negPowerSeries b)


rationalScalePowerSeries :
  ℚ →
  PowerSeries →
  PowerSeries
rationalScalePowerSeries q a n =
  rational q ·ᶜ a n


realScalePowerSeries :
  ℝᶜ →
  PowerSeries →
  PowerSeries
realScalePowerSeries x a n =
  x ·ᶜ a n


shiftPowerSeries :
  PowerSeries →
  PowerSeries
shiftPowerSeries a n =
  a (suc n)


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
  record
    { antitoneModulus = λ _ → NatOrder.≤-refl
    ; tailBound = λ h _ → zeroPowerSeriesTailBound h (λ _ → zero)
    }


zeroPowerSeriesOnBall :
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBall zeroPowerSeries ρ
zeroPowerSeriesOnBall =
  (λ _ → zero) , zeroPowerSeriesOnBallWith


zeroPowerSeriesRadius :
  {R : ℚ⁺} →
  HasPowerSeriesRadius zeroPowerSeries R
zeroPowerSeriesRadius =
  record
    { onSubball =
        λ _ _ →
          zeroPowerSeriesOnBall
    }


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
  record
    { antitoneModulus = λ _ → NatOrder.≤-refl
    ; tailBound = λ h _ → constantPowerSeriesTailBound c h
    }


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
  record
    { onSubball =
        λ _ _ →
          constantPowerSeriesOnBall c
    }


constantPowerSeriesInfiniteRadius :
  (c : ℝᶜ) →
  HasInfinitePowerSeriesRadius (constantPowerSeries c)
constantPowerSeriesInfiniteRadius c _ =
  constantPowerSeriesOnBall c


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
  AntitoneTailModulus μ →
  AntitoneTailModulus (rationalScaleModulus q μ)
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
  AntitoneTailModulus μ →
  AntitoneTailModulus (realScaleModulus κ μ)
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


powerSeriesSumOnBall-zero :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  (zero-bound : BoundedByᶜ ρ 0ᶜ) →
  powerSeriesSumOnBall a ρ μ convergence 0ᶜ zero-bound ≡
  a zero
powerSeriesSumOnBall-zero
  {a = a}
  {ρ = ρ}
  {μ = μ}
  convergence
  zero-bound =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    sum
    (a zero)
    closeAt
  where
  sum : ℝᶜ
  sum =
    powerSeriesSumOnBall a ρ μ convergence 0ᶜ zero-bound

  tailIndex :
    ℚ⁺ →
    ℕ
  tailIndex ε =
    μ (quarter⁺ (half⁺ ε))

  approximationIndex :
    ℚ⁺ →
    ℕ
  approximationIndex ε =
    max (tailIndex ε) (suc zero)

  tailIndex≤approximation :
    (ε : ℚ⁺) →
    NatOrder._≤_ (tailIndex ε) (approximationIndex ε)
  tailIndex≤approximation ε =
    NatOrder.left-≤-max
      {m = tailIndex ε}
      {n = suc zero}

  one≤approximation :
    (ε : ℚ⁺) →
    NatOrder._≤_ (suc zero) (approximationIndex ε)
  one≤approximation ε =
    NatOrder.right-≤-max
      {n = suc zero}
      {m = tailIndex ε}

  closeAt :
    (ε : ℚ⁺) →
    sum ∼[ ε ] a zero
  closeAt ε =
    subst
      (λ partial → sum ∼[ ε ] partial)
      (powerSeriesPartialSum-at-zero-positive
        a
        (approximationIndex ε)
        (one≤approximation ε))
      (seriesSumFromFiniteTailBoundConvergesAt
        (powerSeriesTerm a 0ᶜ)
        μ
        (HasPowerSeriesOnBallWith.tailBound convergence 0ᶜ zero-bound)
        (HasPowerSeriesOnBallWith.antitoneModulus convergence)
        ε
        (approximationIndex ε)
        (tailIndex≤approximation ε))


centeredDisplacement-center :
  (c : ℝᶜ) →
  centeredDisplacement c c ≡ 0ᶜ
centeredDisplacement-center c =
  cong (centeredDisplacement c) (sym (add-zero-right c)) ∙
  centeredDisplacement-center-plus c 0ᶜ


centeredPowerSeriesSumOnBall-center :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  (c : ℝᶜ) →
  (c-inBall : InPowerSeriesBall c ρ c) →
  centeredPowerSeriesSumOnBall a c ρ μ convergence c c-inBall ≡
  a zero
centeredPowerSeriesSumOnBall-center
  {a = a}
  {ρ = ρ}
  {μ = μ}
  convergence
  c
  c-inBall =
  powerSeriesSumOnBall-center-path
    convergence
    (centeredDisplacement-center c)
    (InPowerSeriesBall.displacementBound c-inBall)
    (bounded-byᶜ-zero ρ) ∙
  powerSeriesSumOnBall-zero
    convergence
    (bounded-byᶜ-zero ρ)


centeredPowerSeriesSumEverywhere-center :
  {a : PowerSeries} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (c : ℝᶜ) →
  centeredPowerSeriesSumEverywhere a c radiusData c ≡
  a zero
centeredPowerSeriesSumEverywhere-center
  {a = a}
  radiusData
  c =
  centeredPowerSeriesSumEverywhere-bound-path
    a
    c
    radiusData
    1⁺
    c
    c-inBall ∙
  centeredPowerSeriesSumOnBall-center
    (radiusData 1⁺ .snd)
    c
    c-inBall
  where
  c-inBall : InPowerSeriesBall c 1⁺ c
  c-inBall =
    record
      { displacementBound =
          subst
            (BoundedByᶜ 1⁺)
            (sym (centeredDisplacement-center c))
            (bounded-byᶜ-zero 1⁺)
      }


negPowerSeriesOnBallWith :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesOnBallWith a ρ μ →
  HasPowerSeriesOnBallWith (negPowerSeries a) ρ μ
negPowerSeriesOnBallWith {a = a} {μ = μ} convergence =
  record
    { antitoneModulus =
        HasPowerSeriesOnBallWith.antitoneModulus convergence
    ; tailBound =
        λ h h-bound →
          subst
            (λ u → TailBound u μ)
            (sym (funExt (negPowerSeriesTerm a h)))
            (tailBound-neg
              (HasPowerSeriesOnBallWith.tailBound convergence h h-bound))
    }


negPowerSeriesOnBall :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBall a ρ →
  HasPowerSeriesOnBall (negPowerSeries a) ρ
negPowerSeriesOnBall (μ , convergence) =
  μ , negPowerSeriesOnBallWith convergence


powerSeriesSumOnBall-neg :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    (negPowerSeries a)
    ρ
    μ
    (negPowerSeriesOnBallWith convergence)
    h
    h-bound
  ≡
  -ᶜ powerSeriesSumOnBall a ρ μ convergence h h-bound
powerSeriesSumOnBall-neg
  {a = a}
  {ρ = ρ}
  {μ = μ}
  convergence
  h
  h-bound =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    leftSum
    rightSum
    (λ ε →
      subst
        (λ κ → MetricSpace.Close CauchyRealsMetricSpace leftSum κ rightSum)
        (half⁺+half⁺≡ ε)
        (MetricSpace.close-triangle
          CauchyRealsMetricSpace
          (leftTail ε)
          (MetricSpace.close-sym CauchyRealsMetricSpace (rightTail ε))))
  where
  negConvergence :
    HasPowerSeriesOnBallWith (negPowerSeries a) ρ μ
  negConvergence =
    negPowerSeriesOnBallWith convergence

  approximationIndex :
    ℚ⁺ →
    ℕ
  approximationIndex ε =
    μ (quarter⁺ (half⁺ (half⁺ ε)))

  leftSum : ℝᶜ
  leftSum =
    powerSeriesSumOnBall
      (negPowerSeries a)
      ρ
      μ
      negConvergence
      h
      h-bound

  rightSum : ℝᶜ
  rightSum =
    -ᶜ powerSeriesSumOnBall a ρ μ convergence h h-bound

  leftTail :
    (ε : ℚ⁺) →
    MetricSpace.Close CauchyRealsMetricSpace
      leftSum
      (half⁺ ε)
      (-ᶜ powerSeriesPartialSum a h (approximationIndex ε))
  leftTail ε =
    subst
      (λ partial →
        MetricSpace.Close CauchyRealsMetricSpace
          leftSum
          (half⁺ ε)
          partial)
      (powerSeriesPartialSum-neg a h (approximationIndex ε))
      (seriesSumFromFiniteTailBoundConvergesAt
        (powerSeriesTerm (negPowerSeries a) h)
        μ
        (HasPowerSeriesOnBallWith.tailBound
          negConvergence
          h
          h-bound)
        (HasPowerSeriesOnBallWith.antitoneModulus negConvergence)
        (half⁺ ε)
        (approximationIndex ε)
        NatOrder.≤-refl)

  rightTail :
    (ε : ℚ⁺) →
    MetricSpace.Close CauchyRealsMetricSpace
      rightSum
      (half⁺ ε)
      (-ᶜ powerSeriesPartialSum a h (approximationIndex ε))
  rightTail ε =
    neg-close
      (seriesSumFromFiniteTailBoundConvergesAt
        (powerSeriesTerm a h)
        μ
        (HasPowerSeriesOnBallWith.tailBound
          convergence
          h
          h-bound)
        (HasPowerSeriesOnBallWith.antitoneModulus convergence)
        (half⁺ ε)
        (approximationIndex ε)
        NatOrder.≤-refl)


powerSeriesSumOnBallFrom-neg :
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  (convergence : HasPowerSeriesOnBall a ρ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBallFrom
    (negPowerSeries a)
    ρ
    (negPowerSeriesOnBall convergence)
    h
    h-bound
  ≡
  -ᶜ powerSeriesSumOnBallFrom a ρ convergence h h-bound
powerSeriesSumOnBallFrom-neg (μ , convergence) h h-bound =
  powerSeriesSumOnBall-neg convergence h h-bound


addPowerSeriesOnBallWith :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesOnBallWith a ρ μ →
  HasPowerSeriesOnBallWith b ρ μ →
  HasPowerSeriesOnBallWith (addPowerSeries a b) ρ (splitModulus μ)
addPowerSeriesOnBallWith {a = a} {b = b} {μ = μ} left right =
  record
    { antitoneModulus =
        splitTailModulus-antitone
          (HasPowerSeriesOnBallWith.antitoneModulus left)
    ; tailBound =
        λ h h-bound →
          subst
            (λ u → TailBound u (splitModulus μ))
            (sym (funExt (addPowerSeriesTerm a b h)))
            (tailBound-add
              (HasPowerSeriesOnBallWith.tailBound left h h-bound)
              (HasPowerSeriesOnBallWith.tailBound right h h-bound))
    }


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
  maxAntitone : AntitoneTailModulus (maxModulus μ ν)
  maxAntitone =
    maxTailModulus-antitone
      (HasPowerSeriesOnBallWith.antitoneModulus left)
      (HasPowerSeriesOnBallWith.antitoneModulus right)

  leftMax : HasPowerSeriesOnBallWith a _ (maxModulus μ ν)
  leftMax =
    record
      { antitoneModulus = maxAntitone
      ; tailBound =
          λ h h-bound →
            tailBound-max-left
              (HasPowerSeriesOnBallWith.tailBound left h h-bound)
      }

  rightMax : HasPowerSeriesOnBallWith b _ (maxModulus μ ν)
  rightMax =
    record
      { antitoneModulus = maxAntitone
      ; tailBound =
          λ h h-bound →
            tailBound-max-right
              (HasPowerSeriesOnBallWith.tailBound right h h-bound)
      }


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


rationalScalePowerSeriesOnBallWith :
  (q : ℚ) →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesOnBallWith a ρ μ →
  HasPowerSeriesOnBallWith
    (rationalScalePowerSeries q a)
    ρ
    (rationalScaleModulus q μ)
rationalScalePowerSeriesOnBallWith q {a = a} {μ = μ} convergence =
  record
    { antitoneModulus =
        rationalScaleModulus-antitone
          q
          (HasPowerSeriesOnBallWith.antitoneModulus convergence)
    ; tailBound =
        λ h h-bound →
          subst
            (λ u → TailBound u (rationalScaleModulus q μ))
            (sym (funExt (rationalScalePowerSeriesTerm q a h)))
            (rationalScaleTailBound
              q
              (HasPowerSeriesOnBallWith.tailBound convergence h h-bound))
    }


rationalScalePowerSeriesOnBall :
  (q : ℚ) →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBall a ρ →
  HasPowerSeriesOnBall (rationalScalePowerSeries q a) ρ
rationalScalePowerSeriesOnBall q (μ , convergence) =
  rationalScaleModulus q μ ,
  rationalScalePowerSeriesOnBallWith q convergence


realScalePowerSeriesOnBallWith :
  (x : ℝᶜ) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ x →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesOnBallWith a ρ μ →
  HasPowerSeriesOnBallWith
    (realScalePowerSeries x a)
    ρ
    (realScaleModulus κ μ)
realScalePowerSeriesOnBallWith x κ x-bound {a = a} {μ = μ} convergence =
  record
    { antitoneModulus =
        realScaleModulus-antitone
          κ
          (HasPowerSeriesOnBallWith.antitoneModulus convergence)
    ; tailBound =
        λ h h-bound →
          subst
            (λ u → TailBound u (realScaleModulus κ μ))
            (sym (funExt (realScalePowerSeriesTerm x a h)))
            (realScaleTailBound
              x
              κ
              x-bound
              (HasPowerSeriesOnBallWith.tailBound convergence h h-bound))
    }


realScalePowerSeriesOnBall :
  (x : ℝᶜ) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ x →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  HasPowerSeriesOnBall a ρ →
  HasPowerSeriesOnBall (realScalePowerSeries x a) ρ
realScalePowerSeriesOnBall x κ x-bound (μ , convergence) =
  realScaleModulus κ μ ,
  realScalePowerSeriesOnBallWith x κ x-bound convergence


powerSeriesSumOnBall-rationalScale :
  (q : ℚ) →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    (rationalScalePowerSeries q a)
    ρ
    (rationalScaleModulus q μ)
    (rationalScalePowerSeriesOnBallWith q convergence)
    h
    h-bound
  ≡
  rational q ·ᶜ powerSeriesSumOnBall a ρ μ convergence h h-bound
powerSeriesSumOnBall-rationalScale
  q
  {a = a}
  {ρ = ρ}
  {μ = μ}
  convergence
  h
  h-bound =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    scaledSum
    scaledOriginalSum
    closeAt
  where
  scaledConvergence :
    HasPowerSeriesOnBallWith
      (rationalScalePowerSeries q a)
      ρ
      (rationalScaleModulus q μ)
  scaledConvergence =
    rationalScalePowerSeriesOnBallWith q convergence

  q-bound : BoundedByᶜ (scalar-bound q) (rational q)
  q-bound =
    rational-bound→boundedᶜ
      (scalar-bound q)
      q
      (scalar-bound-rational-boundᶜ q)

  scaledSum : ℝᶜ
  scaledSum =
    powerSeriesSumOnBall
      (rationalScalePowerSeries q a)
      ρ
      (rationalScaleModulus q μ)
      scaledConvergence
      h
      h-bound

  originalSum : ℝᶜ
  originalSum =
    powerSeriesSumOnBall a ρ μ convergence h h-bound

  scaledOriginalSum : ℝᶜ
  scaledOriginalSum =
    rational q ·ᶜ originalSum

  scaleModulus : ℚ⁺ → ℚ⁺
  scaleModulus =
    fst (mulᶜ-continuous-right-with-bound (scalar-bound q) (rational q) q-bound)

  leftIndex :
    ℚ⁺ →
    ℕ
  leftIndex ε =
    rationalScaleModulus
      q
      μ
      (quarter⁺ (half⁺ (half⁺ ε)))

  rightIndex :
    ℚ⁺ →
    ℕ
  rightIndex ε =
    μ (quarter⁺ (half⁺ (scaleModulus (half⁺ ε))))

  approximationIndex :
    ℚ⁺ →
    ℕ
  approximationIndex ε =
    max (leftIndex ε) (rightIndex ε)

  leftIndex≤approximation :
    (ε : ℚ⁺) →
    NatOrder._≤_ (leftIndex ε) (approximationIndex ε)
  leftIndex≤approximation ε =
    NatOrder.left-≤-max
      {m = leftIndex ε}
      {n = rightIndex ε}

  rightIndex≤approximation :
    (ε : ℚ⁺) →
    NatOrder._≤_ (rightIndex ε) (approximationIndex ε)
  rightIndex≤approximation ε =
    NatOrder.right-≤-max
      {n = rightIndex ε}
      {m = leftIndex ε}

  scaledPartialSum :
    ℚ⁺ →
    ℝᶜ
  scaledPartialSum ε =
    rational q ·ᶜ powerSeriesPartialSum a h (approximationIndex ε)

  leftTail :
    (ε : ℚ⁺) →
    scaledSum ∼[ half⁺ ε ] scaledPartialSum ε
  leftTail ε =
    subst
      (λ partial → scaledSum ∼[ half⁺ ε ] partial)
      (powerSeriesPartialSum-rationalScale q a h (approximationIndex ε))
      (seriesSumFromFiniteTailBoundConvergesAt
        (powerSeriesTerm (rationalScalePowerSeries q a) h)
        (rationalScaleModulus q μ)
        (HasPowerSeriesOnBallWith.tailBound
          scaledConvergence
          h
          h-bound)
        (HasPowerSeriesOnBallWith.antitoneModulus scaledConvergence)
        (half⁺ ε)
        (approximationIndex ε)
        (leftIndex≤approximation ε))

  rightTail :
    (ε : ℚ⁺) →
    scaledOriginalSum ∼[ half⁺ ε ] scaledPartialSum ε
  rightTail ε =
    seriesSumFromFiniteTailBound-mul-left-convergesAt
      (rational q)
      (scalar-bound q)
      q-bound
      (powerSeriesTerm a h)
      μ
      (HasPowerSeriesOnBallWith.tailBound convergence h h-bound)
      (HasPowerSeriesOnBallWith.antitoneModulus convergence)
      (half⁺ ε)
      (approximationIndex ε)
      (rightIndex≤approximation ε)

  closeAt :
    (ε : ℚ⁺) →
    scaledSum ∼[ ε ] scaledOriginalSum
  closeAt ε =
    subst
      (λ κ → scaledSum ∼[ κ ] scaledOriginalSum)
      (half⁺+half⁺≡ ε)
      (MetricSpace.close-triangle
        CauchyRealsMetricSpace
        (leftTail ε)
        (MetricSpace.close-sym CauchyRealsMetricSpace (rightTail ε)))


powerSeriesSumOnBall-realScale :
  (x : ℝᶜ) →
  (κ : ℚ⁺) →
  (x-bound : BoundedByᶜ κ x) →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  (convergence : HasPowerSeriesOnBallWith a ρ μ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    (realScalePowerSeries x a)
    ρ
    (realScaleModulus κ μ)
    (realScalePowerSeriesOnBallWith x κ x-bound convergence)
    h
    h-bound
  ≡
  x ·ᶜ powerSeriesSumOnBall a ρ μ convergence h h-bound
powerSeriesSumOnBall-realScale
  x
  κ
  x-bound
  {a = a}
  {ρ = ρ}
  {μ = μ}
  convergence
  h
  h-bound =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    scaledSum
    scaledOriginalSum
    closeAt
  where
  scaledConvergence :
    HasPowerSeriesOnBallWith
      (realScalePowerSeries x a)
      ρ
      (realScaleModulus κ μ)
  scaledConvergence =
    realScalePowerSeriesOnBallWith x κ x-bound convergence

  scaledSum : ℝᶜ
  scaledSum =
    powerSeriesSumOnBall
      (realScalePowerSeries x a)
      ρ
      (realScaleModulus κ μ)
      scaledConvergence
      h
      h-bound

  originalSum : ℝᶜ
  originalSum =
    powerSeriesSumOnBall a ρ μ convergence h h-bound

  scaledOriginalSum : ℝᶜ
  scaledOriginalSum =
    x ·ᶜ originalSum

  scaleModulus : ℚ⁺ → ℚ⁺
  scaleModulus =
    fst (mulᶜ-continuous-right-with-bound κ x x-bound)

  leftIndex :
    ℚ⁺ →
    ℕ
  leftIndex ε =
    realScaleModulus
      κ
      μ
      (quarter⁺ (half⁺ (half⁺ ε)))

  rightIndex :
    ℚ⁺ →
    ℕ
  rightIndex ε =
    μ (quarter⁺ (half⁺ (scaleModulus (half⁺ ε))))

  approximationIndex :
    ℚ⁺ →
    ℕ
  approximationIndex ε =
    max (leftIndex ε) (rightIndex ε)

  leftIndex≤approximation :
    (ε : ℚ⁺) →
    NatOrder._≤_ (leftIndex ε) (approximationIndex ε)
  leftIndex≤approximation ε =
    NatOrder.left-≤-max
      {m = leftIndex ε}
      {n = rightIndex ε}

  rightIndex≤approximation :
    (ε : ℚ⁺) →
    NatOrder._≤_ (rightIndex ε) (approximationIndex ε)
  rightIndex≤approximation ε =
    NatOrder.right-≤-max
      {n = rightIndex ε}
      {m = leftIndex ε}

  scaledPartialSum :
    ℚ⁺ →
    ℝᶜ
  scaledPartialSum ε =
    x ·ᶜ powerSeriesPartialSum a h (approximationIndex ε)

  leftTail :
    (ε : ℚ⁺) →
    scaledSum ∼[ half⁺ ε ] scaledPartialSum ε
  leftTail ε =
    subst
      (λ partial → scaledSum ∼[ half⁺ ε ] partial)
      (powerSeriesPartialSum-realScale x a h (approximationIndex ε))
      (seriesSumFromFiniteTailBoundConvergesAt
        (powerSeriesTerm (realScalePowerSeries x a) h)
        (realScaleModulus κ μ)
        (HasPowerSeriesOnBallWith.tailBound
          scaledConvergence
          h
          h-bound)
        (HasPowerSeriesOnBallWith.antitoneModulus scaledConvergence)
        (half⁺ ε)
        (approximationIndex ε)
        (leftIndex≤approximation ε))

  rightTail :
    (ε : ℚ⁺) →
    scaledOriginalSum ∼[ half⁺ ε ] scaledPartialSum ε
  rightTail ε =
    seriesSumFromFiniteTailBound-mul-left-convergesAt
      x
      κ
      x-bound
      (powerSeriesTerm a h)
      μ
      (HasPowerSeriesOnBallWith.tailBound convergence h h-bound)
      (HasPowerSeriesOnBallWith.antitoneModulus convergence)
      (half⁺ ε)
      (approximationIndex ε)
      (rightIndex≤approximation ε)

  closeAt :
    (ε : ℚ⁺) →
    scaledSum ∼[ ε ] scaledOriginalSum
  closeAt ε =
    subst
      (λ θ → scaledSum ∼[ θ ] scaledOriginalSum)
      (half⁺+half⁺≡ ε)
      (MetricSpace.close-triangle
        CauchyRealsMetricSpace
        (leftTail ε)
        (MetricSpace.close-sym CauchyRealsMetricSpace (rightTail ε)))


powerSeriesSumOnBallFrom-rationalScale :
  (q : ℚ) →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  (convergence : HasPowerSeriesOnBall a ρ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBallFrom
    (rationalScalePowerSeries q a)
    ρ
    (rationalScalePowerSeriesOnBall q convergence)
    h
    h-bound
  ≡
  rational q ·ᶜ powerSeriesSumOnBallFrom a ρ convergence h h-bound
powerSeriesSumOnBallFrom-rationalScale q (μ , convergence) h h-bound =
  powerSeriesSumOnBall-rationalScale q convergence h h-bound


powerSeriesSumOnBallFrom-realScale :
  (x : ℝᶜ) →
  (κ : ℚ⁺) →
  (x-bound : BoundedByᶜ κ x) →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  (convergence : HasPowerSeriesOnBall a ρ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBallFrom
    (realScalePowerSeries x a)
    ρ
    (realScalePowerSeriesOnBall x κ x-bound convergence)
    h
    h-bound
  ≡
  x ·ᶜ powerSeriesSumOnBallFrom a ρ convergence h h-bound
powerSeriesSumOnBallFrom-realScale x κ x-bound (μ , convergence) h h-bound =
  powerSeriesSumOnBall-realScale x κ x-bound convergence h h-bound


powerSeriesSumOnBall-subWithMax :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν : ℚ⁺ → ℕ} →
  (left : HasPowerSeriesOnBallWith a ρ μ) →
  (right : HasPowerSeriesOnBallWith b ρ ν) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    (subPowerSeries a b)
    ρ
    (splitModulus (maxModulus μ ν))
    (subPowerSeriesOnBallWithMax left right)
    h
    h-bound
  ≡
  powerSeriesSumOnBall a ρ μ left h h-bound +ᶜ
  (-ᶜ powerSeriesSumOnBall b ρ ν right h h-bound)
powerSeriesSumOnBall-subWithMax left right h h-bound =
  powerSeriesSumOnBall-addWithMax
    left
    (negPowerSeriesOnBallWith right)
    h
    h-bound ∙
  cong
    (powerSeriesSumOnBall _ _ _ left h h-bound +ᶜ_)
    (powerSeriesSumOnBall-neg right h h-bound)


powerSeriesSumOnBallFrom-sub :
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  (left : HasPowerSeriesOnBall a ρ) →
  (right : HasPowerSeriesOnBall b ρ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBallFrom
    (subPowerSeries a b)
    ρ
    (subPowerSeriesOnBall left right)
    h
    h-bound
  ≡
  powerSeriesSumOnBallFrom a ρ left h h-bound +ᶜ
  (-ᶜ powerSeriesSumOnBallFrom b ρ right h h-bound)
powerSeriesSumOnBallFrom-sub (μ , left) (ν , right) h h-bound =
  powerSeriesSumOnBall-subWithMax left right h h-bound


negPowerSeriesRadius :
  {a : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius a R →
  HasPowerSeriesRadius (negPowerSeries a) R
negPowerSeriesRadius radiusData =
  record
    { onSubball =
        λ ρ ρ<R →
          negPowerSeriesOnBall
            (HasPowerSeriesRadius.onSubball radiusData ρ ρ<R)
    }


addPowerSeriesRadius :
  {a b : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius a R →
  HasPowerSeriesRadius b R →
  HasPowerSeriesRadius (addPowerSeries a b) R
addPowerSeriesRadius left right =
  record
    { onSubball =
        λ ρ ρ<R →
          addPowerSeriesOnBall
            (HasPowerSeriesRadius.onSubball left ρ ρ<R)
            (HasPowerSeriesRadius.onSubball right ρ ρ<R)
    }


subPowerSeriesRadius :
  {a b : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius a R →
  HasPowerSeriesRadius b R →
  HasPowerSeriesRadius (subPowerSeries a b) R
subPowerSeriesRadius left right =
  record
    { onSubball =
        λ ρ ρ<R →
          subPowerSeriesOnBall
            (HasPowerSeriesRadius.onSubball left ρ ρ<R)
            (HasPowerSeriesRadius.onSubball right ρ ρ<R)
    }


rationalScalePowerSeriesRadius :
  (q : ℚ) →
  {a : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius a R →
  HasPowerSeriesRadius (rationalScalePowerSeries q a) R
rationalScalePowerSeriesRadius q radiusData =
  record
    { onSubball =
        λ ρ ρ<R →
          rationalScalePowerSeriesOnBall
            q
            (HasPowerSeriesRadius.onSubball radiusData ρ ρ<R)
    }


realScalePowerSeriesRadius :
  (x : ℝᶜ) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ x →
  {a : PowerSeries} →
  {R : ℚ⁺} →
  HasPowerSeriesRadius a R →
  HasPowerSeriesRadius (realScalePowerSeries x a) R
realScalePowerSeriesRadius x κ x-bound radiusData =
  record
    { onSubball =
        λ ρ ρ<R →
          realScalePowerSeriesOnBall
            x
            κ
            x-bound
            (HasPowerSeriesRadius.onSubball radiusData ρ ρ<R)
    }


negPowerSeriesInfiniteRadius :
  {a : PowerSeries} →
  HasInfinitePowerSeriesRadius a →
  HasInfinitePowerSeriesRadius (negPowerSeries a)
negPowerSeriesInfiniteRadius radiusData ρ =
  negPowerSeriesOnBall (radiusData ρ)


centeredPowerSeriesSumEverywhere-neg :
  {a : PowerSeries} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (c x : ℝᶜ) →
  centeredPowerSeriesSumEverywhere
    (negPowerSeries a)
    c
    (negPowerSeriesInfiniteRadius radiusData)
    x
  ≡
  -ᶜ centeredPowerSeriesSumEverywhere a c radiusData x
centeredPowerSeriesSumEverywhere-neg
  {a = a}
  radiusData
  c
  x =
  Prop.elim
    {P = λ bounds →
      left ≡ -ᶜ centeredPowerSeriesSumEverywhere a c radiusData x}
    (λ _ → MetricSpace.isSetCarrier CauchyRealsMetricSpace _ _)
    step
    (merely-boundedᶜ (centeredDisplacement c x))
  where
  left : ℝᶜ
  left =
    centeredPowerSeriesSumEverywhere
      (negPowerSeries a)
      c
      (negPowerSeriesInfiniteRadius radiusData)
      x

  step :
    Σ[ ρ ∈ ℚ⁺ ] BoundedByᶜ ρ (centeredDisplacement c x) →
    left ≡ -ᶜ centeredPowerSeriesSumEverywhere a c radiusData x
  step (ρ , displacementBound) =
    centeredPowerSeriesSumEverywhere-bound-path
      (negPowerSeries a)
      c
      (negPowerSeriesInfiniteRadius radiusData)
      ρ
      x
      inBall ∙
    powerSeriesSumOnBallFrom-neg
      (radiusData ρ)
      (centeredDisplacement c x)
      displacementBound ∙
    sym
      (cong
        -ᶜ_
        (centeredPowerSeriesSumEverywhere-bound-path
          a
          c
          radiusData
          ρ
          x
          inBall))
    where
    inBall : InPowerSeriesBall c ρ x
    inBall =
      record { displacementBound = displacementBound }


addPowerSeriesInfiniteRadius :
  {a b : PowerSeries} →
  HasInfinitePowerSeriesRadius a →
  HasInfinitePowerSeriesRadius b →
  HasInfinitePowerSeriesRadius (addPowerSeries a b)
addPowerSeriesInfiniteRadius left right ρ =
  addPowerSeriesOnBall (left ρ) (right ρ)


centeredPowerSeriesSumEverywhere-add :
  {a b : PowerSeries} →
  (leftRadius : HasInfinitePowerSeriesRadius a) →
  (rightRadius : HasInfinitePowerSeriesRadius b) →
  (c x : ℝᶜ) →
  centeredPowerSeriesSumEverywhere
    (addPowerSeries a b)
    c
    (addPowerSeriesInfiniteRadius leftRadius rightRadius)
    x
  ≡
  centeredPowerSeriesSumEverywhere a c leftRadius x +ᶜ
  centeredPowerSeriesSumEverywhere b c rightRadius x
centeredPowerSeriesSumEverywhere-add
  {a = a}
  {b = b}
  leftRadius
  rightRadius
  c
  x =
  Prop.elim
    {P = λ bounds →
      addSum ≡
      centeredPowerSeriesSumEverywhere a c leftRadius x +ᶜ
      centeredPowerSeriesSumEverywhere b c rightRadius x}
    (λ _ → MetricSpace.isSetCarrier CauchyRealsMetricSpace _ _)
    step
    (merely-boundedᶜ (centeredDisplacement c x))
  where
  addSum : ℝᶜ
  addSum =
    centeredPowerSeriesSumEverywhere
      (addPowerSeries a b)
      c
      (addPowerSeriesInfiniteRadius leftRadius rightRadius)
      x

  step :
    Σ[ ρ ∈ ℚ⁺ ] BoundedByᶜ ρ (centeredDisplacement c x) →
    addSum ≡
    centeredPowerSeriesSumEverywhere a c leftRadius x +ᶜ
    centeredPowerSeriesSumEverywhere b c rightRadius x
  step (ρ , displacementBound) =
    centeredPowerSeriesSumEverywhere-bound-path
      (addPowerSeries a b)
      c
      (addPowerSeriesInfiniteRadius leftRadius rightRadius)
      ρ
      x
      inBall ∙
    powerSeriesSumOnBallFrom-add
      (leftRadius ρ)
      (rightRadius ρ)
      (centeredDisplacement c x)
      displacementBound ∙
    cong₂
      _+ᶜ_
      (sym
        (centeredPowerSeriesSumEverywhere-bound-path
          a
          c
          leftRadius
          ρ
          x
          inBall))
      (sym
        (centeredPowerSeriesSumEverywhere-bound-path
          b
          c
          rightRadius
          ρ
          x
          inBall))
    where
    inBall : InPowerSeriesBall c ρ x
    inBall =
      record { displacementBound = displacementBound }


subPowerSeriesInfiniteRadius :
  {a b : PowerSeries} →
  HasInfinitePowerSeriesRadius a →
  HasInfinitePowerSeriesRadius b →
  HasInfinitePowerSeriesRadius (subPowerSeries a b)
subPowerSeriesInfiniteRadius left right ρ =
  subPowerSeriesOnBall (left ρ) (right ρ)


rationalScalePowerSeriesInfiniteRadius :
  (q : ℚ) →
  {a : PowerSeries} →
  HasInfinitePowerSeriesRadius a →
  HasInfinitePowerSeriesRadius (rationalScalePowerSeries q a)
rationalScalePowerSeriesInfiniteRadius q radiusData ρ =
  rationalScalePowerSeriesOnBall q (radiusData ρ)


realScalePowerSeriesInfiniteRadius :
  (x : ℝᶜ) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ x →
  {a : PowerSeries} →
  HasInfinitePowerSeriesRadius a →
  HasInfinitePowerSeriesRadius (realScalePowerSeries x a)
realScalePowerSeriesInfiniteRadius x κ x-bound radiusData ρ =
  realScalePowerSeriesOnBall x κ x-bound (radiusData ρ)


centeredPowerSeriesSumEverywhere-sub :
  {a b : PowerSeries} →
  (leftRadius : HasInfinitePowerSeriesRadius a) →
  (rightRadius : HasInfinitePowerSeriesRadius b) →
  (c x : ℝᶜ) →
  centeredPowerSeriesSumEverywhere
    (subPowerSeries a b)
    c
    (subPowerSeriesInfiniteRadius leftRadius rightRadius)
    x
  ≡
  centeredPowerSeriesSumEverywhere a c leftRadius x +ᶜ
  (-ᶜ centeredPowerSeriesSumEverywhere b c rightRadius x)
centeredPowerSeriesSumEverywhere-sub
  {a = a}
  {b = b}
  leftRadius
  rightRadius
  c
  x =
  Prop.elim
    {P = λ bounds →
      subSum ≡
      centeredPowerSeriesSumEverywhere a c leftRadius x +ᶜ
      (-ᶜ centeredPowerSeriesSumEverywhere b c rightRadius x)}
    (λ _ → MetricSpace.isSetCarrier CauchyRealsMetricSpace _ _)
    step
    (merely-boundedᶜ (centeredDisplacement c x))
  where
  subSum : ℝᶜ
  subSum =
    centeredPowerSeriesSumEverywhere
      (subPowerSeries a b)
      c
      (subPowerSeriesInfiniteRadius leftRadius rightRadius)
      x

  step :
    Σ[ ρ ∈ ℚ⁺ ] BoundedByᶜ ρ (centeredDisplacement c x) →
    subSum ≡
    centeredPowerSeriesSumEverywhere a c leftRadius x +ᶜ
    (-ᶜ centeredPowerSeriesSumEverywhere b c rightRadius x)
  step (ρ , displacementBound) =
    centeredPowerSeriesSumEverywhere-bound-path
      (subPowerSeries a b)
      c
      (subPowerSeriesInfiniteRadius leftRadius rightRadius)
      ρ
      x
      inBall ∙
    powerSeriesSumOnBallFrom-sub
      (leftRadius ρ)
      (rightRadius ρ)
      (centeredDisplacement c x)
      displacementBound ∙
    cong₂
      _+ᶜ_
      (sym
        (centeredPowerSeriesSumEverywhere-bound-path
          a
          c
          leftRadius
          ρ
          x
          inBall))
      (cong
        -ᶜ_
        (sym
          (centeredPowerSeriesSumEverywhere-bound-path
            b
            c
            rightRadius
            ρ
            x
            inBall)))
    where
    inBall : InPowerSeriesBall c ρ x
    inBall =
      record { displacementBound = displacementBound }


centeredPowerSeriesSumEverywhere-rationalScale :
  (q : ℚ) →
  {a : PowerSeries} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (c x : ℝᶜ) →
  centeredPowerSeriesSumEverywhere
    (rationalScalePowerSeries q a)
    c
    (rationalScalePowerSeriesInfiniteRadius q radiusData)
    x
  ≡
  rational q ·ᶜ centeredPowerSeriesSumEverywhere a c radiusData x
centeredPowerSeriesSumEverywhere-rationalScale
  q
  {a = a}
  radiusData
  c
  x =
  Prop.elim
    {P = λ bounds →
      scaledSum ≡
      rational q ·ᶜ centeredPowerSeriesSumEverywhere a c radiusData x}
    (λ _ → MetricSpace.isSetCarrier CauchyRealsMetricSpace _ _)
    step
    (merely-boundedᶜ (centeredDisplacement c x))
  where
  scaledSum : ℝᶜ
  scaledSum =
    centeredPowerSeriesSumEverywhere
      (rationalScalePowerSeries q a)
      c
      (rationalScalePowerSeriesInfiniteRadius q radiusData)
      x

  step :
    Σ[ ρ ∈ ℚ⁺ ] BoundedByᶜ ρ (centeredDisplacement c x) →
    scaledSum ≡
    rational q ·ᶜ centeredPowerSeriesSumEverywhere a c radiusData x
  step (ρ , displacementBound) =
    centeredPowerSeriesSumEverywhere-bound-path
      (rationalScalePowerSeries q a)
      c
      (rationalScalePowerSeriesInfiniteRadius q radiusData)
      ρ
      x
      inBall ∙
    powerSeriesSumOnBallFrom-rationalScale
      q
      (radiusData ρ)
      (centeredDisplacement c x)
      displacementBound ∙
    cong
      (rational q ·ᶜ_)
      (sym
        (centeredPowerSeriesSumEverywhere-bound-path
          a
          c
          radiusData
          ρ
          x
          inBall))
    where
    inBall : InPowerSeriesBall c ρ x
    inBall =
      record { displacementBound = displacementBound }


centeredPowerSeriesSumEverywhere-realScale :
  (s : ℝᶜ) →
  (κ : ℚ⁺) →
  (s-bound : BoundedByᶜ κ s) →
  {a : PowerSeries} →
  (radiusData : HasInfinitePowerSeriesRadius a) →
  (c x : ℝᶜ) →
  centeredPowerSeriesSumEverywhere
    (realScalePowerSeries s a)
    c
    (realScalePowerSeriesInfiniteRadius s κ s-bound radiusData)
    x
  ≡
  s ·ᶜ centeredPowerSeriesSumEverywhere a c radiusData x
centeredPowerSeriesSumEverywhere-realScale
  s
  κ
  s-bound
  {a = a}
  radiusData
  c
  x =
  Prop.elim
    {P = λ bounds →
      scaledSum ≡
      s ·ᶜ centeredPowerSeriesSumEverywhere a c radiusData x}
    (λ _ → MetricSpace.isSetCarrier CauchyRealsMetricSpace _ _)
    step
    (merely-boundedᶜ (centeredDisplacement c x))
  where
  scaledSum : ℝᶜ
  scaledSum =
    centeredPowerSeriesSumEverywhere
      (realScalePowerSeries s a)
      c
      (realScalePowerSeriesInfiniteRadius s κ s-bound radiusData)
      x

  step :
    Σ[ ρ ∈ ℚ⁺ ] BoundedByᶜ ρ (centeredDisplacement c x) →
    scaledSum ≡
    s ·ᶜ centeredPowerSeriesSumEverywhere a c radiusData x
  step (ρ , displacementBound) =
    centeredPowerSeriesSumEverywhere-bound-path
      (realScalePowerSeries s a)
      c
      (realScalePowerSeriesInfiniteRadius s κ s-bound radiusData)
      ρ
      x
      inBall ∙
    powerSeriesSumOnBallFrom-realScale
      s
      κ
      s-bound
      (radiusData ρ)
      (centeredDisplacement c x)
      displacementBound ∙
    cong
      (s ·ᶜ_)
      (sym
        (centeredPowerSeriesSumEverywhere-bound-path
          a
          c
          radiusData
          ρ
          x
          inBall))
    where
    inBall : InPowerSeriesBall c ρ x
    inBall =
      record { displacementBound = displacementBound }
