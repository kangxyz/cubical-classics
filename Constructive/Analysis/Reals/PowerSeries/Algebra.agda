{-

Algebraic operations on power-series coefficients

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Algebra where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
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


rationalScalePowerSeriesTerm :
  (q : ℚ) →
  (a : PowerSeries) →
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesTerm (rationalScalePowerSeries q a) h n ≡
  rational q ·ᶜ powerSeriesTerm a h n
rationalScalePowerSeriesTerm q a h n =
  sym (mulᶜ-assoc-rational-left q (a n) (realPower h n))


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


negPowerSeriesInfiniteRadius :
  {a : PowerSeries} →
  HasInfinitePowerSeriesRadius a →
  HasInfinitePowerSeriesRadius (negPowerSeries a)
negPowerSeriesInfiniteRadius radiusData ρ =
  negPowerSeriesOnBall (radiusData ρ)


addPowerSeriesInfiniteRadius :
  {a b : PowerSeries} →
  HasInfinitePowerSeriesRadius a →
  HasInfinitePowerSeriesRadius b →
  HasInfinitePowerSeriesRadius (addPowerSeries a b)
addPowerSeriesInfiniteRadius left right ρ =
  addPowerSeriesOnBall (left ρ) (right ρ)


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
