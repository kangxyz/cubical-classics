{-

Series tail infrastructure for HoTT Cauchy reals

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Series.Tail where

open import Cubical.Foundations.Prelude

import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.FinData.Base using (Fin)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.Data.Sum as Sum using (inl ; inr)

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Base
import Constructive.Analysis.Metric.Cauchy as MetricCauchy
open import Constructive.Analysis.Metric.Instances.CauchyReals
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
open import Constructive.Analysis.Reals.CauchyReals.Order.Rational
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
  using (≤ᶜ-add ; negᶜ-pres≤ᶜ)
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open ClosenessOf RationalsMetricSpace

open import Constructive.Analysis.Reals.Series.Finite

drop :
  ℕ →
  (ℕ → ℝᶜ) →
  ℕ →
  ℝᶜ
drop zero u =
  u
drop (suc n) u =
  drop n (λ k → u (suc k))


drop-index :
  (m : ℕ) →
  (u : ℕ → ℝᶜ) →
  (n : ℕ) →
  drop m u n ≡ u (m + n)
drop-index zero u n =
  refl
drop-index (suc m) u n =
  drop-index m (λ k → u (suc k)) n


drop-suc :
  (m : ℕ) →
  (u : ℕ → ℝᶜ) →
  (λ n → drop m u (suc n)) ≡ drop (suc m) u
drop-suc zero u =
  refl
drop-suc (suc m) u =
  drop-suc m (λ n → u (suc n))


drop-zero :
  (m : ℕ) →
  (u : ℕ → ℝᶜ) →
  drop m u zero ≡ u m
drop-zero m u =
  drop-index m u zero ∙
  cong u (Nat.+-zero m)


tailSum :
  (ℕ → ℝᶜ) →
  ℕ →
  ℕ →
  ℝᶜ
tailSum u m k =
  partialSum (drop m u) k


drop-+ :
  (m n : ℕ) →
  (u : ℕ → ℝᶜ) →
  drop n (drop m u) ≡ drop (m + n) u
drop-+ zero n u =
  refl
drop-+ (suc m) n u =
  drop-+ m n (λ k → u (suc k))


tailSum-drop :
  (u : ℕ → ℝᶜ) →
  (m n k : ℕ) →
  tailSum (drop m u) n k ≡ tailSum u (m + n) k
tailSum-drop u m n k =
  cong (λ v → partialSum v k) (drop-+ m n u)


tailSum-zero :
  (u : ℕ → ℝᶜ) →
  (m : ℕ) →
  tailSum u m zero ≡ 0ᶜ
tailSum-zero u m =
  refl


tailSum-suc :
  (u : ℕ → ℝᶜ) →
  (m k : ℕ) →
  tailSum u m (suc k) ≡
  drop m u zero +ᶜ tailSum (λ n → drop m u (suc n)) zero k
tailSum-suc u m k =
  refl


tailSum-suc-start :
  (u : ℕ → ℝᶜ) →
  (m k : ℕ) →
  tailSum u m (suc k) ≡
  u m +ᶜ tailSum u (suc m) k
tailSum-suc-start u m k =
  cong₂
    _+ᶜ_
    (drop-zero m u)
    (cong (λ v → partialSum v k) (drop-suc m u))


tailSum-one :
  (u : ℕ → ℝᶜ) →
  (n : ℕ) →
  tailSum u n (suc zero) ≡ u n
tailSum-one u n =
  tailSum-suc-start u n zero ∙
  cong (u n +ᶜ_) (tailSum-zero u (suc n)) ∙
  add-zero-right (u n)


partialSum-append :
  (u : ℕ → ℝᶜ) →
  (m n : ℕ) →
  partialSum u (m + n) ≡ partialSum u m +ᶜ tailSum u m n
partialSum-append u zero n =
  sym (add-zero-left (tailSum u zero n))
partialSum-append u (suc m) n =
  cong (u zero +ᶜ_) (partialSum-append (λ k → u (suc k)) m n) ∙
  add-assoc
    (u zero)
    (partialSum (λ k → u (suc k)) m)
    (tailSum u (suc m) n)


partialSum-snoc :
  (u : ℕ → ℝᶜ) →
  (n : ℕ) →
  partialSum u (suc n) ≡ partialSum u n +ᶜ u n
partialSum-snoc u n =
  cong (partialSum u) (sym n+1≡sucn) ∙
  partialSum-append u n (suc zero) ∙
  cong (partialSum u n +ᶜ_) (tailSum-one u n)
  where
  n+1≡sucn : n + suc zero ≡ suc n
  n+1≡sucn =
    Nat.+-suc n zero ∙
    cong suc (Nat.+-zero n)


partialSum-diff-right-tail≤ :
  (u : ℕ → ℝᶜ) →
  (m n : ℕ) →
  NatOrder._≤_ m n →
  Σ[ k ∈ ℕ ]
    partialSum u n +ᶜ (-ᶜ partialSum u m) ≡ tailSum u m k
partialSum-diff-right-tail≤ u m n (k , k+m≡n) =
  k , diff-path
  where
  m+k≡n : m + k ≡ n
  m+k≡n =
    Nat.+-comm m k ∙ k+m≡n

  tail : ℝᶜ
  tail =
    tailSum u m k

  sum-path : partialSum u n ≡ partialSum u m +ᶜ tail
  sum-path =
    sym (cong (partialSum u) m+k≡n) ∙
    partialSum-append u m k

  diff-path :
    partialSum u n +ᶜ (-ᶜ partialSum u m) ≡ tail
  diff-path =
    cong (_+ᶜ (-ᶜ partialSum u m)) sum-path ∙
    cong (_+ᶜ (-ᶜ partialSum u m))
      (add-comm (partialSum u m) tail) ∙
    plus-minus-cancel-right tail (partialSum u m)


partialSum-diff-left-tail≤ :
  (u : ℕ → ℝᶜ) →
  (m n : ℕ) →
  NatOrder._≤_ m n →
  Σ[ k ∈ ℕ ]
    partialSum u m +ᶜ (-ᶜ partialSum u n) ≡ -ᶜ tailSum u m k
partialSum-diff-left-tail≤ u m n (k , k+m≡n) =
  k , diff-path
  where
  m+k≡n : m + k ≡ n
  m+k≡n =
    Nat.+-comm m k ∙ k+m≡n

  tail : ℝᶜ
  tail =
    tailSum u m k

  sum-path : partialSum u n ≡ partialSum u m +ᶜ tail
  sum-path =
    sym (cong (partialSum u) m+k≡n) ∙
    partialSum-append u m k

  diff-path :
    partialSum u m +ᶜ (-ᶜ partialSum u n) ≡ -ᶜ tail
  diff-path =
    cong (λ z → partialSum u m +ᶜ (-ᶜ z)) sum-path ∙
    cong (partialSum u m +ᶜ_) (neg-add (partialSum u m) tail) ∙
    add-assoc (partialSum u m) (-ᶜ partialSum u m) (-ᶜ tail) ∙
    cong (_+ᶜ (-ᶜ tail)) (add-inverse-right (partialSum u m)) ∙
    add-zero-left (-ᶜ tail)


drop-absoluteTerms :
  (m : ℕ) →
  (u : ℕ → ℝᶜ) →
  drop m (λ n → absᶜ (u n)) ≡ (λ n → absᶜ (drop m u n))
drop-absoluteTerms zero u =
  refl
drop-absoluteTerms (suc m) u =
  drop-absoluteTerms m (λ n → u (suc n))


drop-add :
  (m : ℕ) →
  (u v : ℕ → ℝᶜ) →
  drop m (λ n → u n +ᶜ v n) ≡
  (λ n → drop m u n +ᶜ drop m v n)
drop-add zero u v =
  refl
drop-add (suc m) u v =
  drop-add m (λ n → u (suc n)) (λ n → v (suc n))


drop-neg :
  (m : ℕ) →
  (u : ℕ → ℝᶜ) →
  drop m (λ n → -ᶜ u n) ≡
  (λ n → -ᶜ drop m u n)
drop-neg zero u =
  refl
drop-neg (suc m) u =
  drop-neg m (λ n → u (suc n))


tailSum-absoluteTerms :
  (u : ℕ → ℝᶜ) →
  (m k : ℕ) →
  tailSum (λ n → absᶜ (u n)) m k ≡
  partialSum (λ n → absᶜ (drop m u n)) k
tailSum-absoluteTerms u m k =
  cong (λ v → partialSum v k) (drop-absoluteTerms m u)


tailSum-abs-bound :
  (u : ℕ → ℝᶜ) →
  (m k : ℕ) →
  absᶜ (tailSum u m k) ≤ᶜ
  partialSum (λ n → absᶜ (drop m u n)) k
tailSum-abs-bound u m k =
  partialSum-abs-bound (drop m u) k


tailSum-nonnegative :
  (u : ℕ → ℝᶜ) →
  ((n : ℕ) → 0ᶜ ≤ᶜ u n) →
  (m k : ℕ) →
  0ᶜ ≤ᶜ tailSum u m k
tailSum-nonnegative u 0≤u m k =
  partialSum-nonnegative
    (drop m u)
    (λ n →
      subst
        (λ x → 0ᶜ ≤ᶜ x)
        (sym (drop-index m u n))
        (0≤u (m + n)))
    k


tailSum-add :
  (u v : ℕ → ℝᶜ) →
  (m k : ℕ) →
  tailSum (λ n → u n +ᶜ v n) m k ≡
  tailSum u m k +ᶜ tailSum v m k
tailSum-add u v m k =
  cong (λ w → partialSum w k) (drop-add m u v) ∙
  partialSum-add (drop m u) (drop m v) k


tailSum-neg :
  (u : ℕ → ℝᶜ) →
  (m k : ℕ) →
  tailSum (λ n → -ᶜ u n) m k ≡ -ᶜ tailSum u m k
tailSum-neg u m k =
  cong (λ w → partialSum w k) (drop-neg m u) ∙
  partialSum-neg (drop m u) k


TailBound :
  (ℕ → ℝᶜ) →
  (ℚ⁺ → ℕ) →
  Type₀
TailBound u μ =
  (ε : ℚ⁺) →
  (m k : ℕ) →
  NatOrder._≤_ (μ ε) m →
  BoundedByᶜ ε (tailSum u m k)


tailBound-drop :
  {u : ℕ → ℝᶜ} {μ : ℚ⁺ → ℕ} →
  TailBound u μ →
  (m : ℕ) →
  TailBound (drop m u) μ
tailBound-drop {u = u} tailBound m ε n k μ≤n =
  subst
    (BoundedByᶜ ε)
    (sym (tailSum-drop u m n k))
    (tailBound ε (m + n) k μ≤m+n)
  where
  μ≤m+n : NatOrder._≤_ _ (m + n)
  μ≤m+n =
    NatOrder.≤-trans μ≤n (m , refl)


tailBound-lift-drop :
  {u : ℕ → ℝᶜ} {μ : ℚ⁺ → ℕ} →
  (m : ℕ) →
  TailBound (drop m u) μ →
  TailBound u (λ ε → m + μ ε)
tailBound-lift-drop {u = u} {μ = μ} m dropTail ε n k m+μ≤n =
  subst
    (BoundedByᶜ ε)
    (tailSum-drop u m d k ∙ cong (λ l → tailSum u l k) m+d≡n)
    (dropTail ε d k μ≤d)
  where
  j : ℕ
  j =
    m+μ≤n .fst

  j+m+μ≡n :
    j + (m + μ ε) ≡ n
  j+m+μ≡n =
    m+μ≤n .snd

  d : ℕ
  d =
    j + μ ε

  μ≤d : NatOrder._≤_ (μ ε) d
  μ≤d =
    j , refl

  m+d≡n : m + d ≡ n
  m+d≡n =
    Nat.+-assoc m j (μ ε) ∙
    cong (_+ μ ε) (Nat.+-comm m j) ∙
    sym (Nat.+-assoc j m (μ ε)) ∙
    j+m+μ≡n


AntitoneTailModulus :
  (ℚ⁺ → ℕ) →
  Type₀
AntitoneTailModulus μ =
  {ε δ : ℚ⁺} →
  radius ε ℚOrder.≤ radius δ →
  NatOrder._≤_ (μ δ) (μ ε)


antitoneTailModulus-lift-drop :
  {μ : ℚ⁺ → ℕ} →
  (m : ℕ) →
  AntitoneTailModulus μ →
  AntitoneTailModulus (λ ε → m + μ ε)
antitoneTailModulus-lift-drop m μ-ant ε≤δ =
  NatOrder.≤-k+ (μ-ant ε≤δ)


tailBound-pair :
  {u : ℕ → ℝᶜ} {μ : ℚ⁺ → ℕ} →
  TailBound u μ →
  (κ : ℚ⁺) →
  (m n : ℕ) →
  NatOrder._≤_ (μ κ) m →
  NatOrder._≤_ (μ κ) n →
  BoundedByᶜ κ (partialSum u m +ᶜ (-ᶜ partialSum u n))
tailBound-pair {u = u} tailBound κ m n μκ≤m μκ≤n =
  Sum.rec left right (NatOrder.splitℕ-≤ m n)
  where
  left :
    NatOrder._≤_ m n →
    BoundedByᶜ κ (partialSum u m +ᶜ (-ᶜ partialSum u n))
  left m≤n =
    subst
      (BoundedByᶜ κ)
      (sym diff-path)
      (bounded-byᶜ-neg κ (tailSum u m k) (tailBound κ m k μκ≤m))
    where
    diff : Σ[ k ∈ ℕ ]
      partialSum u m +ᶜ (-ᶜ partialSum u n) ≡ -ᶜ tailSum u m k
    diff =
      partialSum-diff-left-tail≤ u m n m≤n

    k : ℕ
    k =
      diff .fst

    diff-path :
      partialSum u m +ᶜ (-ᶜ partialSum u n) ≡ -ᶜ tailSum u m k
    diff-path =
      diff .snd

  right :
    NatOrder._<_ n m →
    BoundedByᶜ κ (partialSum u m +ᶜ (-ᶜ partialSum u n))
  right n<m =
    subst
      (BoundedByᶜ κ)
      (sym diff-path)
      (tailBound κ n k μκ≤n)
    where
    n≤m : NatOrder._≤_ n m
    n≤m =
      NatOrder.<-weaken n<m

    diff : Σ[ k ∈ ℕ ]
      partialSum u m +ᶜ (-ᶜ partialSum u n) ≡ tailSum u n k
    diff =
      partialSum-diff-right-tail≤ u n m n≤m

    k : ℕ
    k =
      diff .fst

    diff-path :
      partialSum u m +ᶜ (-ᶜ partialSum u n) ≡ tailSum u n k
    diff-path =
      diff .snd


absoluteTerms :
  (ℕ → ℝᶜ) →
  ℕ →
  ℝᶜ
absoluteTerms u n =
  absᶜ (u n)


AbsolutelySummableWith :
  (ℕ → ℝᶜ) →
  (ℚ⁺ → ℕ) →
  Type₀
AbsolutelySummableWith u μ =
  TailBound (absoluteTerms u) μ


absoluteSummable→tailBound :
  {u : ℕ → ℝᶜ} {μ : ℚ⁺ → ℕ} →
  AbsolutelySummableWith u μ →
  TailBound u μ
absoluteSummable→tailBound {u = u} absTail ε m k μ≤m =
  bounded-byᶜ upperBound lowerBound
  where
  tail : ℝᶜ
  tail =
    tailSum u m k

  absTailSum : ℝᶜ
  absTailSum =
    partialSum (λ n → absᶜ (drop m u n)) k

  absTailBound : BoundedByᶜ ε (tailSum (absoluteTerms u) m k)
  absTailBound =
    absTail ε m k μ≤m

  absTailSum≤ε : absTailSum ≤ᶜ rational (radius ε)
  absTailSum≤ε =
    subst
      (λ x → x ≤ᶜ rational (radius ε))
      (tailSum-absoluteTerms u m k)
      (upperᶜ absTailBound)

  absTail≤absTailSum : absᶜ tail ≤ᶜ absTailSum
  absTail≤absTailSum =
    tailSum-abs-bound u m k

  absTail≤ε : absᶜ tail ≤ᶜ rational (radius ε)
  absTail≤ε =
    ≤ᶜ-trans
      {x = absᶜ tail}
      {y = absTailSum}
      {z = rational (radius ε)}
      absTail≤absTailSum
      absTailSum≤ε

  upperBound : tail ≤ᶜ rational (radius ε)
  upperBound =
    ≤ᶜ-trans
      {x = tail}
      {y = absᶜ tail}
      {z = rational (radius ε)}
      (≤ᶜabsᶜ-left tail)
      absTail≤ε

  lowerBound : (-ᶜ tail) ≤ᶜ rational (radius ε)
  lowerBound =
    ≤ᶜ-trans
      {x = -ᶜ tail}
      {y = absᶜ tail}
      {z = rational (radius ε)}
      (≤ᶜabsᶜ-right tail)
      absTail≤ε


nonnegative-upper→bounded-byᶜ :
  {ε : ℚ⁺} {x : ℝᶜ} →
  0ᶜ ≤ᶜ x →
  x ≤ᶜ rational (radius ε) →
  BoundedByᶜ ε x
nonnegative-upper→bounded-byᶜ {ε = ε} {x = x} 0≤x x≤ε =
  bounded-byᶜ x≤ε -x≤ε
  where
  -x≤0 : -ᶜ x ≤ᶜ 0ᶜ
  -x≤0 =
    subst
      (λ z → -ᶜ x ≤ᶜ z)
      neg-zeroᶜ
      (negᶜ-pres≤ᶜ {x = 0ᶜ} {y = x} 0≤x)

  0≤ε : 0ᶜ ≤ᶜ rational (radius ε)
  0≤ε =
    ≤ℚ→rational≤ᶜ
      {q = Rational.0ℚ}
      {r = radius ε}
      (ℚOrder.<Weaken≤ Rational.0ℚ (radius ε) (ε .snd))

  -x≤ε : -ᶜ x ≤ᶜ rational (radius ε)
  -x≤ε =
    ≤ᶜ-trans {x = -ᶜ x} {y = 0ᶜ} {z = rational (radius ε)} -x≤0 0≤ε


nonnegative-tail-upper→TailBound :
  {u : ℕ → ℝᶜ} {μ : ℚ⁺ → ℕ} →
  ((n : ℕ) → 0ᶜ ≤ᶜ u n) →
  ((ε : ℚ⁺) →
    (m k : ℕ) →
    NatOrder._≤_ (μ ε) m →
    tailSum u m k ≤ᶜ rational (radius ε)) →
  TailBound u μ
nonnegative-tail-upper→TailBound {u = u} 0≤u upper ε m k μ≤m =
  nonnegative-upper→bounded-byᶜ
    (tailSum-nonnegative u 0≤u m k)
    (upper ε m k μ≤m)


tailSum-ratio-half-upper :
  (u : ℕ → ℝᶜ) →
  ((n : ℕ) → 0ᶜ ≤ᶜ u n) →
  (N : ℕ) →
  ((n : ℕ) → NatOrder._≤_ N n → u (suc n) +ᶜ u (suc n) ≤ᶜ u n) →
  (m k : ℕ) →
  NatOrder._≤_ N m →
  tailSum u m k ≤ᶜ u m +ᶜ u m
tailSum-ratio-half-upper u 0≤u N ratio m zero N≤m =
  subst
    (λ x → x ≤ᶜ u m +ᶜ u m)
    (sym (tailSum-zero u m))
    doubled-nonnegative
  where
  doubled-nonnegative : 0ᶜ ≤ᶜ u m +ᶜ u m
  doubled-nonnegative =
    subst
      (λ x → x ≤ᶜ u m +ᶜ u m)
      (add-zero-left 0ᶜ)
      (≤ᶜ-add
        {a = 0ᶜ}
        {b = u m}
        {c = 0ᶜ}
        {d = u m}
        (0≤u m)
        (0≤u m))
tailSum-ratio-half-upper u 0≤u N ratio m (suc k) N≤m =
  subst
    (λ x → x ≤ᶜ u m +ᶜ u m)
    (sym (tailSum-suc-start u m k))
    (≤ᶜ-trans
      {x = u m +ᶜ tailSum u (suc m) k}
      {y = u m +ᶜ (u (suc m) +ᶜ u (suc m))}
      {z = u m +ᶜ u m}
      tail≤doubled-next
      ratio-step)
  where
  N≤sucm : NatOrder._≤_ N (suc m)
  N≤sucm =
    NatOrder.≤-trans N≤m (suc zero , refl)

  tail≤next-double :
    tailSum u (suc m) k ≤ᶜ u (suc m) +ᶜ u (suc m)
  tail≤next-double =
    tailSum-ratio-half-upper u 0≤u N ratio (suc m) k N≤sucm

  tail≤doubled-next :
    u m +ᶜ tailSum u (suc m) k ≤ᶜ
    u m +ᶜ (u (suc m) +ᶜ u (suc m))
  tail≤doubled-next =
    ≤ᶜ-add
      {a = u m}
      {b = u m}
      {c = tailSum u (suc m) k}
      {d = u (suc m) +ᶜ u (suc m)}
      (≤ᶜ-refl (u m))
      tail≤next-double

  ratio-step :
    u m +ᶜ (u (suc m) +ᶜ u (suc m)) ≤ᶜ u m +ᶜ u m
  ratio-step =
    ≤ᶜ-add
      {a = u m}
      {b = u m}
      {c = u (suc m) +ᶜ u (suc m)}
      {d = u m}
      (≤ᶜ-refl (u m))
      (ratio m N≤m)


eventual-ratio-half-tailBound :
  {u : ℕ → ℝᶜ} {μ : ℚ⁺ → ℕ} →
  ((n : ℕ) → 0ᶜ ≤ᶜ u n) →
  (N : ℕ) →
  ((n : ℕ) → NatOrder._≤_ N n → u (suc n) +ᶜ u (suc n) ≤ᶜ u n) →
  ((ε : ℚ⁺) → NatOrder._≤_ N (μ ε)) →
  ((ε : ℚ⁺) →
    (m : ℕ) →
    NatOrder._≤_ (μ ε) m →
    u m +ᶜ u m ≤ᶜ rational (radius ε)) →
  TailBound u μ
eventual-ratio-half-tailBound {u = u} {μ = μ}
    0≤u N ratio N≤μ doubled-upper =
  nonnegative-tail-upper→TailBound 0≤u upper
  where
  upper :
    (ε : ℚ⁺) →
    (m k : ℕ) →
    NatOrder._≤_ (μ ε) m →
    tailSum u m k ≤ᶜ rational (radius ε)
  upper ε m k μ≤m =
    ≤ᶜ-trans
      {x = tailSum u m k}
      {y = u m +ᶜ u m}
      {z = rational (radius ε)}
      (tailSum-ratio-half-upper
        u
        0≤u
        N
        ratio
        m
        k
        (NatOrder.≤-trans (N≤μ ε) μ≤m))
      (doubled-upper ε m μ≤m)


tailBound-add :
  {u v : ℕ → ℝᶜ} {μ : ℚ⁺ → ℕ} →
  TailBound u μ →
  TailBound v μ →
  TailBound (λ n → u n +ᶜ v n) (λ ε → μ (half⁺ ε))
tailBound-add {u = u} {v = v} u-tail v-tail ε m k μ≤m =
  subst2
    BoundedByᶜ
    (half⁺+half⁺≡ ε)
    (sym (tailSum-add u v m k))
    (bounded-byᶜ-add
      (half⁺ ε)
      (half⁺ ε)
      (tailSum u m k)
      (tailSum v m k)
      (u-tail (half⁺ ε) m k μ≤m)
      (v-tail (half⁺ ε) m k μ≤m))


tailBound-neg :
  {u : ℕ → ℝᶜ} {μ : ℚ⁺ → ℕ} →
  TailBound u μ →
  TailBound (λ n → -ᶜ u n) μ
tailBound-neg {u = u} u-tail ε m k μ≤m =
  subst
    (BoundedByᶜ ε)
    (sym (tailSum-neg u m k))
    (bounded-byᶜ-neg ε (tailSum u m k) (u-tail ε m k μ≤m))
