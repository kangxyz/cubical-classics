{- Bounds for finite rectangular-to-triangular Cauchy-product remainders. -}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Series.CauchyProduct.RemainderBounds where

open import Cubical.Foundations.Prelude

import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Metric
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Quantitative
  using (absᶜ-mul≤product ; mulᶜ-nonnegative)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using
    ( mulᶜ≤abs-product
    ; mulᶜ-pres≤ᶜ-right
    ; neg-mulᶜ≤abs-product
    )
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_ ; ≤ᶜ-refl ; ≤ᶜ-trans)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  using
    ( BoundedByᶜ
    ; bounded-byᶜ
    ; upperᶜ
    )
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  using (close-rational-upper-bound)
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using
    ( absᶜ
    ; absᶜ-least
    ; absᶜ-nonnegative
    ; absᶜ-triangle
    ; absᶜ-zero
    ; nonnegativeᶜ-add
    ; ≤ᶜabsᶜ-left
    ; ≤ᶜabsᶜ-right
    )
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
  using (diffᶜ-nonnegative→≤ᶜ ; ≤ᶜ-add)
open import Constructive.Analysis.Reals.Series.Finite
  using (partialSum)
open import Constructive.Analysis.Reals.Series.Tail
  using
    ( shift
    ; shift-index
    ; partialSum-diff-right-tail≤
    ; tailSum
    ; tailSum-nonnegative
    )
open import Constructive.Analysis.Reals.Series.Comparison
  using
    ( SeriesMajorizedBy
    ; seriesMajorizedByTerms
    ; tailSum-comparison
    )
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open ClosenessOf RationalsMetricSpace

import Constructive.Analysis.Reals.Sequences.Algebra as SeqAlg
import Constructive.Analysis.Reals.Sequences.Convergence as SeqConv
open import Constructive.Analysis.Modulus
  using
    ( AntitoneNatModulus
    ; maxModulus
    ; maxModulus-left≤
    ; maxModulus-right≤
    )

open import Constructive.Analysis.Reals.Series.CauchyProduct.Finite

tailSum-length-monotone :
  (u : ℕ → ℝᶜ) →
  ((n : ℕ) → 0ᶜ ≤ᶜ u n) →
  (m k q : ℕ) →
  NatOrder._≤_ k q →
  tailSum u m k ≤ᶜ tailSum u m q
tailSum-length-monotone u 0≤u m k q k≤q =
  diffᶜ-nonnegative→≤ᶜ
    (subst
      (λ x → 0ᶜ ≤ᶜ x)
      (sym diffPath)
      tailNonnegative)
  where
  diff =
    partialSum-diff-right-tail≤ (shift m u) k q k≤q

  d : ℕ
  d =
    diff .fst

  diffPath :
    tailSum u m q +ᶜ (-ᶜ tailSum u m k) ≡
    tailSum (shift m u) k d
  diffPath =
    diff .snd

  shiftNonnegative :
    (n : ℕ) → 0ᶜ ≤ᶜ shift m u n
  shiftNonnegative n =
    subst
      (λ x → 0ᶜ ≤ᶜ x)
      (sym (shift-index m u n))
      (0≤u (m Nat.+ n))

  tailNonnegative :
    0ᶜ ≤ᶜ tailSum (shift m u) k d
  tailNonnegative =
    tailSum-nonnegative (shift m u) shiftNonnegative k d


partialSum-difference≤tailSum :
  (u : ℕ → ℝᶜ) →
  ((n : ℕ) → 0ᶜ ≤ᶜ u n) →
  (m q : ℕ) →
  NatOrder._≤_ m q →
  partialSum u q +ᶜ (-ᶜ partialSum u m) ≤ᶜ
  tailSum u m q
partialSum-difference≤tailSum u 0≤u m q (k , k+m≡q) =
  subst
    (λ x → x ≤ᶜ tailSum u m q)
    (sym diffPath)
    (tailSum-length-monotone u 0≤u m k q k≤q)
  where
  diff =
    partialSum-diff-right-tail≤ u m q (k , k+m≡q)

  diffPath :
    partialSum u q +ᶜ (-ᶜ partialSum u m) ≡ tailSum u m k
  diffPath =
    diff .snd

  k≤q : NatOrder._≤_ k q
  k≤q =
    m , Nat.+-comm m k ∙ k+m≡q


partialSum-differenceMajorizedBy :
  (v V : ℕ → ℝᶜ) →
  SeriesMajorizedBy v V →
  (m q : ℕ) →
  NatOrder._≤_ m q →
  absᶜ (partialSum v q +ᶜ (-ᶜ partialSum v m)) ≤ᶜ
  partialSum V q +ᶜ (-ᶜ partialSum V m)
partialSum-differenceMajorizedBy v V majorized m q m≤q =
  subst2
    (λ x y → absᶜ x ≤ᶜ y)
    (sym vTailPath)
    (sym VTailPath)
    (tailSum-comparison majorized m k)
  where
  vDiff =
    partialSum-diff-right-tail≤ v m q m≤q

  VDiff =
    partialSum-diff-right-tail≤ V m q m≤q

  k : ℕ
  k =
    vDiff .fst

  vTailPath :
    partialSum v q +ᶜ (-ᶜ partialSum v m) ≡ _
  vTailPath =
    vDiff .snd

  VTailPath :
    partialSum V q +ᶜ (-ᶜ partialSum V m) ≡ _
  VTailPath =
    VDiff .snd


partialSum-differenceMajorant-nonnegative :
  (V : ℕ → ℝᶜ) →
  ((n : ℕ) → 0ᶜ ≤ᶜ V n) →
  (m q : ℕ) →
  NatOrder._≤_ m q →
  0ᶜ ≤ᶜ partialSum V q +ᶜ (-ᶜ partialSum V m)
partialSum-differenceMajorant-nonnegative V 0≤V m q m≤q =
  subst
    (λ x → 0ᶜ ≤ᶜ x)
    (sym VTailPath)
    (tailSum-nonnegative V 0≤V m k)
  where
  VDiff =
    partialSum-diff-right-tail≤ V m q m≤q

  k : ℕ
  k =
    VDiff .fst

  VTailPath :
    partialSum V q +ᶜ (-ᶜ partialSum V m) ≡ _
  VTailPath =
    VDiff .snd


rectangularTriangularRemainder-nonnegative :
  (U V : ℕ → ℝᶜ) →
  ((n : ℕ) → 0ᶜ ≤ᶜ U n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ V n) →
  (m q : ℕ) →
  NatOrder._≤_ m q →
  0ᶜ ≤ᶜ rectangularTriangularRemainder U V m q
rectangularTriangularRemainder-nonnegative U V 0≤U 0≤V zero q m≤q =
  ≤ᶜ-refl 0ᶜ
rectangularTriangularRemainder-nonnegative U V 0≤U 0≤V (suc m) q sucm≤q =
  nonnegativeᶜ-add
    {x = U zero ·ᶜ difference}
    {y = rectangularTriangularRemainder (λ k → U (suc k)) V m q}
    (mulᶜ-nonnegative
      (U zero)
      difference
      (0≤U zero)
      difference-nonnegative)
    (rectangularTriangularRemainder-nonnegative
      (λ k → U (suc k))
      V
      (λ k → 0≤U (suc k))
      0≤V
      m
      q
      m≤q)
  where
  difference : ℝᶜ
  difference =
    partialSum V q +ᶜ (-ᶜ partialSum V (suc m))

  m≤q : NatOrder._≤_ m q
  m≤q =
    NatOrder.≤-trans NatOrder.≤-sucℕ sucm≤q

  difference-nonnegative :
    0ᶜ ≤ᶜ difference
  difference-nonnegative =
    partialSum-differenceMajorant-nonnegative V 0≤V (suc m) q sucm≤q


rectangularTriangularRemainder-termMajorized :
  (u v U V : ℕ → ℝᶜ) →
  (uMajorized : SeriesMajorizedBy u U) →
  (vMajorized : SeriesMajorizedBy v V) →
  (m q : ℕ) →
  NatOrder._≤_ m q →
  absᶜ (rectangularTriangularRemainder u v m q) ≤ᶜ
  rectangularTriangularRemainder U V m q
rectangularTriangularRemainder-termMajorized u v U V uMajorized vMajorized
    zero q m≤q =
  subst
    (λ x → x ≤ᶜ 0ᶜ)
    (sym absᶜ-zero)
    (≤ᶜ-refl 0ᶜ)
rectangularTriangularRemainder-termMajorized u v U V uMajorized vMajorized
    (suc m) q sucm≤q =
  ≤ᶜ-trans
    {x = absᶜ (u zero ·ᶜ vDifference +ᶜ tailRemainder)}
    {y = absᶜ (u zero ·ᶜ vDifference) +ᶜ absᶜ tailRemainder}
    {z = U zero ·ᶜ VDifference +ᶜ majorantTailRemainder}
    (absᶜ-triangle (u zero ·ᶜ vDifference) tailRemainder)
    (≤ᶜ-add
      {a = absᶜ (u zero ·ᶜ vDifference)}
      {b = U zero ·ᶜ VDifference}
      {c = absᶜ tailRemainder}
      {d = majorantTailRemainder}
      head≤
      tail≤)
  where
  vDifference : ℝᶜ
  vDifference =
    partialSum v q +ᶜ (-ᶜ partialSum v (suc m))

  VDifference : ℝᶜ
  VDifference =
    partialSum V q +ᶜ (-ᶜ partialSum V (suc m))

  tailRemainder : ℝᶜ
  tailRemainder =
    rectangularTriangularRemainder (λ k → u (suc k)) v m q

  majorantTailRemainder : ℝᶜ
  majorantTailRemainder =
    rectangularTriangularRemainder (λ k → U (suc k)) V m q

  V-nonnegative :
    (n : ℕ) → 0ᶜ ≤ᶜ V n
  V-nonnegative n =
    SeriesMajorizedBy.majorantNonnegative vMajorized zero n

  U0-nonnegative :
    0ᶜ ≤ᶜ U zero
  U0-nonnegative =
    SeriesMajorizedBy.majorantNonnegative uMajorized zero zero

  VDifference-nonnegative :
    0ᶜ ≤ᶜ VDifference
  VDifference-nonnegative =
    partialSum-differenceMajorant-nonnegative
      V
      V-nonnegative
      (suc m)
      q
      sucm≤q

  u0≤U0 :
    absᶜ (u zero) ≤ᶜ U zero
  u0≤U0 =
    SeriesMajorizedBy.termMajorized uMajorized zero zero

  vDifference≤VDifference :
    absᶜ vDifference ≤ᶜ VDifference
  vDifference≤VDifference =
    partialSum-differenceMajorizedBy
      v
      V
      vMajorized
      (suc m)
      q
      sucm≤q

  head≤ :
    absᶜ (u zero ·ᶜ vDifference) ≤ᶜ U zero ·ᶜ VDifference
  head≤ =
    absᶜ-mul≤product
      (u zero)
      vDifference
      (U zero)
      VDifference
      U0-nonnegative
      VDifference-nonnegative
      u0≤U0
      vDifference≤VDifference

  shiftedUMajorized :
    SeriesMajorizedBy (λ k → u (suc k)) (λ k → U (suc k))
  shiftedUMajorized =
    seriesMajorizedByTerms
      (λ n → SeriesMajorizedBy.termMajorized uMajorized zero (suc n))
      (λ n → SeriesMajorizedBy.majorantNonnegative uMajorized zero (suc n))

  m≤q : NatOrder._≤_ m q
  m≤q =
    NatOrder.≤-trans NatOrder.≤-sucℕ sucm≤q

  tail≤ :
    absᶜ tailRemainder ≤ᶜ majorantTailRemainder
  tail≤ =
    rectangularTriangularRemainder-termMajorized
      (λ k → u (suc k))
      v
      (λ k → U (suc k))
      V
      shiftedUMajorized
      vMajorized
      m
      q
      m≤q


rectangularTriangularRemainderBoundFromMajorant :
  {u v U V : ℕ → ℝᶜ} →
  (uMajorized : SeriesMajorizedBy u U) →
  (vMajorized : SeriesMajorizedBy v V) →
  (ε : ℚ⁺) →
  (n : ℕ) →
  BoundedByᶜ
    ε
    (rectangularTriangularRemainder U V n n) →
  BoundedByᶜ
    ε
    (rectangularTriangularRemainder u v n n)
rectangularTriangularRemainderBoundFromMajorant {u = u} {v = v} {U = U} {V = V}
    uMajorized vMajorized ε n majorantBound =
  bounded-byᶜ
    (≤ᶜ-trans
      {x = actualRemainder}
      {y = absᶜ actualRemainder}
      {z = rational (radius ε)}
      (≤ᶜabsᶜ-left actualRemainder)
      absActual≤ε)
    (≤ᶜ-trans
      {x = -ᶜ actualRemainder}
      {y = absᶜ actualRemainder}
      {z = rational (radius ε)}
      (≤ᶜabsᶜ-right actualRemainder)
      absActual≤ε)
  where
  actualRemainder : ℝᶜ
  actualRemainder =
    rectangularTriangularRemainder u v n n

  majorantRemainder : ℝᶜ
  majorantRemainder =
    rectangularTriangularRemainder U V n n

  absActual≤majorant :
    absᶜ actualRemainder ≤ᶜ majorantRemainder
  absActual≤majorant =
    rectangularTriangularRemainder-termMajorized
      u
      v
      U
      V
      uMajorized
      vMajorized
      n
      n
      NatOrder.≤-refl

  absActual≤ε :
    absᶜ actualRemainder ≤ᶜ rational (radius ε)
  absActual≤ε =
    ≤ᶜ-trans
      {x = absᶜ actualRemainder}
      {y = majorantRemainder}
      {z = rational (radius ε)}
      absActual≤majorant
      (upperᶜ majorantBound)
