{-

Part of Constructive.Analysis.Reals.PowerSeries.CauchyProduct

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Bounds where

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
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.OrderedCommRing
  using
    ( mulᶜ≤abs-product
    ; mulᶜ-pres≤ᶜ-right
    ; neg-mulᶜ≤abs-product
    )
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_ ; ≤ᶜ-refl ; ≤ᶜ-trans)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounded
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
open import Constructive.Analysis.Reals.Series
  using
    ( SeriesMajorizedBy
    ; TailBound
    ; drop
    ; drop-index
    ; partialSum
    ; partialSum-diff-right-tail≤
    ; partialSumSequence
    ; seriesSumFromFiniteTailBound
    ; seriesMajorizedByTerms
    ; tailSum
    ; tailSum-comparison
    ; tailSum-nonnegative
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

open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Core
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Remainder

mulᶜ-nonnegative :
  (x y : ℝᶜ) →
  0ᶜ ≤ᶜ x →
  0ᶜ ≤ᶜ y →
  0ᶜ ≤ᶜ x ·ᶜ y
mulᶜ-nonnegative x y 0≤x 0≤y =
  subst
    (λ z → z ≤ᶜ x ·ᶜ y)
    (mulᶜ-zero-left y)
    (mulᶜ-pres≤ᶜ-right 0ᶜ x y 0≤y 0≤x)


absᶜ-mul≤product :
  (x y X Y : ℝᶜ) →
  0ᶜ ≤ᶜ X →
  0ᶜ ≤ᶜ Y →
  absᶜ x ≤ᶜ X →
  absᶜ y ≤ᶜ Y →
  absᶜ (x ·ᶜ y) ≤ᶜ X ·ᶜ Y
absᶜ-mul≤product x y X Y 0≤X 0≤Y absx≤X absy≤Y =
  absᶜ-least
    (x ·ᶜ y)
    (X ·ᶜ Y)
    (mulᶜ-nonnegative X Y 0≤X 0≤Y)
    (≤ᶜ-trans
      {x = x ·ᶜ y}
      {y = absᶜ x ·ᶜ absᶜ y}
      {z = X ·ᶜ Y}
      (mulᶜ≤abs-product x y)
      absProduct≤majorantProduct)
    (≤ᶜ-trans
      {x = -ᶜ (x ·ᶜ y)}
      {y = absᶜ x ·ᶜ absᶜ y}
      {z = X ·ᶜ Y}
      (neg-mulᶜ≤abs-product x y)
      absProduct≤majorantProduct)
  where
  absProduct≤majorantProduct :
    absᶜ x ·ᶜ absᶜ y ≤ᶜ X ·ᶜ Y
  absProduct≤majorantProduct =
    ≤ᶜ-trans
      {x = absᶜ x ·ᶜ absᶜ y}
      {y = X ·ᶜ absᶜ y}
      {z = X ·ᶜ Y}
      (mulᶜ-pres≤ᶜ-right
        (absᶜ x)
        X
        (absᶜ y)
        (absᶜ-nonnegative y)
        absx≤X)
      (subst2
        _≤ᶜ_
        (mulᶜ-comm (absᶜ y) X)
        (mulᶜ-comm Y X)
        (mulᶜ-pres≤ᶜ-right
          (absᶜ y)
          Y
          X
          0≤X
          absy≤Y))


n≤sucn : (n : ℕ) → NatOrder._≤_ n (suc n)
n≤sucn n =
  suc zero , refl


add-nonnegative-right≤ :
  {x y : ℝᶜ} →
  0ᶜ ≤ᶜ y →
  x ≤ᶜ x +ᶜ y
add-nonnegative-right≤ {x = x} {y = y} 0≤y =
  subst
    (λ z → z ≤ᶜ x +ᶜ y)
    (add-zero-right x)
    (≤ᶜ-add
      {a = x}
      {b = x}
      {c = 0ᶜ}
      {d = y}
      (≤ᶜ-refl x)
      0≤y)


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
        (ℚ.- Rational.0ℚ)
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


tailBoundFromConvergesWithModulus :
  (u : ℕ → ℝᶜ) →
  (x : ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  SeqConv.ConvergesWithModulus (partialSumSequence u) x μ →
  TailBound u (λ ε → μ (quarter⁺ ε))
tailBoundFromConvergesWithModulus u x μ converges ε m k μ≤m =
  subst
    (BoundedByᶜ ε)
    diffPath
    diff-bound
  where
  α : ℚ⁺
  α =
    quarter⁺ ε

  n : ℕ
  n =
    m Nat.+ k

  m≤n : NatOrder._≤_ m n
  m≤n =
    k , Nat.+-comm k m

  μ≤n : NatOrder._≤_ (μ α) n
  μ≤n =
    NatOrder.≤-trans μ≤m m≤n

  partialN∼x :
    partialSum u n ∼[ α ] x
  partialN∼x =
    converges α n μ≤n

  partialM∼x :
    partialSum u m ∼[ α ] x
  partialM∼x =
    converges α m μ≤m

  partialN∼partialM :
    partialSum u n ∼[ half⁺ ε ] partialSum u m
  partialN∼partialM =
    subst
      (λ ρ → partialSum u n ∼[ ρ ] partialSum u m)
      (ℚ⁺Path (quarter-sum≡half ε))
      (MetricSpace.close-triangle
        CauchyRealsMetricSpace
        partialN∼x
        (MetricSpace.close-sym CauchyRealsMetricSpace partialM∼x))

  diff : ℝᶜ
  diff =
    partialSum u n +ᶜ (-ᶜ partialSum u m)

  tailDiff =
    partialSum-diff-right-tail≤ u m n m≤n

  diffPath :
    diff ≡ tailSum u m k
  diffPath =
    tailDiff .snd

  diff-bound :
    BoundedByᶜ ε diff
  diff-bound =
    close→difference-bounded-byᶜ
      (partialSum u n)
      (partialSum u m)
      (half< ε)
      partialN∼partialM


sequenceCauchyProductTailBoundFromRemainderConvergence :
  (u v : ℕ → ℝᶜ) →
  (ν τ χ β : ℚ⁺ → ℕ) →
  (κ ι : ℚ⁺) →
  (uTail : TailBound u ν) →
  (ν-antitone : AntitoneNatModulus ν) →
  (vTail : TailBound v τ) →
  (τ-antitone : AntitoneNatModulus τ) →
  (sumU-bound :
    BoundedByᶜ ι (seriesSumFromFiniteTailBound u ν uTail ν-antitone)) →
  (partialV-bound :
    SeqAlg.EventuallyBoundedByWith β κ (partialSumSequence v)) →
  (remainder→0 :
    SeqConv.ConvergesWithModulus
      (λ n → rectangularTriangularRemainder u v n n)
      0ᶜ
      χ) →
  TailBound
    (sequenceCauchyProduct u v)
    (λ ε →
      sequenceCauchyProductPartialSumsConvergeToProductFromRemainderConvergence
        u
        v
        ν
        τ
        χ
        β
        κ
        ι
        uTail
        ν-antitone
        vTail
        τ-antitone
        sumU-bound
        partialV-bound
        remainder→0
        .fst
        (quarter⁺ ε))
sequenceCauchyProductTailBoundFromRemainderConvergence
  u
  v
  ν
  τ
  χ
  β
  κ
  ι
  uTail
  ν-antitone
  vTail
  τ-antitone
  sumU-bound
  partialV-bound
  remainder→0 =
  tailBoundFromConvergesWithModulus
    (sequenceCauchyProduct u v)
    productLimit
    (productConverges .fst)
    (productConverges .snd)
  where
  productLimit : ℝᶜ
  productLimit =
    seriesSumFromFiniteTailBound u ν uTail ν-antitone ·ᶜ
    seriesSumFromFiniteTailBound v τ vTail τ-antitone

  productConverges :
    SeqConv.ConvergesTo
      (partialSumSequence (sequenceCauchyProduct u v))
      productLimit
  productConverges =
    sequenceCauchyProductPartialSumsConvergeToProductFromRemainderConvergence
      u
      v
      ν
      τ
      χ
      β
      κ
      ι
      uTail
      ν-antitone
      vTail
      τ-antitone
      sumU-bound
      partialV-bound
      remainder→0


sequenceCauchyProductTailBoundFromRemainderBound :
  (u v : ℕ → ℝᶜ) →
  (ν τ χ β : ℚ⁺ → ℕ) →
  (κ ι : ℚ⁺) →
  (uTail : TailBound u ν) →
  (ν-antitone : AntitoneNatModulus ν) →
  (vTail : TailBound v τ) →
  (τ-antitone : AntitoneNatModulus τ) →
  (sumU-bound :
    BoundedByᶜ ι (seriesSumFromFiniteTailBound u ν uTail ν-antitone)) →
  (partialV-bound :
    SeqAlg.EventuallyBoundedByWith β κ (partialSumSequence v)) →
  (remainderBound :
    (ε : ℚ⁺) →
    (n : ℕ) →
    NatOrder._≤_ (χ ε) n →
    BoundedByᶜ ε (rectangularTriangularRemainder u v n n)) →
  TailBound
    (sequenceCauchyProduct u v)
    (λ ε →
      sequenceCauchyProductPartialSumsConvergeToProductFromRemainderConvergence
        u
        v
        ν
        τ
        (λ ε → χ (half⁺ ε))
        β
        κ
        ι
        uTail
        ν-antitone
        vTail
        τ-antitone
        sumU-bound
        partialV-bound
        (rectangularTriangularRemainderConvergesFromBound u v χ remainderBound)
        .fst
        (quarter⁺ ε))
sequenceCauchyProductTailBoundFromRemainderBound
  u
  v
  ν
  τ
  χ
  β
  κ
  ι
  uTail
  ν-antitone
  vTail
  τ-antitone
  sumU-bound
  partialV-bound
  remainderBound =
  sequenceCauchyProductTailBoundFromRemainderConvergence
    u
    v
    ν
    τ
    (λ ε → χ (half⁺ ε))
    β
    κ
    ι
    uTail
    ν-antitone
    vTail
    τ-antitone
    sumU-bound
    partialV-bound
    (rectangularTriangularRemainderConvergesFromBound u v χ remainderBound)


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
    partialSum-diff-right-tail≤ (drop m u) k q k≤q

  d : ℕ
  d =
    diff .fst

  diffPath :
    tailSum u m q +ᶜ (-ᶜ tailSum u m k) ≡
    tailSum (drop m u) k d
  diffPath =
    diff .snd

  dropNonnegative :
    (n : ℕ) → 0ᶜ ≤ᶜ drop m u n
  dropNonnegative n =
    subst
      (λ x → 0ᶜ ≤ᶜ x)
      (sym (drop-index m u n))
      (0≤u (m Nat.+ n))

  tailNonnegative :
    0ᶜ ≤ᶜ tailSum (drop m u) k d
  tailNonnegative =
    tailSum-nonnegative (drop m u) dropNonnegative k d


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
    NatOrder.≤-trans (n≤sucn m) sucm≤q

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
    NatOrder.≤-trans (n≤sucn m) sucm≤q

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
