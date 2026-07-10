{-

Part of Constructive.Analysis.Reals.PowerSeries.CauchyProduct

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.CauchyProduct.MajorantRemainder where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_)
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.Completions.CauchyCompletion.Closeness
open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Metric
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Metric.Instances.Rationals
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.CommRing
  using (CauchyRealsCommRing)
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
    ; bounded-byᶜ-add
    ; bounded-byᶜ-close-zero
    ; merely-boundedᶜ
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
    ; comparisonTest
    ; diff-close-zero→close
    ; drop
    ; drop-index
    ; partialSum
    ; partialSum-add
    ; partialSum-diff-right-tail≤
    ; partialSum-suc
    ; partialSumSequence
    ; seriesSumFromFiniteTailBound
    ; seriesSumFromFiniteTailBoundConvergesTo
    ; seriesMajorizedByTerms
    ; nonnegative-upper→bounded-byᶜ
    ; tailSum
    ; tailSum-comparison
    ; tailSum-nonnegative
    ; tailSum-suc-start
    )
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower ; realPower-suc ; realPower-zero)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Radius
  using
    ( HasPowerSeriesOnBall
    ; HasPowerSeriesOnBallWith
    ; powerSeriesSumOnBall
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using
    ( PowerSeriesMajorizedOnBall
    ; majorizedOnBall→hasPowerSeriesOnBall
    ; majorizedOnBall→hasPowerSeriesOnBallWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( addPowerSeries
    ; constantPowerSeries
    ; negPowerSeries
    ; partialSum-mulLeft
    ; rationalScalePowerSeries
    ; shiftPowerSeries
    ; subPowerSeries
    ; zeroPowerSeries
    )
open import Constructive.Data.PositiveRationals
import Constructive.Data.Rationals as Rational

open ClosenessOf RationalsMetricSpace

import Constructive.Analysis.Reals.Sequences.Algebra as SeqAlg
import Constructive.Analysis.Reals.Sequences.Convergence as SeqConv
import Constructive.Analysis.Reals.Sequences.Order as SeqOrder
open import Constructive.Analysis.Modulus
  using
    ( AntitoneNatModulus
    ; maxModulus
    ; maxModulus-left≤
    ; maxModulus-right≤
    )

open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Internal
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Core
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Remainder
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Bounds

rectangularTriangularRemainderConvergesFromMajorantBound :
  {u v U V : ℕ → ℝᶜ} →
  SeriesMajorizedBy u U →
  SeriesMajorizedBy v V →
  (χ : ℚ⁺ → ℕ) →
  ((ε : ℚ⁺) →
    (n : ℕ) →
    NatOrder._≤_ (χ ε) n →
    BoundedByᶜ
      ε
      (rectangularTriangularRemainder U V n n)) →
  SeqConv.ConvergesWithModulus
    (λ n → rectangularTriangularRemainder u v n n)
    0ᶜ
    (λ ε → χ (half⁺ ε))
rectangularTriangularRemainderConvergesFromMajorantBound
    {u = u} {v = v} uMajorized vMajorized χ majorantBound =
  rectangularTriangularRemainderConvergesFromBound
    u
    v
    χ
    (λ ε n χ≤n →
      rectangularTriangularRemainderBoundFromMajorant
        uMajorized
        vMajorized
        ε
        n
        (majorantBound ε n χ≤n))


sequenceCauchyProductTailBoundFromMajorantRemainderBound :
  {u v U V : ℕ → ℝᶜ} →
  (ν τ χ β : ℚ⁺ → ℕ) →
  (κ ι : ℚ⁺) →
  (uTail : TailBound u ν) →
  (ν-antitone : AntitoneNatModulus ν) →
  (vTail : TailBound v τ) →
  (τ-antitone : AntitoneNatModulus τ) →
  (uMajorized : SeriesMajorizedBy u U) →
  (vMajorized : SeriesMajorizedBy v V) →
  (sumU-bound :
    BoundedByᶜ ι (seriesSumFromFiniteTailBound u ν uTail ν-antitone)) →
  (partialV-bound :
    SeqAlg.EventuallyBoundedByWith β κ (partialSumSequence v)) →
  (majorantRemainderBound :
    (ε : ℚ⁺) →
    (n : ℕ) →
    NatOrder._≤_ (χ ε) n →
    BoundedByᶜ ε (rectangularTriangularRemainder U V n n)) →
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
        (rectangularTriangularRemainderConvergesFromMajorantBound
          uMajorized
          vMajorized
          χ
          majorantRemainderBound)
        .fst
        (quarter⁺ ε))
sequenceCauchyProductTailBoundFromMajorantRemainderBound
  {u = u}
  {v = v}
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
  uMajorized
  vMajorized
  sumU-bound
  partialV-bound
  majorantRemainderBound =
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
    (λ ε n χ≤n →
      rectangularTriangularRemainderBoundFromMajorant
        uMajorized
        vMajorized
        ε
        n
        (majorantRemainderBound ε n χ≤n))


rectangularTriangularRemainderBoundFromProductTail :
  (U V : ℕ → ℝᶜ) →
  ((n : ℕ) → 0ᶜ ≤ᶜ U n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ V n) →
  ((n : ℕ) →
    rectangularTriangularRemainder U V n n ≤ᶜ
    tailSum (sequenceCauchyProduct U V) n n) →
  {μ : ℚ⁺ → ℕ} →
  TailBound (sequenceCauchyProduct U V) μ →
  (ε : ℚ⁺) →
  (n : ℕ) →
  NatOrder._≤_ (μ ε) n →
  BoundedByᶜ ε (rectangularTriangularRemainder U V n n)
rectangularTriangularRemainderBoundFromProductTail
    U V 0≤U 0≤V remainder≤tail productTail ε n μ≤n =
  nonnegative-upper→bounded-byᶜ
    (rectangularTriangularRemainder-nonnegative
      U
      V
      0≤U
      0≤V
      n
      n
      NatOrder.≤-refl)
    (≤ᶜ-trans
      {x = rectangularTriangularRemainder U V n n}
      {y = tailSum (sequenceCauchyProduct U V) n n}
      {z = rational (radius ε)}
      (remainder≤tail n)
      (upperᶜ (productTail ε n n μ≤n)))


tailSum-sequenceCauchyProduct-suc :
  (u v : ℕ → ℝᶜ) →
  (m q : ℕ) →
  tailSum (sequenceCauchyProduct u v) (suc m) q ≡
  u zero ·ᶜ tailSum v (suc m) q +ᶜ
  tailSum (sequenceCauchyProduct (λ k → u (suc k)) v) m q
tailSum-sequenceCauchyProduct-suc u v m zero =
  sym
    (cong
      (_+ᶜ 0ᶜ)
      (mulᶜ-zero-right (u zero)) ∙
    add-zero-left 0ᶜ)
tailSum-sequenceCauchyProduct-suc u v m (suc q) =
  tailSum-suc-start (sequenceCauchyProduct u v) (suc m) q ∙
  cong₂
    _+ᶜ_
    (sequenceCauchyProduct-suc u v m)
    (tailSum-sequenceCauchyProduct-suc u v (suc m) q) ∙
  SolverHelpers.tail-cauchy-product-decomposition-step
    CauchyRealsCommRing
    (u zero)
    (v (suc m))
    (tailSum v (suc (suc m)) q)
    (sequenceCauchyProduct (λ k → u (suc k)) v m)
    (tailSum
      (sequenceCauchyProduct (λ k → u (suc k)) v)
      (suc m)
      q) ∙
  cong₂
    _+ᶜ_
    (cong
      (u zero ·ᶜ_)
      (sym (tailSum-suc-start v (suc m) q)))
    (sym
      (tailSum-suc-start
        (sequenceCauchyProduct (λ k → u (suc k)) v)
        m
        q))


sequenceCauchyProduct-nonnegative :
  (u v : ℕ → ℝᶜ) →
  ((n : ℕ) → 0ᶜ ≤ᶜ u n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ v n) →
  (n : ℕ) →
  0ᶜ ≤ᶜ sequenceCauchyProduct u v n
sequenceCauchyProduct-nonnegative u v 0≤u 0≤v zero =
  mulᶜ-nonnegative (u zero) (v zero) (0≤u zero) (0≤v zero)
sequenceCauchyProduct-nonnegative u v 0≤u 0≤v (suc n) =
  nonnegativeᶜ-add
    {x = u zero ·ᶜ v (suc n)}
    {y = sequenceCauchyProduct (λ k → u (suc k)) v n}
    (mulᶜ-nonnegative
      (u zero)
      (v (suc n))
      (0≤u zero)
      (0≤v (suc n)))
    (sequenceCauchyProduct-nonnegative
      (λ k → u (suc k))
      v
      (λ k → 0≤u (suc k))
      0≤v
      n)


tailSum-sequenceCauchyProduct-shift≤ :
  (u v : ℕ → ℝᶜ) →
  ((n : ℕ) → 0ᶜ ≤ᶜ u n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ v n) →
  (m q : ℕ) →
  tailSum (sequenceCauchyProduct (λ k → u (suc k)) v) m q ≤ᶜ
  tailSum (sequenceCauchyProduct u v) (suc m) q
tailSum-sequenceCauchyProduct-shift≤ u v 0≤u 0≤v m q =
  subst
    (λ z → shiftTail ≤ᶜ z)
    (sym (tailSum-sequenceCauchyProduct-suc u v m q))
    shiftTail≤decomposed
  where
  headTail : ℝᶜ
  headTail =
    u zero ·ᶜ tailSum v (suc m) q

  shiftTail : ℝᶜ
  shiftTail =
    tailSum (sequenceCauchyProduct (λ k → u (suc k)) v) m q

  headTail-nonnegative :
    0ᶜ ≤ᶜ headTail
  headTail-nonnegative =
    mulᶜ-nonnegative
      (u zero)
      (tailSum v (suc m) q)
      (0≤u zero)
      (tailSum-nonnegative v 0≤v (suc m) q)

  shiftTail≤shiftPlusHead :
    shiftTail ≤ᶜ shiftTail +ᶜ headTail
  shiftTail≤shiftPlusHead =
    add-nonnegative-right≤ headTail-nonnegative

  shiftTail≤decomposed :
    shiftTail ≤ᶜ headTail +ᶜ shiftTail
  shiftTail≤decomposed =
    subst
      (λ z → shiftTail ≤ᶜ z)
      (add-comm shiftTail headTail)
      shiftTail≤shiftPlusHead


rectangularTriangularRemainder≤cauchyProductTail :
  (U V : ℕ → ℝᶜ) →
  ((n : ℕ) → 0ᶜ ≤ᶜ U n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ V n) →
  (m q : ℕ) →
  NatOrder._≤_ m q →
  rectangularTriangularRemainder U V m q ≤ᶜ
  tailSum (sequenceCauchyProduct U V) m q
rectangularTriangularRemainder≤cauchyProductTail U V 0≤U 0≤V zero q _ =
  tailSum-nonnegative
    (sequenceCauchyProduct U V)
    (sequenceCauchyProduct-nonnegative U V 0≤U 0≤V)
    zero
    q
rectangularTriangularRemainder≤cauchyProductTail U V 0≤U 0≤V
    (suc m) q sucm≤q =
  subst
    (λ z →
      rectangularTriangularRemainder U V (suc m) q ≤ᶜ z)
    (sym (tailSum-sequenceCauchyProduct-suc U V m q))
    remainder≤decomposedTail
  where
  difference : ℝᶜ
  difference =
    partialSum V q +ᶜ (-ᶜ partialSum V (suc m))

  fullTail : ℝᶜ
  fullTail =
    tailSum V (suc m) q

  headRemainder : ℝᶜ
  headRemainder =
    U zero ·ᶜ difference

  headTail : ℝᶜ
  headTail =
    U zero ·ᶜ fullTail

  tailRemainder : ℝᶜ
  tailRemainder =
    rectangularTriangularRemainder (λ k → U (suc k)) V m q

  shiftTail : ℝᶜ
  shiftTail =
    tailSum (sequenceCauchyProduct (λ k → U (suc k)) V) m q

  m≤q : NatOrder._≤_ m q
  m≤q =
    NatOrder.≤-trans (n≤sucn m) sucm≤q

  difference≤fullTail :
    difference ≤ᶜ fullTail
  difference≤fullTail =
    partialSum-difference≤tailSum V 0≤V (suc m) q sucm≤q

  head≤ :
    headRemainder ≤ᶜ headTail
  head≤ =
    subst2
      _≤ᶜ_
      (mulᶜ-comm difference (U zero))
      (mulᶜ-comm fullTail (U zero))
      (mulᶜ-pres≤ᶜ-right
        difference
        fullTail
        (U zero)
        (0≤U zero)
        difference≤fullTail)

  tail≤ :
    tailRemainder ≤ᶜ shiftTail
  tail≤ =
    rectangularTriangularRemainder≤cauchyProductTail
      (λ k → U (suc k))
      V
      (λ k → 0≤U (suc k))
      0≤V
      m
      q
      m≤q

  remainder≤decomposedTail :
    rectangularTriangularRemainder U V (suc m) q ≤ᶜ
    headTail +ᶜ shiftTail
  remainder≤decomposedTail =
    ≤ᶜ-add
      {a = headRemainder}
      {b = headTail}
      {c = tailRemainder}
      {d = shiftTail}
      head≤
      tail≤


sequenceCauchyProduct-termMajorized :
  (u v U V : ℕ → ℝᶜ) →
  ((n : ℕ) → absᶜ (u n) ≤ᶜ U n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ U n) →
  ((n : ℕ) → absᶜ (v n) ≤ᶜ V n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ V n) →
  (n : ℕ) →
  absᶜ (sequenceCauchyProduct u v n) ≤ᶜ
  sequenceCauchyProduct U V n
sequenceCauchyProduct-termMajorized u v U V u≤U 0≤U v≤V 0≤V zero =
  absᶜ-mul≤product
    (u zero)
    (v zero)
    (U zero)
    (V zero)
    (0≤U zero)
    (0≤V zero)
    (u≤U zero)
    (v≤V zero)
sequenceCauchyProduct-termMajorized u v U V u≤U 0≤U v≤V 0≤V (suc n) =
  ≤ᶜ-trans
    {x = absᶜ
      (u zero ·ᶜ v (suc n) +ᶜ
       sequenceCauchyProduct (λ k → u (suc k)) v n)}
    {y =
      absᶜ (u zero ·ᶜ v (suc n)) +ᶜ
      absᶜ (sequenceCauchyProduct (λ k → u (suc k)) v n)}
    {z =
      U zero ·ᶜ V (suc n) +ᶜ
      sequenceCauchyProduct (λ k → U (suc k)) V n}
    (absᶜ-triangle
      (u zero ·ᶜ v (suc n))
      (sequenceCauchyProduct (λ k → u (suc k)) v n))
    (≤ᶜ-add
      {a = absᶜ (u zero ·ᶜ v (suc n))}
      {b = U zero ·ᶜ V (suc n)}
      {c = absᶜ (sequenceCauchyProduct (λ k → u (suc k)) v n)}
      {d = sequenceCauchyProduct (λ k → U (suc k)) V n}
      (absᶜ-mul≤product
        (u zero)
        (v (suc n))
        (U zero)
        (V (suc n))
        (0≤U zero)
        (0≤V (suc n))
        (u≤U zero)
        (v≤V (suc n)))
      (sequenceCauchyProduct-termMajorized
        (λ k → u (suc k))
        v
        (λ k → U (suc k))
        V
        (λ k → u≤U (suc k))
        (λ k → 0≤U (suc k))
        v≤V
        0≤V
        n))


sequenceCauchyProductMajorizedByTerms :
  {u v U V : ℕ → ℝᶜ} →
  ((n : ℕ) → absᶜ (u n) ≤ᶜ U n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ U n) →
  ((n : ℕ) → absᶜ (v n) ≤ᶜ V n) →
  ((n : ℕ) → 0ᶜ ≤ᶜ V n) →
  SeriesMajorizedBy
    (sequenceCauchyProduct u v)
    (sequenceCauchyProduct U V)
sequenceCauchyProductMajorizedByTerms {u = u} {v = v} {U = U} {V = V}
  u≤U
  0≤U
  v≤V
  0≤V =
  seriesMajorizedByTerms
    (sequenceCauchyProduct-termMajorized u v U V u≤U 0≤U v≤V 0≤V)
    (sequenceCauchyProduct-nonnegative U V 0≤U 0≤V)


sequenceCauchyProductMajorizedBy :
  {u v U V : ℕ → ℝᶜ} →
  SeriesMajorizedBy u U →
  SeriesMajorizedBy v V →
  SeriesMajorizedBy
    (sequenceCauchyProduct u v)
    (sequenceCauchyProduct U V)
sequenceCauchyProductMajorizedBy u-majorized v-majorized =
  sequenceCauchyProductMajorizedByTerms
    (λ n → SeriesMajorizedBy.termMajorized u-majorized zero n)
    (λ n → SeriesMajorizedBy.majorantNonnegative u-majorized zero n)
    (λ n → SeriesMajorizedBy.termMajorized v-majorized zero n)
    (λ n → SeriesMajorizedBy.majorantNonnegative v-majorized zero n)


sequenceCauchyProductTailBoundFromMajorant :
  {u v U V : ℕ → ℝᶜ} →
  {μ : ℚ⁺ → ℕ} →
  SeriesMajorizedBy u U →
  SeriesMajorizedBy v V →
  TailBound (sequenceCauchyProduct U V) μ →
  TailBound (sequenceCauchyProduct u v) μ
sequenceCauchyProductTailBoundFromMajorant u-majorized v-majorized =
  comparisonTest
    (sequenceCauchyProductMajorizedBy u-majorized v-majorized)
