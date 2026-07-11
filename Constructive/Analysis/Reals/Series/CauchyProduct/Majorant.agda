{- Majorants and tail bounds for Cauchy products. -}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Series.CauchyProduct.Majorant where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Tactics.CommRingSolver.Reflection
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.AdditiveGroup
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Structures
  using (CauchyRealsCommRing)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Quantitative
  using (absᶜ-mul≤product ; mulᶜ-nonnegative)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Ordered
  using
    ( mulᶜ≤abs-product
    ; mulᶜ-pres≤ᶜ-right
    )
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Base
  using (_≤ᶜ_ ; ≤ᶜ-trans)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  using
    ( BoundedByᶜ
    ; bounded-byᶜ
    ; upperᶜ
    )
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using
    ( absᶜ
    ; absᶜ-triangle
    ; nonnegativeᶜ-add
    )
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
  using (≤ᶜ-add)
open import Constructive.Analysis.Reals.Series.Finite using (partialSum)
open import Constructive.Analysis.Reals.Series.Tail
  using
    ( TailBound
    ; nonnegative-upper→bounded-byᶜ
    ; tailSum
    ; tailSum-nonnegative
    ; tailSum-suc-start
    )
open import Constructive.Analysis.Reals.Series.Comparison
  using
    ( SeriesMajorizedBy
    ; comparisonTest
    ; seriesMajorizedByTerms
    )
open import Constructive.Data.PositiveRationals

import Constructive.Analysis.Reals.Sequences.Algebra as SeqAlg
import Constructive.Analysis.Reals.Sequences.Convergence as SeqConv
open import Constructive.Analysis.Modulus
  using (AntitoneNatModulus)

open import Constructive.Analysis.Reals.Series.CauchyProduct.Finite
open import Constructive.Analysis.Reals.Series.CauchyProduct.RemainderBounds


private
  module SolverHelpers {ℓ : Level} (𝒩 : CommRing ℓ) where
    open CommRingStr (𝒩 .snd)

    tail-cauchy-product-decomposition-step :
      (u v tv cp tcp : 𝒩 .fst) →
      ((u · v + cp) + (u · tv + tcp)) ≡
      (u · (v + tv) + (cp + tcp))
    tail-cauchy-product-decomposition-step _ _ _ _ _ =
      solve! 𝒩





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
    NatOrder.≤-trans NatOrder.≤-sucℕ sucm≤q

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
