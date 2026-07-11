{-

Neumann inverses from convergent finite series identities

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Series.Neumann where

open import Cubical.Foundations.Prelude

import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; suc ; zero)
import Cubical.Data.Nat.Order as NatOrder
open import Cubical.Data.Sigma using (fst)

open import Constructive.Analysis.Metric.Base using (MetricSpace)
open import Constructive.Analysis.Modulus using (AntitoneNatModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Metric
  using (CauchyRealsMetricSpace)
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using (neg-zeroᶜ)
open import Constructive.Analysis.Reals.Series.Cauchy
  using
    ( seriesSumFromFiniteTailBound
    ; seriesSumFromFiniteTailBound-mul-left-convergesAt
    )
open import Constructive.Analysis.Reals.Series.Finite using (partialSum)
open import Constructive.Analysis.Reals.Series.Tail
  using (TailBound ; tailSum ; tailSum-one)
open import Constructive.Data.PositiveRationals


seriesSumFromFiniteTailBound-neumannRightInverse :
  (factor : ℝᶜ) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ factor →
  (u : ℕ → ℝᶜ) →
  (μ : ℚ⁺ → ℕ) →
  (tailBound : TailBound u μ) →
  (μ-antitone : AntitoneNatModulus μ) →
  (index : ℕ → ℕ) →
  ((n : ℕ) → NatOrder._≤_ n (index n)) →
  ((n : ℕ) →
    factor ·ᶜ partialSum u (index n) ≡
    1ᶜ +ᶜ (-ᶜ u (index n))) →
  factor ·ᶜ seriesSumFromFiniteTailBound u μ tailBound μ-antitone ≡ 1ᶜ
seriesSumFromFiniteTailBound-neumannRightInverse
  factor
  κ
  factorBound
  u
  μ
  tailBound
  μ-antitone
  index
  index-lower
  finiteIdentity =
  MetricSpace.close-separated
    CauchyRealsMetricSpace
    product
    1ᶜ
    closeAt
  where
  sum : ℝᶜ
  sum =
    seriesSumFromFiniteTailBound u μ tailBound μ-antitone

  product : ℝᶜ
  product =
    factor ·ᶜ sum

  closeAt :
    (ε : ℚ⁺) →
    product ∼[ ε ] 1ᶜ
  closeAt ε =
    subst
      (λ precision → product ∼[ precision ] 1ᶜ)
      (half⁺+half⁺≡ ε)
      (MetricSpace.close-triangle
        CauchyRealsMetricSpace
        product∼partial
        partial∼one)
    where
    η : ℚ⁺
    η =
      half⁺ ε

    productPrecision : ℚ⁺
    productPrecision =
      quarter⁺
        (half⁺
          (fst (mulᶜ-continuous-right-with-bound κ factor factorBound) η))

    tailPrecision : ℚ⁺
    tailPrecision =
      half⁺ η

    productIndex tailIndex baseIndex n : ℕ
    productIndex =
      μ productPrecision
    tailIndex =
      μ tailPrecision
    baseIndex =
      productIndex Nat.+ tailIndex
    n =
      index baseIndex

    baseIndex≤n : NatOrder._≤_ baseIndex n
    baseIndex≤n =
      index-lower baseIndex

    productIndex≤n : NatOrder._≤_ productIndex n
    productIndex≤n =
      NatOrder.≤-trans
        (tailIndex , Nat.+-comm tailIndex productIndex)
        baseIndex≤n

    tailIndex≤n : NatOrder._≤_ tailIndex n
    tailIndex≤n =
      NatOrder.≤-trans
        (productIndex , refl)
        baseIndex≤n

    product∼partial :
      product ∼[ η ] factor ·ᶜ partialSum u n
    product∼partial =
      seriesSumFromFiniteTailBound-mul-left-convergesAt
        factor
        κ
        factorBound
        u
        μ
        tailBound
        μ-antitone
        η
        n
        productIndex≤n

    termTailBound :
      BoundedByᶜ tailPrecision (tailSum u n (suc zero))
    termTailBound =
      tailBound tailPrecision n (suc zero) tailIndex≤n

    termBound :
      BoundedByᶜ tailPrecision (u n)
    termBound =
      subst
        (BoundedByᶜ tailPrecision)
        (tailSum-one u n)
        termTailBound

    term∼zero :
      u n ∼[ η ] 0ᶜ
    term∼zero =
      bounded-byᶜ-close-zero
        tailPrecision
        η
        (u n)
        termBound
        (half< η)

    negTerm∼zero :
      (-ᶜ u n) ∼[ η ] 0ᶜ
    negTerm∼zero =
      subst
        (λ z → (-ᶜ u n) ∼[ η ] z)
        neg-zeroᶜ
        (neg-close term∼zero)

    oneMinusTerm∼one :
      (1ᶜ +ᶜ (-ᶜ u n)) ∼[ η ] 1ᶜ
    oneMinusTerm∼one =
      subst
        (λ z → (1ᶜ +ᶜ (-ᶜ u n)) ∼[ η ] z)
        (add-zero-right 1ᶜ)
        (add-close-right 1ᶜ negTerm∼zero)

    partial∼one :
      factor ·ᶜ partialSum u n ∼[ η ] 1ᶜ
    partial∼one =
      subst
        (λ z → z ∼[ η ] 1ᶜ)
        (sym (finiteIdentity baseIndex))
        oneMinusTerm∼one
