{-

Nonnegative approximation for Dedekind-completion arithmetic

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Approximation where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

import Constructive.Algebra.LinearlyOrderedCommRing.Base as LinearBase
open import Constructive.Algebra.LinearlyOrderedCommRing
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.Algebra.LinearlyOrderedField.Archimedean
open import Constructive.Analysis.Completions.DedekindCompletion.Base
open import Constructive.Analysis.Completions.DedekindCompletion.Order
open import Constructive.Analysis.Completions.DedekindCompletion.Approximation
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Addition
open import Constructive.Foundations.Powerset hiding (Pred)

private
  variable
    ℓ ℓ' ℓᴾ : Level


module NonnegativeApproximation
  (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') {ℓᴾ : Level} where

  baseField : LinearlyOrderedField ℓ ℓ'
  baseField = 𝒜 .fst

  open CompletionBase baseField
  private
    module OrdD = CompletionOrder baseField

  open LinearlyOrderedFieldStr baseField

  open Addition 𝒜 {ℓᴾ}
  open CompletionApproximation 𝒜 {ℓᴾ}

  private
    K : Type ℓ
    K = baseField .fst .fst .fst

  upper-of-nonnegative>0 :
    (x : DedekindCompletion ℓᴾ) →
    OrdD._≤_ 0𝔻 x →
    (q : K) →
    q ∈ upper x →
    0r < q
  upper-of-nonnegative>0 x 0≤x q q∈Ux with trichotomy 0r q
  ... | LinearBase.lt 0<q = 0<q
  ... | LinearBase.eq 0≡q =
    Empty.rec
      (Prop.rec Empty.isProp⊥
        (λ (r , r<q , r∈Ux) →
          let
            r<0 : r < 0r
            r<0 =
              subst (λ v → r < v) (sym 0≡q) r<q
          in
          CompletionBase.disjoint {𝒦 = baseField} x r (0≤x r (lift r<0)) r∈Ux)
        (CompletionBase.upper-rounded {𝒦 = baseField} x q q∈Ux))
  ... | LinearBase.gt q<0 =
    Empty.rec
      (CompletionBase.disjoint {𝒦 = baseField} x q (0≤x q (lift q<0)) q∈Ux)

  CloseBounds≥0 : DedekindCompletion ℓᴾ → K → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
  CloseBounds≥0 x ε =
    Σ[ p ∈ K ] Σ[ q ∈ K ]
      (p ∈ lower x) ×
      (q ∈ upper x) ×
      (p < q) ×
      (q < p + ε) ×
      (0r < q)

  BoundedCloseBounds≥0 :
    DedekindCompletion ℓᴾ → K → K → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
  BoundedCloseBounds≥0 x ε u =
    Σ[ p ∈ K ] Σ[ q ∈ K ]
      (p ∈ lower x) ×
      (q ∈ upper x) ×
      (p < q) ×
      (q < p + ε) ×
      (0r < q) ×
      (q ≤ u)

  close-bounds≥0 :
    (x : DedekindCompletion ℓᴾ) →
    OrdD._≤_ 0𝔻 x →
    (ε : K) →
    0r < ε →
    ∥ CloseBounds≥0 x ε ∥₁
  close-bounds≥0 x 0≤x ε 0<ε =
    Prop.rec squash₁
      (λ (p , q , p∈Lx , q∈Ux , p<q , q<p+ε) →
        ∣ p , q
        , p∈Lx
        , q∈Ux
        , p<q
        , q<p+ε
        , upper-of-nonnegative>0 x 0≤x q q∈Ux
        ∣₁)
      (close-bounds x ε 0<ε)

  bounded-close-bounds≥0 :
    (x : DedekindCompletion ℓᴾ) →
    OrdD._≤_ 0𝔻 x →
    (ε u : K) →
    0r < ε →
    u ∈ upper x →
    ∥ BoundedCloseBounds≥0 x ε u ∥₁
  bounded-close-bounds≥0 x 0≤x ε u 0<ε u∈Ux =
    Prop.rec squash₁
      (λ (p , q , p∈Lx , q∈Ux , p<q , q<p+ε , q≤u) →
        ∣ p , q
        , p∈Lx
        , q∈Ux
        , p<q
        , q<p+ε
        , upper-of-nonnegative>0 x 0≤x q q∈Ux
        , q≤u
        ∣₁)
      (bounded-close-bounds x ε u 0<ε u∈Ux)

  MultiplicationCloseBounds :
    DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ → K → K → K →
    Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
  MultiplicationCloseBounds x y δ U V =
    Σ[ lx ∈ K ] Σ[ ux ∈ K ] Σ[ ly ∈ K ] Σ[ uy ∈ K ]
      (lx ∈ lower x) ×
      (ux ∈ upper x) ×
      (lx < ux) ×
      (ux < lx + δ) ×
      (0r < ux) ×
      (ux ≤ U) ×
      (ly ∈ lower y) ×
      (uy ∈ upper y) ×
      (ly < uy) ×
      (uy < ly + δ) ×
      (0r < uy) ×
      (uy ≤ V)

  multiplication-close-bounds :
    (x y : DedekindCompletion ℓᴾ) →
    OrdD._≤_ 0𝔻 x →
    OrdD._≤_ 0𝔻 y →
    (δ U V : K) →
    0r < δ →
    U ∈ upper x →
    V ∈ upper y →
    ∥ MultiplicationCloseBounds x y δ U V ∥₁
  multiplication-close-bounds x y 0≤x 0≤y δ U V 0<δ U∈Ux V∈Uy =
    Prop.rec2 squash₁
      (λ (lx , ux , lx∈Lx , ux∈Ux , lx<ux , ux<lx+δ , 0<ux , ux≤U)
         (ly , uy , ly∈Ly , uy∈Uy , ly<uy , uy<ly+δ , 0<uy , uy≤V) →
        ∣ lx , ux , ly , uy
        , lx∈Lx
        , ux∈Ux
        , lx<ux
        , ux<lx+δ
        , 0<ux
        , ux≤U
        , ly∈Ly
        , uy∈Uy
        , ly<uy
        , uy<ly+δ
        , 0<uy
        , uy≤V
        ∣₁)
      (bounded-close-bounds≥0 x 0≤x δ U 0<δ U∈Ux)
      (bounded-close-bounds≥0 y 0≤y δ V 0<δ V∈Uy)
