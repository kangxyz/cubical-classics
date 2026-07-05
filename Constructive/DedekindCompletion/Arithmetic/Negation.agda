{-

Negation of constructive Dedekind completions

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.DedekindCompletion.Arithmetic.Negation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence using (hPropExt)

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedean
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.DedekindCompletion
open import Constructive.Foundations.Powerset hiding (Pred)

private
  variable
    ℓ ℓ' ℓᴾ : Level


module Negation (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') {ℓᴾ : Level} where

  𝒦 : LinearlyOrderedField ℓ ℓ'
  𝒦 = 𝒜 .fst

  open CompletionBase 𝒦
  module O = CompletionOrder 𝒦
  open LinearlyOrderedFieldStr 𝒦

  private
    K : Type ℓ
    K = 𝒦 .fst .fst .fst

  -𝔻_ : DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ
  (-𝔻 x) .lower q = (- q ∈ upper x) , isProp∈ (upper x) (- q)
  (-𝔻 x) .upper q = (- q ∈ lower x) , isProp∈ (lower x) (- q)
  (-𝔻 x) .isDedekindCut .IsDedekindCut.lower-inhabited =
    Prop.rec squash₁
      (λ (q , q∈Ux) →
        ∣ - q
        , subst (λ r → r ∈ upper x) (sym (-Idempotent q)) q∈Ux
        ∣₁)
      (CompletionBase.upper-inhabited {𝒦 = 𝒦} x)
  (-𝔻 x) .isDedekindCut .IsDedekindCut.upper-inhabited =
    Prop.rec squash₁
      (λ (q , q∈Lx) →
        ∣ - q
        , subst (λ r → r ∈ lower x) (sym (-Idempotent q)) q∈Lx
        ∣₁)
      (CompletionBase.lower-inhabited {𝒦 = 𝒦} x)
  (-𝔻 x) .isDedekindCut .IsDedekindCut.lower-closed =
    λ p q p<q -q∈Ux →
      CompletionBase.upper-closed {𝒦 = 𝒦} x (- q) (- p) (-Reverse< p<q) -q∈Ux
  (-𝔻 x) .isDedekindCut .IsDedekindCut.upper-closed =
    λ p q p<q -p∈Lx →
      CompletionBase.lower-closed {𝒦 = 𝒦} x (- q) (- p) (-Reverse< p<q) -p∈Lx
  (-𝔻 x) .isDedekindCut .IsDedekindCut.lower-rounded =
    λ q -q∈Ux →
      Prop.rec squash₁
        (λ (r , r<-q , r∈Ux) →
          ∣ - r
          , subst (λ s → s < - r)
              (-Idempotent q)
              (-Reverse< r<-q)
          , subst (λ s → s ∈ upper x) (sym (-Idempotent r)) r∈Ux
          ∣₁)
        (CompletionBase.upper-rounded {𝒦 = 𝒦} x (- q) -q∈Ux)
  (-𝔻 x) .isDedekindCut .IsDedekindCut.upper-rounded =
    λ q -q∈Lx →
      Prop.rec squash₁
        (λ (r , -q<r , r∈Lx) →
          ∣ - r
          , subst (λ s → - r < s)
              (-Idempotent q)
              (-Reverse< -q<r)
          , subst (λ s → s ∈ lower x) (sym (-Idempotent r)) r∈Lx
          ∣₁)
        (CompletionBase.lower-rounded {𝒦 = 𝒦} x (- q) -q∈Lx)
  (-𝔻 x) .isDedekindCut .IsDedekindCut.disjoint =
    λ q -q∈Ux -q∈Lx →
      CompletionBase.disjoint {𝒦 = 𝒦} x (- q) -q∈Lx -q∈Ux
  (-𝔻 x) .isDedekindCut .IsDedekindCut.located =
    λ p q p<q →
      Prop.rec squash₁
        (λ where
          (Sum.inl -q∈Lx) → ∣ Sum.inr -q∈Lx ∣₁
          (Sum.inr -p∈Ux) → ∣ Sum.inl -p∈Ux ∣₁)
        (CompletionBase.located {𝒦 = 𝒦} x (- q) (- p) (-Reverse< p<q))

  infix 8 -𝔻_

  neg-involutive :
    (x : DedekindCompletion ℓᴾ) →
    -𝔻 (-𝔻 x) ≡ x
  neg-involutive x =
    completionExt (-𝔻 (-𝔻 x)) x
      (λ q → subst (λ r → r ∈ lower x) (-Idempotent q))
      (λ q → subst (λ r → r ∈ lower x) (sym (-Idempotent q)))
      (λ q → subst (λ r → r ∈ upper x) (-Idempotent q))
      (λ q → subst (λ r → r ∈ upper x) (sym (-Idempotent q)))

  neg-≤-reverse :
    (x y : DedekindCompletion ℓᴾ) →
    O._≤_ x y →
    O._≤_ (-𝔻 y) (-𝔻 x)
  neg-≤-reverse x y x≤y q -q∈Uy =
    O.upper-inclusion-from-lower y x x≤y (- q) -q∈Uy

  neg-≤-reflect :
    (x y : DedekindCompletion ℓᴾ) →
    O._≤_ (-𝔻 y) (-𝔻 x) →
    O._≤_ x y
  neg-≤-reflect x y -y≤-x q q∈Lx =
    subst (λ r → r ∈ lower y) (-Idempotent q)
      (O.upper-inclusion-from-lower (-𝔻 x) (-𝔻 y) -y≤-x
        (- q)
        (subst (λ r → r ∈ lower x) (sym (-Idempotent q)) q∈Lx))

  neg-≤-iff :
    (x y : DedekindCompletion ℓᴾ) →
    O._≤_ x y ≡ O._≤_ (-𝔻 y) (-𝔻 x)
  neg-≤-iff x y =
    hPropExt (O.isProp≤ x y) (O.isProp≤ (-𝔻 y) (-𝔻 x))
      (neg-≤-reverse x y)
      (neg-≤-reflect x y)

  neg-<-reverse :
    (x y : DedekindCompletion ℓᴾ) →
    O._<_ x y →
    O._<_ (-𝔻 y) (-𝔻 x)
  neg-<-reverse x y x<y =
    Prop.rec squash₁
      (λ (q , q∈Ux , q∈Ly) →
        ∣ - q
        , subst (λ r → r ∈ lower y) (sym (-Idempotent q)) q∈Ly
        , subst (λ r → r ∈ upper x) (sym (-Idempotent q)) q∈Ux
        ∣₁)
      x<y
