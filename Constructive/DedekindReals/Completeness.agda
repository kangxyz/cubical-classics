{-

Constructive Dedekind completeness for constructive Dedekind reals

This is the rational instance of generic Dedekind completeness.  Dedekind
completeness means that every located cut of Dedekind reals is represented by
a unique Dedekind real.

-}
{-# OPTIONS --safe #-}
module Constructive.DedekindReals.Completeness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)

open import Constructive.DedekindCompletion.Completeness as Completion
open import Constructive.Algebra.LinearlyOrderedField.Instances.Rationals
open import Constructive.DedekindReals

private
  variable
    ℓ : Level

module Generic {ℓ : Level} =
  Completion.CompletionCompleteness ℚArchimedeanLinearlyOrderedField ℓ


RealPred : (ℓ : Level) → Type (ℓ-suc ℓ)
RealPred ℓ = Generic.CompletionPred {ℓ = ℓ}

_∈ᴿ_ : DedekindReal ℓ → RealPred ℓ → Type ℓ
_∈ᴿ_ {ℓ = ℓ} = Generic._∈𝔻_ {ℓ = ℓ}

infix 4 _∈ᴿ_

isProp∈ᴿ : (P : RealPred ℓ) → (x : DedekindReal ℓ) → isProp (x ∈ᴿ P)
isProp∈ᴿ {ℓ = ℓ} = Generic.isProp∈𝔻 {ℓ = ℓ}


record IsRealValuedCut (L U : RealPred ℓ) : Type (ℓ-suc ℓ) where
  no-eta-equality

  field
    real-lower-inhabited :
      ∥ Σ[ x ∈ DedekindReal ℓ ] x ∈ᴿ L ∥₁

    real-upper-inhabited :
      ∥ Σ[ x ∈ DedekindReal ℓ ] x ∈ᴿ U ∥₁

    real-lower-closed :
      (x y : DedekindReal ℓ) →
      Order._<_ {ℓ = ℓ} x y →
      y ∈ᴿ L →
      x ∈ᴿ L

    real-upper-closed :
      (x y : DedekindReal ℓ) →
      Order._<_ {ℓ = ℓ} x y →
      x ∈ᴿ U →
      y ∈ᴿ U

    real-lower-rounded :
      (x : DedekindReal ℓ) →
      x ∈ᴿ L →
      ∥ Σ[ y ∈ DedekindReal ℓ ] (Order._<_ {ℓ = ℓ} x y) × (y ∈ᴿ L) ∥₁

    real-upper-rounded :
      (x : DedekindReal ℓ) →
      x ∈ᴿ U →
      ∥ Σ[ y ∈ DedekindReal ℓ ] (Order._<_ {ℓ = ℓ} y x) × (y ∈ᴿ U) ∥₁

    real-disjoint :
      (x : DedekindReal ℓ) →
      x ∈ᴿ L →
      x ∈ᴿ U →
      ⊥

    real-located :
      (x y : DedekindReal ℓ) →
      Order._<_ {ℓ = ℓ} x y →
      ∥ (x ∈ᴿ L) ⊎ (y ∈ᴿ U) ∥₁


record RealValuedCut (ℓ : Level) : Type (ℓ-suc ℓ) where
  no-eta-equality

  field
    realLower : RealPred ℓ
    realUpper : RealPred ℓ
    isRealValuedCut : IsRealValuedCut realLower realUpper

  open IsRealValuedCut isRealValuedCut public


open RealValuedCut public


toCompletionValuedCut :
  RealValuedCut ℓ →
  Generic.CompletionValuedCut {ℓ = ℓ}
toCompletionValuedCut C .Generic.completionLower = realLower C
toCompletionValuedCut C .Generic.completionUpper = realUpper C
toCompletionValuedCut C .Generic.isCompletionValuedCut
  .Generic.IsCompletionValuedCut.completion-lower-inhabited =
  real-lower-inhabited C
toCompletionValuedCut C .Generic.isCompletionValuedCut
  .Generic.IsCompletionValuedCut.completion-upper-inhabited =
  real-upper-inhabited C
toCompletionValuedCut C .Generic.isCompletionValuedCut
  .Generic.IsCompletionValuedCut.completion-lower-closed =
  real-lower-closed C
toCompletionValuedCut C .Generic.isCompletionValuedCut
  .Generic.IsCompletionValuedCut.completion-upper-closed =
  real-upper-closed C
toCompletionValuedCut C .Generic.isCompletionValuedCut
  .Generic.IsCompletionValuedCut.completion-lower-rounded =
  real-lower-rounded C
toCompletionValuedCut C .Generic.isCompletionValuedCut
  .Generic.IsCompletionValuedCut.completion-upper-rounded =
  real-upper-rounded C
toCompletionValuedCut C .Generic.isCompletionValuedCut
  .Generic.IsCompletionValuedCut.completion-disjoint =
  real-disjoint C
toCompletionValuedCut C .Generic.isCompletionValuedCut
  .Generic.IsCompletionValuedCut.completion-located =
  real-located C


representingLower : RealValuedCut ℓ → ℚPred ℓ
representingLower C =
  Generic.representingLower (toCompletionValuedCut C)


representingUpper : RealValuedCut ℓ → ℚPred ℓ
representingUpper C =
  Generic.representingUpper (toCompletionValuedCut C)


isDedekindRealRepresenting :
  (C : RealValuedCut ℓ) →
  IsDedekindReal (representingLower C) (representingUpper C)
isDedekindRealRepresenting C =
  Generic.isDedekindCutRepresenting (toCompletionValuedCut C)


representing-real : RealValuedCut ℓ → DedekindReal ℓ
representing-real C =
  Generic.representing-completion (toCompletionValuedCut C)


represented-lower :
  (C : RealValuedCut ℓ) (x : DedekindReal ℓ) →
  (x ∈ᴿ realLower C → Order._<_ {ℓ = ℓ} x (representing-real C))
  ×
  (Order._<_ {ℓ = ℓ} x (representing-real C) → x ∈ᴿ realLower C)
represented-lower C =
  Generic.represented-lower (toCompletionValuedCut C)


represented-upper :
  (C : RealValuedCut ℓ) (x : DedekindReal ℓ) →
  (x ∈ᴿ realUpper C → Order._<_ {ℓ = ℓ} (representing-real C) x)
  ×
  (Order._<_ {ℓ = ℓ} (representing-real C) x → x ∈ᴿ realUpper C)
represented-upper C =
  Generic.represented-upper (toCompletionValuedCut C)


representsLower :
  RealValuedCut ℓ →
  DedekindReal ℓ →
  Type (ℓ-suc ℓ)
representsLower C =
  Generic.representsLower (toCompletionValuedCut C)


representsCut :
  RealValuedCut ℓ →
  DedekindReal ℓ →
  Type (ℓ-suc ℓ)
representsCut C =
  Generic.representsCut (toCompletionValuedCut C)


-- Dedekind completeness means that every located cut whose elements are
-- Dedekind reals is represented by a unique Dedekind real.  The representative
-- `z` realizes the lower side as `x < z` and the upper side as `z < x`.
isDedekindComplete : {ℓ : Level} → Type (ℓ-suc ℓ)
isDedekindComplete {ℓ = ℓ} =
  (C : RealValuedCut ℓ) →
  Σ[ z ∈ DedekindReal ℓ ]
    representsCut C z
    ×
    ((z' : DedekindReal ℓ) → representsCut C z' → z' ≡ z)


representing-real-unique :
  (C : RealValuedCut ℓ) (z : DedekindReal ℓ) →
  representsLower C z →
  z ≡ representing-real C
representing-real-unique C =
  Generic.representing-completion-unique (toCompletionValuedCut C)


representing-real-representsLower :
  (C : RealValuedCut ℓ) →
  representsLower C (representing-real C)
representing-real-representsLower C =
  Generic.representing-completion-representsLower (toCompletionValuedCut C)


representing-real-representsCut :
  (C : RealValuedCut ℓ) →
  representsCut C (representing-real C)
representing-real-representsCut C =
  Generic.representing-completion-representsCut (toCompletionValuedCut C)


isDedekindCompleteDedekindReal : {ℓ : Level} → isDedekindComplete {ℓ = ℓ}
isDedekindCompleteDedekindReal C =
  representing-real C ,
  representing-real-representsCut C ,
  λ z z-rep → representing-real-unique C z (z-rep .fst)
