{-

Constructive Dedekind reals over the rationals

This is the rational instance of `Constructive.DedekindCompletion`.

-}
{-# OPTIONS --safe #-}
module Constructive.DedekindReals.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals using (ℚ)

import Constructive.DedekindCompletion.Base as Completion
open import Constructive.DedekindCompletion.Instances.Rationals

private
  variable
    ℓ : Level

  ℚField = ℚArchimedeanLinearlyOrderedField .fst

module Base = Completion.CompletionBase ℚField


ℚPred : (ℓ : Level) → Type (ℓ-suc ℓ)
ℚPred = Base.Pred

_∈_ : ℚ → ℚPred ℓ → Type ℓ
_∈_ = Base._∈_

infix 4 _∈_

isProp∈ : (P : ℚPred ℓ) → (q : ℚ) → isProp (q ∈ P)
isProp∈ = Base.isProp∈

isSetℚPred : isSet (ℚPred ℓ)
isSetℚPred = Base.isSetPred

_⊆_ : ℚPred ℓ → ℚPred ℓ → Type ℓ
_⊆_ = Base._⊆_

infix 4 _⊆_

isProp⊆ : (P Q : ℚPred ℓ) → isProp (P ⊆ Q)
isProp⊆ = Base.isProp⊆

⊆-refl : (P : ℚPred ℓ) → P ⊆ P
⊆-refl = Base.⊆-refl

⊆-trans : (P Q R : ℚPred ℓ) → P ⊆ Q → Q ⊆ R → P ⊆ R
⊆-trans = Base.⊆-trans

predExt : (P Q : ℚPred ℓ) → P ⊆ Q → Q ⊆ P → P ≡ Q
predExt = Base.predExt


IsDedekindReal : ℚPred ℓ → ℚPred ℓ → Type ℓ
IsDedekindReal = Base.IsDedekindCut

module IsDedekindReal = Base.IsDedekindCut

DedekindReal : (ℓ : Level) → Type (ℓ-suc ℓ)
DedekindReal = Base.DedekindCompletion

module DedekindReal = Base.DedekindCompletion

open Base public
  using
    ( lower
    ; upper
    ; lower-inhabited
    ; upper-inhabited
    ; lower-closed
    ; upper-closed
    ; lower-rounded
    ; upper-rounded
    ; disjoint
    ; located
    )


isPropIsDedekindReal : (L U : ℚPred ℓ) → isProp (IsDedekindReal L U)
isPropIsDedekindReal = Base.isPropIsDedekindCut

DedekindRealPath :
  (x y : DedekindReal ℓ) →
  lower x ≡ lower y →
  upper x ≡ upper y →
  x ≡ y
DedekindRealPath = Base.DedekindCompletionPath

realExt :
  (x y : DedekindReal ℓ) →
  lower x ⊆ lower y →
  lower y ⊆ lower x →
  upper x ⊆ upper y →
  upper y ⊆ upper x →
  x ≡ y
realExt = Base.completionExt

isSetDedekindReal : isSet (DedekindReal ℓ)
isSetDedekindReal = Base.isSetDedekindCompletion
