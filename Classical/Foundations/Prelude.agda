{-

This file should contain the very basic fact in classical world,
that differs from constructive approach,
usually the direct and fundamental corollary of the axioms.
Better packing them up to be imported most conveniently.

-}
{-# OPTIONS --safe #-}
module Classical.Foundations.Prelude where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Bool
open import Cubical.Data.Bool.Properties
  using (isPropBool→Type*)
open import Cubical.Relation.Nullary

open import Classical.Axioms.ExcludedMiddle
open import Classical.Axioms.Resizing

private
  variable
    ℓ : Level
    X : Type ℓ


-- Renaming to emphasize that Prop is a subobject classifier in the classical world.

Prop : Type ℓ-zero
Prop = Bool

isSetProp : isSet Prop
isSetProp = isSetBool

type : Prop → Type ℓ
type = Bool→Type*

prop : Prop → hProp ℓ
prop P = Bool→Type* P , isPropBool→Type*

bool : Dec X → Prop
bool = Dec→Bool


-- Packing up the corollary of LEM about impredicativity

module Impredicativity (decide : LEM) where

  -- The type Prop is a subobject classifier

  Prop≃hProp : Prop ≃ hProp ℓ
  Prop≃hProp = Bool≃hProp decide

  isSubobjectClassifierProp : isSubobjectClassifier Prop
  isSubobjectClassifierProp = isSubobjectClassifierBool decide

  -- Law of Excluded Middle implies Propositional Resizing

  shift : Drop
  shift = LEM→Drop decide

  resizing : Resizing
  resizing = LEM→Resizing decide
