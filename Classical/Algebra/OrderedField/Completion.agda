{-

MacNeille Completion of Archimedean Ordered Fields

The construction is by Dedekind cuts. Classically, for linear orders
and ordered fields, MacNeille completeness is the usual Dedekind
least-upper-bound completeness. Constructively, the MacNeille name
keeps this apart from other Dedekind-cut completeness notions.

TODO: Separate the completion procedure into constructive/classical parts,
as indicated in `https://github.com/kangrongji/cubical-classics/issues/10`.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Classical.Algebra.OrderedField.Completion where

open import Cubical.Foundations.Prelude
open import Classical.Axioms
open import Constructive.Algebra.StrictlyOrderedCommRing.Archimedes
open import Constructive.Algebra.StrictlyOrderedField.Base
open import Constructive.Algebra.StrictlyOrderedField.Morphism
open import Classical.Algebra.OrderedField.Completeness
open import Classical.DedekindCut.Completeness
open import Classical.DedekindCut.UniversalProperty

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level


module Completion ⦃ 🤖 : Oracle ⦄
  (𝒦 : StrictlyOrderedField ℓ ℓ')(archimedes : isArchimedean (𝒦 .fst)) where

  open MacNeilleCompleteOrderedField
  open CompletenessOfCuts 𝒦
  open UniversalProperty  𝒦

  complete : MacNeilleCompleteOrderedField (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  complete = 𝕂MacNeilleCompleteOrderedField archimedes

  extend : (𝒦' : MacNeilleCompleteOrderedField ℓ'' ℓ''') → StrictlyOrderedFieldHom 𝒦 (𝒦' .fst) → StrictlyOrderedFieldHom (complete .fst) (𝒦' .fst)
  extend = extendedStrictlyOrderedFieldHom archimedes
