{-

Completion of Archimedean Ordered Field

Warning: Though classically the procedure defined here is called Dedekind completion,
constructively it is the MacNeille completion, which is different from the Dedekind one.

TODO: Separating the completion procedure into construtive/classical parts,
as indicated in `https://github.com/kangrongji/cubical-classics/issues/10`.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Classical.Algebra.OrderedField.Completion where

open import Cubical.Foundations.Prelude
open import Classical.Axioms
open import Constructive.Algebra.StrictlyOrderedCommRing.Archimedes
open import Constructive.Algebra.OrderedField.Base
open import Constructive.Algebra.OrderedField.Morphism
open import Classical.Algebra.OrderedField.Completeness
open import Classical.DedekindCut.Completeness
open import Classical.DedekindCut.UniversalProperty

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level


module Completion ⦃ 🤖 : Oracle ⦄
  (𝒦 : OrderedField ℓ ℓ')(archimedes : isArchimedean (𝒦 .fst)) where

  open CompleteOrderedField
  open CompletenessOfCuts 𝒦
  open UniversalProperty  𝒦

  complete : CompleteOrderedField (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  complete = 𝕂CompleteOrderedField archimedes

  extend : (𝒦' : CompleteOrderedField ℓ'' ℓ''') → OrderedFieldHom 𝒦 (𝒦' .fst) → OrderedFieldHom (complete .fst) (𝒦' .fst)
  extend = extendedOrderedFieldHom archimedes
