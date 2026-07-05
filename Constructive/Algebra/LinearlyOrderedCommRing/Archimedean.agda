{-

  The Archimedean Property of Linearly Ordered Commutative Rings

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.LinearlyOrderedCommRing.Archimedean where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Algebra.CommRing
open import Cubical.Relation.Nullary

open import Constructive.Preliminary.Nat
open import Constructive.Algebra.LinearlyOrderedCommRing

private
  variable
    ℓ ℓ' : Level


module _ (𝓡 : LinearlyOrderedCommRing ℓ ℓ') where

  private
    R = 𝓡 .fst .fst

  open CommRingStr   ((LinearlyOrderedCommRing→CommRing 𝓡) .snd)
  open LinearlyOrderedCommRingStr 𝓡


  -- We have two versions of the Archimedean property.
  -- The untruncated version seems much stronger than the truncated version,
  -- but they turn out to be equivalent.

  isArchimedean : Type (ℓ-max ℓ ℓ')
  isArchimedean = (q ε : R) → ε > 0r → Σ[ n ∈ ℕ ] n ⋆ ε > q

  isArchimedean∥∥ : Type (ℓ-max ℓ ℓ')
  isArchimedean∥∥ = (q ε : R) → ε > 0r → ∥ Σ[ n ∈ ℕ ] n ⋆ ε > q ∥₁


  -- The equivalence; one side is trivial.

  isArchimedean→isArchimedean∥∥ : isArchimedean → isArchimedean∥∥
  isArchimedean→isArchimedean∥∥ archimedean q ε ε>0 = ∣ archimedean q ε ε>0 ∣₁

  isArchimedean∥∥→isArchimedean : isArchimedean∥∥ → isArchimedean
  isArchimedean∥∥→isArchimedean ∥archimedean∥ q ε ε>0 = case-split (trichotomy q 0r)
    where
    case-split : Trichotomy (𝓡 .fst) q 0r → _
    case-split (lt q<0) = 0 , subst (_> q) (sym (0⋆q≡0 ε)) q<0
    case-split (eq q≡0) = 1 , transport (λ i → 1⋆q≡q ε (~ i) > q≡0 (~ i)) ε>0
    case-split (gt q>0) = find (λ _ → dec< _ _) (∥archimedean∥ q ε ε>0)
