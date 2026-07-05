{-

  The Archimedean Property of Linearly Ordered Commutative Rings

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.LinearlyOrderedCommRing.Archimedean where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing using (CommRingStr)
open import Cubical.Relation.Nullary

open import Constructive.Preliminary.Nat
open import Constructive.Algebra.LinearlyOrderedCommRing
open import Constructive.Algebra.OrderedCommRing.Archimedean public

private
  variable
    ℓ ℓ' : Level


module _ (𝓡 : LinearlyOrderedCommRing ℓ ℓ') where

  open CommRingStr ((LinearlyOrderedCommRing→CommRing 𝓡) .snd) using (0r)
  open LinearlyOrderedCommRingStr 𝓡

  -- Linearity turns the truncated ordered-ring property into an untruncated
  -- witness.

  isArchimedean∥∥→isArchimedean :
    isArchimedean∥∥ (𝓡 .fst) → isArchimedean (𝓡 .fst)
  isArchimedean∥∥→isArchimedean ∥archimedean∥ q ε ε>0 = case-split (trichotomy q 0r)
    where
    case-split : Trichotomy (𝓡 .fst) q 0r → _
    case-split (lt q<0) = 0 , subst (_> q) (sym (0⋆q≡0 ε)) q<0
    case-split (eq q≡0) = 1 , transport (λ i → 1⋆q≡q ε (~ i) > q≡0 (~ i)) ε>0
    case-split (gt q>0) = find (λ _ → dec< _ _) (∥archimedean∥ q ε ε>0)
