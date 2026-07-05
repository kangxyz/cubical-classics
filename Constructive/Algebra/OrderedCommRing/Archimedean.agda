{-

  The Archimedean Property of Ordered Commutative Rings

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.OrderedCommRing.Archimedean where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
  using (OrderedCommRing ; OrderedCommRing→CommRing)

open import Constructive.Algebra.OrderedCommRing.Properties

private
  variable
    ℓ ℓ' : Level


module _ (𝓡 : OrderedCommRing ℓ ℓ') where

  private
    R = 𝓡 .fst

  open OrderedCommRingTheory 𝓡
  open CommRingStr ((OrderedCommRing→CommRing 𝓡) .snd) using (0r)

  isArchimedean : Type (ℓ-max ℓ ℓ')
  isArchimedean = (q ε : R) → ε > 0r → Σ[ n ∈ ℕ ] n ⋆ ε > q

  isArchimedean∥∥ : Type (ℓ-max ℓ ℓ')
  isArchimedean∥∥ = (q ε : R) → ε > 0r → ∥ Σ[ n ∈ ℕ ] n ⋆ ε > q ∥₁

  isPropIsArchimedean∥∥ : isProp isArchimedean∥∥
  isPropIsArchimedean∥∥ =
    isPropΠ3 (λ _ _ _ → squash₁)

  isArchimedean→isArchimedean∥∥ : isArchimedean → isArchimedean∥∥
  isArchimedean→isArchimedean∥∥ archimedean q ε ε>0 =
    ∣ archimedean q ε ε>0 ∣₁
