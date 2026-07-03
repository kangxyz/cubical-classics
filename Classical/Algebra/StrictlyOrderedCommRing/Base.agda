{-

Strictly ordered commutative ring

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.StrictlyOrderedCommRing.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing using (CommRing)
open import Cubical.Algebra.OrderedCommRing as CubicalOrderedCommRing
  using (OrderedCommRing ; OrderedCommRingStr ; OrderedCommRing→CommRing)

private
  variable
    ℓ ℓ' : Level


module _ (𝓡 : OrderedCommRing ℓ ℓ') where

  open OrderedCommRingStr (𝓡 .snd)

  private
    R = 𝓡 .fst

  data Trichotomy (x y : R) : Type (ℓ-max ℓ ℓ') where
    lt : x < y → Trichotomy x y
    eq : x ≡ y → Trichotomy x y
    gt : y < x → Trichotomy x y


  record StrictOrderStrOnOrderedCommRing : Type (ℓ-suc (ℓ-max ℓ ℓ')) where

    constructor strictorderstr
    no-eta-equality

    field

      trichotomy : (x y : R) → Trichotomy x y


StrictlyOrderedCommRing : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
StrictlyOrderedCommRing ℓ ℓ' = Σ[ 𝓡 ∈ OrderedCommRing ℓ ℓ' ] StrictOrderStrOnOrderedCommRing 𝓡

StrictlyOrderedCommRing→OrderedCommRing : StrictlyOrderedCommRing ℓ ℓ' → OrderedCommRing ℓ ℓ'
StrictlyOrderedCommRing→OrderedCommRing = fst

StrictlyOrderedCommRing→CommRing : StrictlyOrderedCommRing ℓ ℓ' → CommRing ℓ
StrictlyOrderedCommRing→CommRing 𝓡 = OrderedCommRing→CommRing (𝓡 .fst)
