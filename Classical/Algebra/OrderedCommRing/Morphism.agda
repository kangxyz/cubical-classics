{-

  Homomorphisms between ordered commutative rings

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedCommRing.Morphism where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level


record OrderedCommRingHom
  (𝓡 : OrderedCommRing ℓ ℓ')
  (𝓡' : OrderedCommRing ℓ'' ℓ''')
  : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓ''')) where
  field
    ring-hom : CommRingHom (OrderedCommRing→CommRing 𝓡) (OrderedCommRing→CommRing 𝓡')
    pres<    : (x y : 𝓡 .fst) → OrderedCommRingStr._<_ (𝓡 .snd) x y →
               OrderedCommRingStr._<_ (𝓡' .snd) (ring-hom .fst x) (ring-hom .fst y)
    pres≤    : (x y : 𝓡 .fst) → OrderedCommRingStr._≤_ (𝓡 .snd) x y →
               OrderedCommRingStr._≤_ (𝓡' .snd) (ring-hom .fst x) (ring-hom .fst y)
