{-

Strictly ordered commutative ring

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.StrictlyOrderedCommRing.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing using (CommRing)
open import Cubical.Algebra.OrderedCommRing
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

  isPropTrichotomy : (x y : R) → isProp (Trichotomy x y)
  isPropTrichotomy x y (lt x<y) (lt x<y') i =
    lt (is-prop-valued< x y x<y x<y' i)
  isPropTrichotomy x y (eq x≡y) (eq x≡y') i =
    eq (is-set x y x≡y x≡y' i)
  isPropTrichotomy x y (gt y<x) (gt y<x') i =
    gt (is-prop-valued< y x y<x y<x' i)
  isPropTrichotomy x y (lt x<y) (eq x≡y) =
    Empty.rec (is-irrefl y (subst (λ z → z < y) x≡y x<y))
  isPropTrichotomy x y (lt x<y) (gt y<x) =
    Empty.rec (is-asym x y x<y y<x)
  isPropTrichotomy x y (gt y<x) (eq x≡y) =
    Empty.rec (is-irrefl x (subst (λ z → z < x) (sym x≡y) y<x))
  isPropTrichotomy x y (gt y<x) (lt x<y) =
    Empty.rec (is-asym x y x<y y<x)
  isPropTrichotomy x y (eq x≡y) (lt x<y) =
    Empty.rec (is-irrefl y (subst (λ z → z < y) x≡y x<y))
  isPropTrichotomy x y (eq x≡y) (gt y<x) =
    Empty.rec (is-irrefl x (subst (λ z → z < x) (sym x≡y) y<x))


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
