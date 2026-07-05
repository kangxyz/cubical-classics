{-

Constructive MacNeille completeness for posets

A MacNeille cut is a pair of predicates closed under the lower-bound /
upper-bound Galois connection:

  L x  iff  x is a lower bound of U
  U y  iff  y is an upper bound of L

The bounded form restricts to cuts whose two sides are inhabited

-}
{-# OPTIONS --safe #-}
module Constructive.Algebra.Order.MacNeilleCompleteness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
  using (∥_∥₁)
open import Cubical.Relation.Binary.Order.Poset
import Constructive.Foundations.Powerset as Powerset

private
  variable
    ℓ ℓ' ℓᴸ ℓᵁ ℓᴾ : Level


module MacNeilleCompleteness (P : Poset ℓ ℓ') where

  private
    Carrier : Type ℓ
    Carrier = P .fst

  open PosetStr (P .snd)
    renaming
      ( _≤_ to _≤P_
      ; is-prop-valued to isProp≤
      ; is-refl to ≤-refl
      ; is-trans to ≤-trans
      )

  Pred : (ℓᴾ : Level) → Type _
  Pred ℓᴾ = Powerset.Pred Carrier ℓᴾ

  open Powerset
    using
      ( _∈_
      ; isProp∈
      ; _⇔ᵖ_
      ; isProp⇔ᵖ
      )

  lowerBounds : Pred ℓᵁ → Pred (ℓ-max ℓ (ℓ-max ℓ' ℓᵁ))
  lowerBounds U x =
    ((u : Carrier) → u ∈ U → x ≤P u) ,
    isPropΠ2 λ u _ → isProp≤ x u

  upperBounds : Pred ℓᴸ → Pred (ℓ-max ℓ (ℓ-max ℓ' ℓᴸ))
  upperBounds L y =
    ((l : Carrier) → l ∈ L → l ≤P y) ,
    isPropΠ2 λ l _ → isProp≤ l y


  record IsMacNeilleCut (L : Pred ℓᴸ) (U : Pred ℓᵁ) :
      Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓᴸ ℓᵁ))) where
    no-eta-equality

    field
      lower-is-lowerBounds : L ⇔ᵖ lowerBounds U
      upper-is-upperBounds : U ⇔ᵖ upperBounds L

  isPropIsMacNeilleCut :
    (L : Pred ℓᴸ) (U : Pred ℓᵁ) →
    isProp (IsMacNeilleCut L U)
  isPropIsMacNeilleCut L U C D i .IsMacNeilleCut.lower-is-lowerBounds =
    isProp⇔ᵖ L (lowerBounds U)
      (C .IsMacNeilleCut.lower-is-lowerBounds)
      (D .IsMacNeilleCut.lower-is-lowerBounds)
      i
  isPropIsMacNeilleCut L U C D i .IsMacNeilleCut.upper-is-upperBounds =
    isProp⇔ᵖ U (upperBounds L)
      (C .IsMacNeilleCut.upper-is-upperBounds)
      (D .IsMacNeilleCut.upper-is-upperBounds)
      i


  record MacNeilleCut (ℓᴸ ℓᵁ : Level) :
      Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓᴸ ℓᵁ)))) where
    no-eta-equality

    field
      lower : Pred ℓᴸ
      upper : Pred ℓᵁ
      isMacNeilleCut : IsMacNeilleCut lower upper

    open IsMacNeilleCut isMacNeilleCut public


  open MacNeilleCut public
  open IsMacNeilleCut public


  principalLower : Carrier → Pred ℓ'
  principalLower c x = (x ≤P c) , isProp≤ x c

  principalUpper : Carrier → Pred ℓ'
  principalUpper c y = (c ≤P y) , isProp≤ c y

  principal-isMacNeilleCut :
    (c : Carrier) →
    IsMacNeilleCut (principalLower c) (principalUpper c)
  principal-isMacNeilleCut c .IsMacNeilleCut.lower-is-lowerBounds x .fst x≤c y c≤y =
    ≤-trans x c y x≤c c≤y
  principal-isMacNeilleCut c .IsMacNeilleCut.lower-is-lowerBounds x .snd x≤all =
    x≤all c (≤-refl c)
  principal-isMacNeilleCut c .IsMacNeilleCut.upper-is-upperBounds y .fst c≤y x x≤c =
    ≤-trans x c y x≤c c≤y
  principal-isMacNeilleCut c .IsMacNeilleCut.upper-is-upperBounds y .snd all≤y =
    all≤y c (≤-refl c)

  principalMacNeilleCut : Carrier → MacNeilleCut ℓ' ℓ'
  principalMacNeilleCut c .lower = principalLower c
  principalMacNeilleCut c .upper = principalUpper c
  principalMacNeilleCut c .isMacNeilleCut = principal-isMacNeilleCut c


  record RepresentsMacNeilleCut
      (C : MacNeilleCut ℓᴸ ℓᵁ) (c : Carrier) :
      Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓᴸ ℓᵁ))) where
    no-eta-equality

    field
      represents-lower : lower C ⇔ᵖ principalLower c
      represents-upper : upper C ⇔ᵖ principalUpper c

  isPropRepresentsMacNeilleCut :
    (C : MacNeilleCut ℓᴸ ℓᵁ) (c : Carrier) →
    isProp (RepresentsMacNeilleCut C c)
  isPropRepresentsMacNeilleCut C c R S i .RepresentsMacNeilleCut.represents-lower =
    isProp⇔ᵖ (lower C) (principalLower c)
      (R .RepresentsMacNeilleCut.represents-lower)
      (S .RepresentsMacNeilleCut.represents-lower)
      i
  isPropRepresentsMacNeilleCut C c R S i .RepresentsMacNeilleCut.represents-upper =
    isProp⇔ᵖ (upper C) (principalUpper c)
      (R .RepresentsMacNeilleCut.represents-upper)
      (S .RepresentsMacNeilleCut.represents-upper)
      i


  isPrincipalMacNeilleCut :
    MacNeilleCut ℓᴸ ℓᵁ →
    Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓᴸ ℓᵁ)))
  isPrincipalMacNeilleCut C =
    Σ[ c ∈ Carrier ] RepresentsMacNeilleCut C c

  isPropIsPrincipalMacNeilleCut :
    (C : MacNeilleCut ℓᴸ ℓᵁ) →
    isProp (isPrincipalMacNeilleCut C)
  isPropIsPrincipalMacNeilleCut C (c , c-rep) (d , d-rep) =
    Σ≡Prop
      (isPropRepresentsMacNeilleCut C)
      (is-antisym c d c≤d d≤c)
    where
    c∈L : c ∈ lower C
    c∈L =
      c-rep .RepresentsMacNeilleCut.represents-lower c .snd
        (≤-refl c)

    d∈L : d ∈ lower C
    d∈L =
      d-rep .RepresentsMacNeilleCut.represents-lower d .snd
        (≤-refl d)

    c≤d : c ≤P d
    c≤d =
      d-rep .RepresentsMacNeilleCut.represents-lower c .fst c∈L

    d≤c : d ≤P c
    d≤c =
      c-rep .RepresentsMacNeilleCut.represents-lower d .fst d∈L

  isLowerInhabited :
    MacNeilleCut ℓᴸ ℓᵁ →
    Type (ℓ-max ℓ ℓᴸ)
  isLowerInhabited C =
    ∥ Σ[ x ∈ Carrier ] x ∈ lower C ∥₁

  isUpperInhabited :
    MacNeilleCut ℓᴸ ℓᵁ →
    Type (ℓ-max ℓ ℓᵁ)
  isUpperInhabited C =
    ∥ Σ[ x ∈ Carrier ] x ∈ upper C ∥₁

  isBoundedMacNeilleCut :
    MacNeilleCut ℓᴸ ℓᵁ →
    Type (ℓ-max ℓ (ℓ-max ℓᴸ ℓᵁ))
  isBoundedMacNeilleCut C =
    isLowerInhabited C × isUpperInhabited C

  isMacNeilleComplete :
    (ℓᴸ ℓᵁ : Level) →
    Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓᴸ ℓᵁ))))
  -- Full MacNeille completeness: every MacNeille cut is principal
  isMacNeilleComplete ℓᴸ ℓᵁ =
    (C : MacNeilleCut ℓᴸ ℓᵁ) → isPrincipalMacNeilleCut C

  isPropIsMacNeilleComplete :
    (ℓᴸ ℓᵁ : Level) →
    isProp (isMacNeilleComplete ℓᴸ ℓᵁ)
  isPropIsMacNeilleComplete ℓᴸ ℓᵁ =
    isPropΠ λ C → isPropIsPrincipalMacNeilleCut C

  isBoundedMacNeilleComplete :
    (ℓᴸ ℓᵁ : Level) →
    Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓᴸ ℓᵁ))))
  -- Bounded MacNeille completeness: every inhabited two-sided MacNeille cut
  -- is principal
  isBoundedMacNeilleComplete ℓᴸ ℓᵁ =
    (C : MacNeilleCut ℓᴸ ℓᵁ) →
    isBoundedMacNeilleCut C →
    isPrincipalMacNeilleCut C

  isPropIsBoundedMacNeilleComplete :
    (ℓᴸ ℓᵁ : Level) →
    isProp (isBoundedMacNeilleComplete ℓᴸ ℓᵁ)
  isPropIsBoundedMacNeilleComplete ℓᴸ ℓᵁ =
    isPropΠ2 λ C _ → isPropIsPrincipalMacNeilleCut C
