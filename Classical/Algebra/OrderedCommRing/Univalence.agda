{-

SIP for ordered commutative rings

-}
{-# OPTIONS --safe --lossy-unification #-}
module Classical.Algebra.OrderedCommRing.Univalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP

import Cubical.Functions.Logic as L

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Relation.Nullary

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe
open import Cubical.Reflection.RecordEquiv

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Univalence
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.StrictOrder

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level


unquoteDecl IsOrderedCommRingIsoΣ =
  declareRecordIsoΣ IsOrderedCommRingIsoΣ (quote IsOrderedCommRing)

isPropIsOrderedCommRing :
  {R : Type ℓ}
  (0r 1r : R)
  (_+_ _·_ : R → R → R)
  (-_ : R → R)
  (_<_ _≤_ : R → R → Type ℓ')
  → isProp (IsOrderedCommRing 0r 1r _+_ _·_ -_ _<_ _≤_)
isPropIsOrderedCommRing 0r 1r _+_ _·_ -_ _<_ _≤_ =
  isOfHLevelRetractFromIso 1 IsOrderedCommRingIsoΣ
  (
    isPropΣ (isPropIsCommRing 0r 1r _+_ _·_ -_) λ isCommRing →
    isPropΣ (isPropIsPseudolattice _≤_) λ isPseudolattice →
    isPropΣ (isPropIsStrictOrder _<_) λ isStrictOrder →
    let isProp≤ = IsPseudolattice.is-prop-valued isPseudolattice
        isProp< = IsStrictOrder.is-prop-valued isStrictOrder
    in
    isPropΣ (isPropΠ3 λ x y _ → isProp≤ x y) λ <-≤-weaken →
    isPropΣ (isPropΠ2 λ x y → isOfHLevel≃ 1 (isProp≤ x y) (isProp¬ (y < x))) λ ≤≃¬> →
    isPropΣ (isPropΠ4 λ x y z _ → isProp≤ (x + z) (y + z)) λ +MonoR≤ →
    isPropΣ (isPropΠ4 λ x y z _ → isProp< (x + z) (y + z)) λ +MonoR< →
    isPropΣ (isPropΠ3 λ x y _ → squash₁) λ posSum→pos∨pos →
    isPropΣ (isPropΠ5 λ x y z _ _ → isProp< x z) λ <-≤-trans →
    isPropΣ (isPropΠ5 λ x y z _ _ → isProp< x z) λ ≤-<-trans →
    isPropΣ (isPropΠ5 λ x y z _ _ → isProp≤ (x · z) (y · z)) λ ·MonoR≤ →
    isPropΣ (isPropΠ5 λ x y z _ _ → isProp< (x · z) (y · z)) λ ·MonoR< →
    isProp< 0r 1r
  )


record IsOrderedCommRingEquiv
  {A : Type ℓ} {B : Type ℓ''}
  (M : OrderedCommRingStr ℓ' A)
  (e : A ≃ B)
  (N : OrderedCommRingStr ℓ''' B)
  : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓ''')) where

  private
    module M = OrderedCommRingStr M
    module N = OrderedCommRingStr N

  field
    pres0 : equivFun e M.0r ≡ N.0r
    pres1 : equivFun e M.1r ≡ N.1r
    pres+ : (x y : A) → equivFun e (x M.+ y) ≡ equivFun e x N.+ equivFun e y
    pres· : (x y : A) → equivFun e (x M.· y) ≡ equivFun e x N.· equivFun e y
    pres- : (x : A) → equivFun e (M.- x) ≡ N.- equivFun e x
    pres< : (x y : A) → (x M.< y) ≃ (equivFun e x N.< equivFun e y)
    pres≤ : (x y : A) → (x M.≤ y) ≃ (equivFun e x N.≤ equivFun e y)


OrderedCommRingEquiv :
  OrderedCommRing ℓ ℓ' →
  OrderedCommRing ℓ'' ℓ''' →
  Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓ'''))
OrderedCommRingEquiv M N =
  Σ[ e ∈ M .fst ≃ N .fst ] IsOrderedCommRingEquiv (M .snd) e (N .snd)


𝒮ᴰ-OrderedCommRing : DUARel (𝒮-Univ ℓ) (OrderedCommRingStr ℓ') (ℓ-max ℓ ℓ')
𝒮ᴰ-OrderedCommRing =
  𝒮ᴰ-Record (𝒮-Univ _) IsOrderedCommRingEquiv
    (fields:
      data[ 0r ∣ null ∣ pres0 ]
      data[ 1r ∣ null ∣ pres1 ]
      data[ _+_ ∣ bin ∣ pres+ ]
      data[ _·_ ∣ bin ∣ pres· ]
      data[ -_ ∣ autoDUARel _ _ ∣ pres- ]
      data[ _<_ ∣ autoDUARel _ _ ∣ pres< ]
      data[ _≤_ ∣ autoDUARel _ _ ∣ pres≤ ]
      prop[ isOrderedCommRing ∣ (λ _ _ → isPropIsOrderedCommRing _ _ _ _ _ _ _) ])
  where
  open OrderedCommRingStr
  open IsOrderedCommRingEquiv
  null = autoDUARel (𝒮-Univ _) (λ A → A)
  bin = autoDUARel (𝒮-Univ _) (λ A → A → A → A)


OrderedCommRingPath : (M N : OrderedCommRing ℓ ℓ') → OrderedCommRingEquiv M N ≃ (M ≡ N)
OrderedCommRingPath = ∫ 𝒮ᴰ-OrderedCommRing .UARel.ua

uaOrderedCommRing : {M N : OrderedCommRing ℓ ℓ'} → OrderedCommRingEquiv M N → M ≡ N
uaOrderedCommRing {M = M} {N = N} = equivFun (OrderedCommRingPath M N)
