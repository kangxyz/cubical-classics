{-

SIP for strictly ordered commutative rings

-}
{-# OPTIONS --safe --lossy-unification #-}
module Classical.Algebra.StrictlyOrderedCommRing.Univalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.SIP

import Cubical.Functions.Logic as L

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation

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
open import Cubical.Relation.Nullary

open import Classical.Algebra.StrictlyOrderedCommRing
open import Classical.Algebra.StrictlyOrderedCommRing.Base as StrictBase
  using    ()
  renaming (Trichotomy to Trichotomyᶜ ; lt to ltᶜ ; eq to eqᶜ ; gt to gtᶜ)
open import Classical.Algebra.StrictlyOrderedCommRing.Morphism

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    𝓡  : StrictlyOrderedCommRing ℓ   ℓ'
    𝓡' : StrictlyOrderedCommRing ℓ'' ℓ'''


{-

  Ordered commutative rings

-}

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


{-

  Equivalence of strictly ordered commutative rings

-}

open StrictlyOrderedCommRingHom

isStrictlyOrderedCommRingEquiv : StrictlyOrderedCommRingHom 𝓡 𝓡' → Type _
isStrictlyOrderedCommRingEquiv f = isEquiv (f .ring-hom .fst)


module _ (𝓡ᶜ : OrderedCommRing ℓ ℓ') where

  private
    R = 𝓡ᶜ .fst

  module Ord = OrderedCommRingStr (𝓡ᶜ .snd)

  isPropTrichotomyᶜ : (x y : R) → isProp (Trichotomyᶜ 𝓡ᶜ x y)
  isPropTrichotomyᶜ x y (ltᶜ x<y) (ltᶜ x<y') i = ltᶜ (Ord.is-prop-valued< x y x<y x<y' i)
  isPropTrichotomyᶜ x y (eqᶜ x≡y) (eqᶜ x≡y') i = eqᶜ (Ord.is-set x y x≡y x≡y' i)
  isPropTrichotomyᶜ x y (gtᶜ y<x) (gtᶜ y<x') i = gtᶜ (Ord.is-prop-valued< y x y<x y<x' i)
  isPropTrichotomyᶜ x y (ltᶜ x<y) (eqᶜ x≡y) =
    Empty.rec (Ord.is-irrefl y (subst (λ z → z Ord.< y) x≡y x<y))
  isPropTrichotomyᶜ x y (ltᶜ x<y) (gtᶜ y<x) =
    Empty.rec (Ord.is-asym x y x<y y<x)
  isPropTrichotomyᶜ x y (gtᶜ y<x) (eqᶜ x≡y) =
    Empty.rec (Ord.is-irrefl x (subst (λ z → z Ord.< x) (sym x≡y) y<x))
  isPropTrichotomyᶜ x y (gtᶜ y<x) (ltᶜ x<y) =
    Empty.rec (Ord.is-asym x y x<y y<x)
  isPropTrichotomyᶜ x y (eqᶜ x≡y) (ltᶜ x<y) =
    Empty.rec (Ord.is-irrefl y (subst (λ z → z Ord.< y) x≡y x<y))
  isPropTrichotomyᶜ x y (eqᶜ x≡y) (gtᶜ y<x) =
    Empty.rec (Ord.is-irrefl x (subst (λ z → z Ord.< x) (sym x≡y) y<x))


isPropStrictOrderStrOnOrderedCommRing :
  (𝓡ᶜ : OrderedCommRing ℓ ℓ') → isProp (StrictOrderStrOnOrderedCommRing 𝓡ᶜ)
isPropStrictOrderStrOnOrderedCommRing 𝓡ᶜ s t i .StrictOrderStrOnOrderedCommRing.trichotomy =
  isPropΠ2 (isPropTrichotomyᶜ 𝓡ᶜ) (s .StrictOrderStrOnOrderedCommRing.trichotomy) (t .StrictOrderStrOnOrderedCommRing.trichotomy) i


module _ {𝓡 𝓡' : StrictlyOrderedCommRing ℓ ℓ'}
  {f : StrictlyOrderedCommRingHom 𝓡 𝓡'}(isEquiv-f : isStrictlyOrderedCommRingEquiv f) where

  private
    𝓡ᵒ  = 𝓡 .fst
    𝓡'ᵒ = 𝓡' .fst

  module R  = OrderedCommRingStr (𝓡ᵒ .snd)
  module R' = OrderedCommRingStr (𝓡'ᵒ .snd)

  open StrictlyOrderedCommRingHom f
  open StrictlyOrderedCommRingHomStr f
  open StrictlyOrderedCommRingStr 𝓡
    using    (Diff>0→<ᶜ ; <ᶜ→Diff>0)
  open StrictlyOrderedCommRingStr 𝓡'
    using    ()
    renaming (Diff>0→<ᶜ to Diff>0→<ᶜ' ; <ᶜ→Diff>0 to <ᶜ→Diff>0')
  open IsCommRingHom (f .ring-hom .snd)

  <ᶜPres : (x y : 𝓡ᵒ .fst) → x R.< y → f .ring-hom .fst x R'.< f .ring-hom .fst y
  <ᶜPres x y x<y = Diff>0→<ᶜ' (homPres< x y (<ᶜ→Diff>0 x<y))

  <ᶜRefl : (x y : 𝓡ᵒ .fst) → f .ring-hom .fst x R'.< f .ring-hom .fst y → x R.< y
  <ᶜRefl x y fx<fy = Diff>0→<ᶜ (homRefl< x y (<ᶜ→Diff>0' fx<fy))

  ≤ᶜPres : (x y : 𝓡ᵒ .fst) → x R.≤ y → f .ring-hom .fst x R'.≤ f .ring-hom .fst y
  ≤ᶜPres x y x≤y =
    invEq (R'.≤≃¬> (f .ring-hom .fst x) (f .ring-hom .fst y)) λ fy<fx →
      equivFun (R.≤≃¬> x y) x≤y (<ᶜRefl y x fy<fx)

  ≤ᶜRefl : (x y : 𝓡ᵒ .fst) → f .ring-hom .fst x R'.≤ f .ring-hom .fst y → x R.≤ y
  ≤ᶜRefl x y fx≤fy =
    invEq (R.≤≃¬> x y) λ y<x →
      equivFun (R'.≤≃¬> (f .ring-hom .fst x) (f .ring-hom .fst y)) fx≤fy (<ᶜPres y x y<x)

  orderedCommRingEquiv : OrderedCommRingEquiv 𝓡ᵒ 𝓡'ᵒ
  orderedCommRingEquiv .fst = f .ring-hom .fst , isEquiv-f
  orderedCommRingEquiv .snd .IsOrderedCommRingEquiv.pres0 = pres0
  orderedCommRingEquiv .snd .IsOrderedCommRingEquiv.pres1 = pres1
  orderedCommRingEquiv .snd .IsOrderedCommRingEquiv.pres+ = pres+
  orderedCommRingEquiv .snd .IsOrderedCommRingEquiv.pres· = pres·
  orderedCommRingEquiv .snd .IsOrderedCommRingEquiv.pres- = pres-
  orderedCommRingEquiv .snd .IsOrderedCommRingEquiv.pres< x y =
    propBiimpl→Equiv (R.is-prop-valued< x y) (R'.is-prop-valued< _ _) (<ᶜPres x y) (<ᶜRefl x y)
  orderedCommRingEquiv .snd .IsOrderedCommRingEquiv.pres≤ x y =
    propBiimpl→Equiv (R.is-prop-valued≤ x y) (R'.is-prop-valued≤ _ _) (≤ᶜPres x y) (≤ᶜRefl x y)

  path-orderedCommRing : 𝓡ᵒ ≡ 𝓡'ᵒ
  path-orderedCommRing = uaOrderedCommRing orderedCommRingEquiv

  uaStrictlyOrderedCommRing : 𝓡 ≡ 𝓡'
  uaStrictlyOrderedCommRing i .fst = path-orderedCommRing i
  uaStrictlyOrderedCommRing i .snd =
    isProp→PathP (λ i → isPropStrictOrderStrOnOrderedCommRing (path-orderedCommRing i)) (𝓡 .snd) (𝓡' .snd) i
