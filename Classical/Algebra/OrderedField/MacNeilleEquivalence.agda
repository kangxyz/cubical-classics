{-

Classical comparison with bounded MacNeille completeness

For ordered fields, the bounded cut formulation matches the powerset
supremum principle

The full cut formulation also contains endpoint cuts, so the comparison uses
the bounded form

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.MacNeilleEquivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Relation.Binary.Order.Poset

open import Classical.Axioms
open import Classical.Preliminary.Logic
open import Classical.Foundations.Powerset
import Classical.Foundations.Powerset as Powerset
open import Classical.Algebra.OrderedField.Extremum
open import Classical.Algebra.OrderedField.Completeness

import Constructive.Algebra.Order.MacNeilleCompleteness as ConstructiveMacNeilleCompleteness
open import Constructive.Algebra.LinearlyOrderedField
import Constructive.Foundations.Powerset as CP

private
  variable
    ℓ ℓ' ℓᴸ ℓᵁ : Level


module MacNeilleEquivalence ⦃ 🤖 : Oracle ⦄ (𝒦 : LinearlyOrderedField ℓ ℓ') where

  open Oracle 🤖
  open LinearlyOrderedFieldStr 𝒦
  open Extremum 𝒦
  open Supremum
  open MacNeilleCompleteOrderedField 𝒦

  private
    K : Type ℓ
    K = 𝒦 .fst .fst .fst

  _∈ℙ_ : K → ℙ K → Type
  x ∈ℙ A = Powerset._∈_ x A

  infix 4 _∈ℙ_

  K≤Poset : Poset ℓ ℓ'
  K≤Poset =
    poset K _≤_
      (isposet
        is-set
        (λ x y → isProp≤ {x = x} {y = y})
        (λ x → ≤-refl {x = x} refl)
        (λ x y z → ≤-trans {x = x} {y = y} {z = z})
        (λ x y x≤y y≤x → ≤-asym {x = x} {y = y} x≤y y≤x))

  module CM = ConstructiveMacNeilleCompleteness.MacNeilleCompleteness K≤Poset


  classical→boundedMacNeilleComplete :
    isMacNeilleComplete →
    CM.isBoundedMacNeilleComplete ℓᴸ ℓᵁ
  classical→boundedMacNeilleComplete getSup C (lower-inhab , upper-inhab) =
    s , represents
    where
    lower-sub : ℙ K
    lower-sub = specify (CM.lower C)

    lower-sub-inhab : isInhabited lower-sub
    lower-sub-inhab =
      Prop.map
        (λ (x , x∈L) → x , Inhab→∈ (CM.lower C) x∈L)
        lower-inhab

    lower-sub-bounded : isUpperBounded lower-sub
    lower-sub-bounded =
      Prop.map bound-from-upper upper-inhab
      where
      bound-from-upper :
        Σ[ u ∈ K ] u CP.∈ CM.upper C →
        Σ[ u ∈ K ] ((x : K) → x ∈ℙ lower-sub → x ≤ u)
      bound-from-upper (u , u∈U) =
        u ,
        λ x x∈lower-sub →
          CM.MacNeilleCut.upper-is-upperBounds C u .fst u∈U x
            (∈→Inhab (CM.lower C) x∈lower-sub)

    lower-sup : Supremum lower-sub
    lower-sup = getSup lower-sub-inhab lower-sub-bounded

    s : K
    s = lower-sup .sup

    lower→≤s : (x : K) → x CP.∈ CM.lower C → x ≤ s
    lower→≤s x x∈L =
      lower-sup .bound x (Inhab→∈ (CM.lower C) x∈L)

    ≤s→lower : (x : K) → x ≤ s → x CP.∈ CM.lower C
    ≤s→lower x x≤s =
      CM.MacNeilleCut.lower-is-lowerBounds C x .snd
        λ u u∈U →
          ≤-trans {x = x} {y = s} {z = u}
            x≤s
            (lower-sup .least u
              λ l l∈lower-sub →
                CM.MacNeilleCut.upper-is-upperBounds C u .fst u∈U l
                  (∈→Inhab (CM.lower C) l∈lower-sub))

    upper→s≤ : (u : K) → u CP.∈ CM.upper C → s ≤ u
    upper→s≤ u u∈U =
      lower-sup .least u
        λ l l∈lower-sub →
          CM.MacNeilleCut.upper-is-upperBounds C u .fst u∈U l
            (∈→Inhab (CM.lower C) l∈lower-sub)

    s≤→upper : (u : K) → s ≤ u → u CP.∈ CM.upper C
    s≤→upper u s≤u =
      CM.MacNeilleCut.upper-is-upperBounds C u .snd
        λ l l∈L →
          ≤-trans {x = l} {y = s} {z = u}
            (lower→≤s l l∈L)
            s≤u

    represents : CM.RepresentsMacNeilleCut C s
    represents .CM.RepresentsMacNeilleCut.represents-lower x =
      lower→≤s x , ≤s→lower x
    represents .CM.RepresentsMacNeilleCut.represents-upper u =
      upper→s≤ u , s≤→upper u


  upperBoundPred : ℙ K → CM.Pred (ℓ-max ℓ ℓ')
  upperBoundPred A u =
    ((x : K) → x ∈ℙ A → x ≤ u) ,
    isPropΠ2 λ x _ → isProp≤ {x = x} {y = u}

  lowerHullPred : ℙ K → CM.Pred (ℓ-max ℓ ℓ')
  lowerHullPred A x =
    ((u : K) → u CP.∈ upperBoundPred A → x ≤ u) ,
    isPropΠ2 λ u _ → isProp≤ {x = x} {y = u}

  powersetMacNeilleCut : ℙ K → CM.MacNeilleCut (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  powersetMacNeilleCut A .CM.MacNeilleCut.lower =
    lowerHullPred A
  powersetMacNeilleCut A .CM.MacNeilleCut.upper =
    upperBoundPred A
  powersetMacNeilleCut A .CM.MacNeilleCut.isMacNeilleCut
    .CM.IsMacNeilleCut.lower-is-lowerBounds x .fst x∈lower u u∈upper =
      x∈lower u u∈upper
  powersetMacNeilleCut A .CM.MacNeilleCut.isMacNeilleCut
    .CM.IsMacNeilleCut.lower-is-lowerBounds x .snd x≤upper =
      x≤upper
  powersetMacNeilleCut A .CM.MacNeilleCut.isMacNeilleCut
    .CM.IsMacNeilleCut.upper-is-upperBounds u .fst u∈upper x x∈lower =
      x∈lower u u∈upper
  powersetMacNeilleCut A .CM.MacNeilleCut.isMacNeilleCut
    .CM.IsMacNeilleCut.upper-is-upperBounds u .snd lower≤u x x∈A =
      lower≤u x (λ v v∈upper → v∈upper x x∈A)

  powersetCut-bounded :
    (A : ℙ K) →
    isInhabited A →
    isUpperBounded A →
    CM.isBoundedMacNeilleCut (powersetMacNeilleCut A)
  powersetCut-bounded A inhab upper-bounded =
    lower-inhab , upper-bounded
    where
    lower-inhab :
      ∥ Σ[ x ∈ K ] x CP.∈ CM.lower (powersetMacNeilleCut A) ∥₁
    lower-inhab =
      Prop.map
        (λ (a , a∈A) → a , λ u u∈upper → u∈upper a a∈A)
        inhab

  boundedMacNeilleComplete→classical :
    CM.isBoundedMacNeilleComplete (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ') →
    isMacNeilleComplete
  boundedMacNeilleComplete→classical getPrincipal {A = A} inhab upper-bounded =
    supA
    where
    C : CM.MacNeilleCut (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
    C = powersetMacNeilleCut A

    principal : CM.isPrincipalMacNeilleCut C
    principal =
      getPrincipal C (powersetCut-bounded A inhab upper-bounded)

    s : K
    s = principal .fst

    represents : CM.RepresentsMacNeilleCut C s
    represents = principal .snd

    A⊆lower : (x : K) → x ∈ℙ A → x CP.∈ CM.lower C
    A⊆lower x x∈A u u∈upper =
      u∈upper x x∈A

    supA : Supremum A
    supA .sup = s
    supA .bound x x∈A =
      CM.RepresentsMacNeilleCut.represents-lower represents x .fst
        (A⊆lower x x∈A)
    supA .least u u-bound =
      CM.RepresentsMacNeilleCut.represents-upper represents u .fst
        u-bound

  classical↔boundedMacNeilleComplete :
    (isMacNeilleComplete →
      CM.isBoundedMacNeilleComplete (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ'))
    ×
    (CM.isBoundedMacNeilleComplete (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ') →
      isMacNeilleComplete)
  classical↔boundedMacNeilleComplete =
    classical→boundedMacNeilleComplete ,
    boundedMacNeilleComplete→classical

  classical≃boundedMacNeilleComplete :
    isMacNeilleComplete
      ≃
    CM.isBoundedMacNeilleComplete (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  classical≃boundedMacNeilleComplete =
    propBiimpl→Equiv
      isPropIsMacNeilleComplete
      (CM.isPropIsBoundedMacNeilleComplete (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ'))
      classical→boundedMacNeilleComplete
      boundedMacNeilleComplete→classical


open MacNeilleEquivalence public
  using
    ( K≤Poset
    ; classical→boundedMacNeilleComplete
    ; boundedMacNeilleComplete→classical
    ; classical↔boundedMacNeilleComplete
    ; classical≃boundedMacNeilleComplete
    ; powersetMacNeilleCut
    )
