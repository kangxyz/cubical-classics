{-

Archimedean property for constructive Dedekind completions

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Completions.DedekindCompletion.Archimedean where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

import Constructive.Algebra.OrderedCommRing.Archimedean as OrderedArch
import Constructive.Algebra.OrderedCommRing.Properties as OrderedProperties
open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedean
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.Analysis.Completions.DedekindCompletion.Base
open import Constructive.Analysis.Completions.DedekindCompletion.Order
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Addition
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Order
import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Structures as CompletionOrderedCommRing

private
  variable
    ℓ ℓ' ℓᴾ : Level


module OrderedCommRingArchimedean
  (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') {ℓᴾ : Level} where

  baseField : LinearlyOrderedField ℓ ℓ'
  baseField = 𝒜 .fst

  private
    K : Type ℓ
    K = baseField .fst .fst .fst

  open CompletionBase baseField
  module CutOrder = CompletionOrder baseField
  open CutOrder
    using
      ( K→<-pres ; upper→<K ; lower→K< ; principalUpper→K<
      )
    renaming
      ( _<_ to _<D_
      ; <-trans to <D-trans
      )
  open LinearlyOrderedFieldStr baseField
    using
      ( 0r ; _+_ ; _<_ ; _>_
      ; middle ; middle>l ; middle<r
      ; <-trans ; +-Pres< ; +-rPos→>
      )
    renaming
      ( _⋆_ to _⋆K_
      ; 1⋆q≡q to 1⋆Kq≡q
      ; sucn⋆q≡n⋆q+q to sucn⋆Kq≡n⋆Kq+q
      )

  open Addition 𝒜 {ℓᴾ}
  open OrderProperties 𝒜 {ℓᴾ} using (∃lower>0)
  open CompletionOrderedCommRing.OrderedCommRingStructure 𝒜 {ℓᴾ}
    using (DedekindCompletionOrderedCommRing)

  module DedekindOrdered =
    OrderedProperties.OrderedCommRingTheory DedekindCompletionOrderedCommRing

  _⋆D_ : ℕ → DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ
  _⋆D_ = DedekindOrdered._⋆_

  infixl 7 _⋆D_

  principal-add-below-plus :
    (a b : K) (x y : DedekindCompletion ℓᴾ) →
    K→𝔻 ℓᴾ a <D x →
    K→𝔻 ℓᴾ b <D y →
    K→𝔻 ℓᴾ (a + b) <D (x +𝔻 y)
  principal-add-below-plus a b x y =
    Prop.rec2 squash₁
      (λ (r , r∈Ua , r∈Lx) (s , s∈Ub , s∈Ly) →
        let
          a<r : a < r
          a<r = principalUpper→K< r a r∈Ua

          b<s : b < s
          b<s = principalUpper→K< s b s∈Ub

          a+b<r+s : a + b < r + s
          a+b<r+s = +-Pres< a<r b<s

          q : K
          q = middle (a + b) (r + s)
        in
        ∣ q
        , lift (middle>l a+b<r+s)
        , ∣ r , s , r∈Lx , s∈Ly , middle<r a+b<r+s ∣₁
        ∣₁)

  principal-scalar-below :
    (n : ℕ) (δ : K) (ε : DedekindCompletion ℓᴾ) →
    K→𝔻 ℓᴾ δ <D ε →
    K→𝔻 ℓᴾ (suc n ⋆K δ) <D (suc n ⋆D ε)
  principal-scalar-below zero δ ε δ<ε =
    subst2 _<D_
      (cong (K→𝔻 ℓᴾ) (sym (1⋆Kq≡q δ)))
      (sym (DedekindOrdered.1⋆q≡q ε))
      δ<ε
  principal-scalar-below (suc n) δ ε δ<ε =
    subst2 _<D_
      (cong (K→𝔻 ℓᴾ) (sym (sucn⋆Kq≡n⋆Kq+q (suc n) δ)))
      (sym (DedekindOrdered.sucn⋆q≡n⋆q+q (suc n) ε))
      (principal-add-below-plus
        (suc n ⋆K δ) δ
        (suc n ⋆D ε) ε
        (principal-scalar-below n δ ε δ<ε)
        δ<ε)

  isArchimedean∥∥DedekindCompletion :
    OrderedArch.isArchimedean∥∥ DedekindCompletionOrderedCommRing
  isArchimedean∥∥DedekindCompletion x ε ε>0 =
    Prop.rec2 squash₁
      (λ (u , u∈Ux) (δ , 0<δ , δ∈Lε) →
        let
          n : ℕ
          n = 𝒜 .snd u δ 0<δ .fst

          u<nδ : u < n ⋆K δ
          u<nδ = 𝒜 .snd u δ 0<δ .snd

          u<sucnδ : u < suc n ⋆K δ
          u<sucnδ =
            <-trans u<nδ
              (subst (n ⋆K δ <_)
                (sym (sucn⋆Kq≡n⋆Kq+q n δ))
                (+-rPos→> 0<δ))

          x<Ku : x <D K→𝔻 ℓᴾ u
          x<Ku = upper→<K x u u∈Ux

          Ku<Ksucnδ : K→𝔻 ℓᴾ u <D K→𝔻 ℓᴾ (suc n ⋆K δ)
          Ku<Ksucnδ = K→<-pres u (suc n ⋆K δ) u<sucnδ

          Kδ<ε : K→𝔻 ℓᴾ δ <D ε
          Kδ<ε = lower→K< ε δ δ∈Lε

          Ksucnδ<sucnε :
            K→𝔻 ℓᴾ (suc n ⋆K δ) <D (suc n ⋆D ε)
          Ksucnδ<sucnε = principal-scalar-below n δ ε Kδ<ε
        in
        ∣ suc n
        , <D-trans x (K→𝔻 ℓᴾ u) (suc n ⋆D ε)
            x<Ku
            (<D-trans
              (K→𝔻 ℓᴾ u)
              (K→𝔻 ℓᴾ (suc n ⋆K δ))
              (suc n ⋆D ε)
              Ku<Ksucnδ
              Ksucnδ<sucnε)
        ∣₁)
      (CompletionBase.upper-inhabited {𝒦 = 𝒜 .fst} x)
      (∃lower>0 ε ε>0)


open OrderedCommRingArchimedean public
  using (isArchimedean∥∥DedekindCompletion)
