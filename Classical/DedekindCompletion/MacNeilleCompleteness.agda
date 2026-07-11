{-

MacNeille completeness of constructive Dedekind completions under Oracle

Classical powerset suprema are obtained from located completion-valued cuts.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Classical.DedekindCompletion.MacNeilleCompleteness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.Data.Unit using (tt*)
open import Cubical.Data.Bool using (Bool ; Dec→Bool ; Bool→Type*)
open import Cubical.Data.Bool.Properties using (isPropBool→Type*)
open import Cubical.Relation.Nullary using (yes ; no ; ¬_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Field
open import Cubical.Algebra.OrderedCommRing

open import Classical.Axioms
open import Classical.Foundations.Powerset
import Classical.Foundations.Powerset as Powerset
open import Classical.Algebra.OrderedField.Extremum
open import Classical.Algebra.OrderedField.Completeness

import Constructive.Algebra.LinearlyOrderedCommRing as LinearOCR
import Constructive.Algebra.LinearlyOrderedField as LinearOF
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.Algebra.LinearlyOrderedField.Archimedean
open import Constructive.Analysis.Completions.DedekindCompletion.Base
open import Constructive.Analysis.Completions.DedekindCompletion.Order
open import Constructive.Analysis.Completions.DedekindCompletion.Completeness
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Addition
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Multiplication
open import Constructive.Analysis.Completions.DedekindCompletion.Arithmetic.Structures

private
  variable
    ℓ ℓ' ℓᴾ ℓ₀ ℓ₁ : Level


_∈ℙ_ : ⦃ _ : Oracle ⦄ → {X : Type ℓ} → X → ℙ X → Type
x ∈ℙ A = Powerset._∈_ x A

infix 6 _∈ℙ_


module ClassicalResize ⦃ 🤖 : Oracle ⦄ where
  open Oracle 🤖

  small : hProp ℓ₀ → hProp ℓ₁
  small P = Bool→Type* (Dec→Bool (decide (P .snd))) , isPropBool→Type*

  to-small : (P : hProp ℓ₀) → P .fst → small {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} P .fst
  to-small P p with decide (P .snd)
  ... | yes _ = tt*
  ... | no ¬p = Empty.rec (¬p p)

  from-small : (P : hProp ℓ₀) → small {ℓ₀ = ℓ₀} {ℓ₁ = ℓ₁} P .fst → P .fst
  from-small P p with decide (P .snd)
  ... | yes q = q
  ... | no ¬p = Empty.rec* p


module CompletionOrderAliases
    (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ')
    {ℓᴾ : Level} where

  private
    baseField = 𝒜 .fst

  module RawOrder = CompletionOrder baseField

  _≤_ = RawOrder._≤_ {ℓᴾ = ℓᴾ}
  _<_ = RawOrder._<_ {ℓᴾ = ℓᴾ}
  _#_ = RawOrder._#_ {ℓᴾ = ℓᴾ}

  infix 4 _≤_ _<_ _#_

  isProp< = RawOrder.isProp< {ℓᴾ = ℓᴾ}
  ≤-antisym = RawOrder.≤-antisym {ℓᴾ = ℓᴾ}
  ¬>→≤ = RawOrder.¬>→≤ {ℓᴾ = ℓᴾ}
  <-irrefl = RawOrder.<-irrefl {ℓᴾ = ℓᴾ}
  <-trans = RawOrder.<-trans {ℓᴾ = ℓᴾ}
  <≤-asym = RawOrder.<≤-asym {ℓᴾ = ℓᴾ}
  ≤-trans = RawOrder.≤-trans {ℓᴾ = ℓᴾ}
  <→≤ = RawOrder.<→≤ {ℓᴾ = ℓᴾ}
  lower→K< = RawOrder.lower→K< {ℓᴾ = ℓᴾ}
  upper→<K = RawOrder.upper→<K {ℓᴾ = ℓᴾ}
  basis-between = RawOrder.basis-between {ℓᴾ = ℓᴾ}
  #-irrefl = RawOrder.#-irrefl {ℓᴾ = ℓᴾ}


module LinearlyOrderedFieldStructure
    ⦃ 🤖 : Oracle ⦄
    (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ')
    {ℓᴾ : Level} where

  open Oracle 🤖

  baseField : LinearlyOrderedField ℓ ℓ'
  baseField = 𝒜 .fst

  private
    ℓ≤ : Level
    ℓ≤ = ℓ-max ℓ (ℓ-max ℓ' ℓᴾ)

    ℓ𝔻 : Level
    ℓ𝔻 = ℓ-suc ℓ≤

  module Base = CompletionBase baseField
  module CO = CompletionOrderAliases 𝒜 {ℓᴾ}
  module AdditionAtLevel = Addition 𝒜 {ℓᴾ}
  module Mul = Multiplication 𝒜 {ℓᴾ}
  module CR = CommRingStructure 𝒜 {ℓᴾ}
  module OCR = OrderedCommRingStructure 𝒜 {ℓᴾ}
  module OHF = OrderedHeytingFieldStructure 𝒜 {ℓᴾ}

  open Base using (DedekindCompletion)
  open AdditionAtLevel using (0𝔻 ; 1𝔻)
  open Mul using (_*𝔻_)

  trichotomy :
    (x y : DedekindCompletion ℓᴾ) →
    LinearOCR.Trichotomy OCR.DedekindCompletionOrderedCommRing x y
  trichotomy x y with decide (CO.isProp< x y)
  ... | yes x<y = LinearOCR.lt x<y
  ... | no ¬x<y with decide (CO.isProp< y x)
  ... | yes y<x = LinearOCR.gt y<x
  ... | no ¬y<x =
    LinearOCR.eq
      (CO.≤-antisym x y
        (CO.¬>→≤ x y ¬y<x)
        (CO.¬>→≤ y x ¬x<y))

  DedekindCompletionLinearlyOrderedCommRing :
    LinearOCR.LinearlyOrderedCommRing ℓ𝔻 ℓ≤
  DedekindCompletionLinearlyOrderedCommRing =
    OCR.DedekindCompletionOrderedCommRing ,
    LinearOCR.linearorderstr trichotomy

  #from≠0 :
    (x : DedekindCompletion ℓᴾ) →
    ¬ x ≡ 0𝔻 →
    CO._#_ x 0𝔻
  #from≠0 x x≢0 with trichotomy x 0𝔻
  ... | LinearOCR.lt x<0 = Sum.inl x<0
  ... | LinearOCR.gt 0<x = Sum.inr 0<x
  ... | LinearOCR.eq x≡0 = Empty.rec (x≢0 x≡0)

  hasInverse :
    (x : DedekindCompletion ℓᴾ) →
    ¬ x ≡ 0𝔻 →
    Σ[ y ∈ DedekindCompletion ℓᴾ ] x *𝔻 y ≡ 1𝔻
  hasInverse x x≢0 =
    OHF.inv# x (#from≠0 x x≢0)

  0≢1 : ¬ 0𝔻 ≡ 1𝔻
  0≢1 0≡1 =
    CO.#-irrefl 0𝔻
      (subst (λ x → CO._#_ 0𝔻 x) (sym 0≡1) OHF.0#1)

  DedekindCompletionIsFieldOnLinearlyOrderedCommRing :
    LinearOF.IsFieldOnLinearlyOrderedCommRing
      DedekindCompletionLinearlyOrderedCommRing
  DedekindCompletionIsFieldOnLinearlyOrderedCommRing =
    isfield
      (CommRingStr.isCommRing (CR.DedekindCompletionCommRing .snd))
      hasInverse
      0≢1

  DedekindCompletionLinearlyOrderedField :
    LinearOF.LinearlyOrderedField ℓ𝔻 ℓ≤
  DedekindCompletionLinearlyOrderedField =
    DedekindCompletionLinearlyOrderedCommRing ,
    DedekindCompletionIsFieldOnLinearlyOrderedCommRing


module MacNeilleCompleteness
    ⦃ 🤖 : Oracle ⦄
    (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ')
    {ℓᴾ : Level} where

  open Oracle 🤖
  open ClassicalResize ⦃ 🤖 ⦄

  baseField : LinearlyOrderedField ℓ ℓ'
  baseField = 𝒜 .fst

  private
    ℓ≤ : Level
    ℓ≤ = ℓ-max ℓ (ℓ-max ℓ' ℓᴾ)

    ℓ𝔻 : Level
    ℓ𝔻 = ℓ-suc ℓ≤

  module Base = CompletionBase baseField
  module CO = CompletionOrderAliases 𝒜 {ℓᴾ}
  module Complete = CompletionCompleteness 𝒜 ℓᴾ
  module LOF = LinearlyOrderedFieldStructure ⦃ 🤖 ⦄ 𝒜 {ℓᴾ}
  module M = MacNeilleCompleteOrderedField LOF.DedekindCompletionLinearlyOrderedField
  module E = Extremum LOF.DedekindCompletionLinearlyOrderedField
  open E.Supremum

  open Base using (DedekindCompletion ; K→𝔻)

  private
    D : Type ℓ𝔻
    D = DedekindCompletion ℓᴾ

  rawLower : ℙ D → D → hProp ℓ𝔻
  rawLower A x =
    ∥ Σ[ a ∈ D ] (a ∈ℙ A) × CO._<_ x a ∥₁ ,
    squash₁

  rawUpper : ℙ D → D → hProp ℓ𝔻
  rawUpper A x =
    ∥ Σ[ b ∈ D ] ((a : D) → a ∈ℙ A → CO._≤_ a b) × CO._<_ b x ∥₁ ,
    squash₁

  lowerPred : ℙ D → Complete.CompletionPred
  lowerPred A x = small (rawLower A x)

  upperPred : ℙ D → Complete.CompletionPred
  upperPred A x = small (rawUpper A x)

  lower→raw :
    (A : ℙ D) (x : D) →
    Complete._∈𝔻_ x (lowerPred A) →
    rawLower A x .fst
  lower→raw A x = from-small (rawLower A x)

  raw→lower :
    (A : ℙ D) (x : D) →
    rawLower A x .fst →
    Complete._∈𝔻_ x (lowerPred A)
  raw→lower A x = to-small (rawLower A x)

  upper→raw :
    (A : ℙ D) (x : D) →
    Complete._∈𝔻_ x (upperPred A) →
    rawUpper A x .fst
  upper→raw A x = from-small (rawUpper A x)

  raw→upper :
    (A : ℙ D) (x : D) →
    rawUpper A x .fst →
    Complete._∈𝔻_ x (upperPred A)
  raw→upper A x = to-small (rawUpper A x)

  powersetCut :
    (A : ℙ D) →
    isInhabited A →
    E.isUpperBounded A →
    Complete.CompletionValuedCut
  powersetCut A inhab bound .Complete.completionLower = lowerPred A
  powersetCut A inhab bound .Complete.completionUpper = upperPred A
  powersetCut A inhab bound .Complete.isCompletionValuedCut
    .Complete.IsCompletionValuedCut.completion-lower-inhabited =
    Prop.rec squash₁ step inhab
    where
    step :
      Σ[ a ∈ D ] a ∈ℙ A →
      ∥ Σ[ x ∈ D ] Complete._∈𝔻_ x (lowerPred A) ∥₁
    step (a , a∈A) =
      Prop.rec squash₁
        (λ (q , q∈La) →
          let x = K→𝔻 ℓᴾ q in
          ∣ x , raw→lower A x ∣ a , a∈A , CO.lower→K< a q q∈La ∣₁ ∣₁)
        (Base.DedekindCompletion.lower-inhabited a)
  powersetCut A inhab bound .Complete.isCompletionValuedCut
    .Complete.IsCompletionValuedCut.completion-upper-inhabited =
    Prop.rec squash₁ step bound
    where
    step :
      Σ[ b ∈ D ] ((a : D) → a ∈ℙ A → CO._≤_ a b) →
      ∥ Σ[ x ∈ D ] Complete._∈𝔻_ x (upperPred A) ∥₁
    step (b , b-bound) =
      Prop.rec squash₁
        (λ (q , q∈Ub) →
          let x = K→𝔻 ℓᴾ q in
          ∣ x , raw→upper A x ∣ b , b-bound , CO.upper→<K b q q∈Ub ∣₁ ∣₁)
        (Base.DedekindCompletion.upper-inhabited b)
  powersetCut A inhab bound .Complete.isCompletionValuedCut
    .Complete.IsCompletionValuedCut.completion-lower-closed =
    λ x y x<y y∈L →
      raw→lower A x
        (Prop.rec squash₁
          (λ (a , a∈A , y<a) →
            ∣ a , a∈A , CO.<-trans x y a x<y y<a ∣₁)
          (lower→raw A y y∈L))
  powersetCut A inhab bound .Complete.isCompletionValuedCut
    .Complete.IsCompletionValuedCut.completion-upper-closed =
    λ x y x<y x∈U →
      raw→upper A y
        (Prop.rec squash₁
          (λ (b , b-bound , b<x) →
            ∣ b , b-bound , CO.<-trans b x y b<x x<y ∣₁)
          (upper→raw A x x∈U))
  powersetCut A inhab bound .Complete.isCompletionValuedCut
    .Complete.IsCompletionValuedCut.completion-lower-rounded =
    λ x x∈L →
      Prop.rec squash₁
        (λ (a , a∈A , x<a) →
          Prop.rec squash₁
            (λ (q , x<q , q<a) →
              let y = K→𝔻 ℓᴾ q in
              ∣ y , x<q , raw→lower A y ∣ a , a∈A , q<a ∣₁ ∣₁)
            (CO.basis-between x a x<a))
        (lower→raw A x x∈L)
  powersetCut A inhab bound .Complete.isCompletionValuedCut
    .Complete.IsCompletionValuedCut.completion-upper-rounded =
    λ x x∈U →
      Prop.rec squash₁
        (λ (b , b-bound , b<x) →
          Prop.rec squash₁
            (λ (q , b<q , q<x) →
              let y = K→𝔻 ℓᴾ q in
              ∣ y , q<x , raw→upper A y ∣ b , b-bound , b<q ∣₁ ∣₁)
            (CO.basis-between b x b<x))
        (upper→raw A x x∈U)
  powersetCut A inhab bound .Complete.isCompletionValuedCut
    .Complete.IsCompletionValuedCut.completion-disjoint =
    λ x x∈L x∈U →
      Prop.rec2 Empty.isProp⊥
        (λ (a , a∈A , x<a) (b , b-bound , b<x) →
          CO.<≤-asym x a x<a
            (CO.≤-trans a b x (b-bound a a∈A) (CO.<→≤ b x b<x)))
        (lower→raw A x x∈L)
        (upper→raw A x x∈U)
  powersetCut A inhab bound .Complete.isCompletionValuedCut
    .Complete.IsCompletionValuedCut.completion-located
    x y x<y with decide (lowerPred A x .snd)
  ... | yes x∈L = ∣ Sum.inl x∈L ∣₁
  ... | no x∉L =
    ∣ Sum.inr
        (raw→upper A y
          ∣ x
          , (λ a a∈A →
              CO.¬>→≤ a x
                (λ x<a →
                  x∉L (raw→lower A x ∣ a , a∈A , x<a ∣₁)))
          , x<y
          ∣₁)
    ∣₁

  supremum :
    (A : ℙ D) →
    (inhab : isInhabited A) →
    (bound : E.isUpperBounded A) →
    E.Supremum A
  supremum A inhab bound .sup =
    Complete.isDedekindCompleteDedekindCompletion (powersetCut A inhab bound) .fst
  supremum A inhab bound .bound a a∈A =
    CO.¬>→≤ a s no-s<a
    where
    C = powersetCut A inhab bound
    s = Complete.isDedekindCompleteDedekindCompletion C .fst
    s-rep = Complete.isDedekindCompleteDedekindCompletion C .snd .fst

    no-s<a : ¬ CO._<_ s a
    no-s<a s<a =
      CO.<-irrefl s
        (s-rep .fst s .fst
          (raw→lower A s ∣ a , a∈A , s<a ∣₁))
  supremum A inhab bound .least b b-bound =
    CO.¬>→≤ s b no-b<s
    where
    C = powersetCut A inhab bound
    s = Complete.isDedekindCompleteDedekindCompletion C .fst
    s-rep = Complete.isDedekindCompleteDedekindCompletion C .snd .fst

    no-b<s : ¬ CO._<_ b s
    no-b<s b<s =
      Prop.rec Empty.isProp⊥
        (λ (a , a∈A , b<a) →
          CO.<≤-asym b a b<a (b-bound a a∈A))
        (lower→raw A b (s-rep .fst b .snd b<s))

  isMacNeilleCompleteDedekindCompletion : M.isMacNeilleComplete
  isMacNeilleCompleteDedekindCompletion {A = A} =
    supremum A


open LinearlyOrderedFieldStructure public
  using
    ( DedekindCompletionLinearlyOrderedField
    ; DedekindCompletionLinearlyOrderedCommRing
    )

open MacNeilleCompleteness public
  using (isMacNeilleCompleteDedekindCompletion ; supremum)
