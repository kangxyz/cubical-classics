{-

MacNeille completeness of constructive Dedekind reals under Oracle

Classical powerset suprema from located real-valued cuts

-}
{-# OPTIONS --safe --lossy-unification #-}
module Classical.DedekindReals.MacNeilleCompleteness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.Data.Unit using (tt*)
open import Cubical.Data.Bool using (Bool ; true ; false ; Dec→Bool ; Bool→Type*)
open import Cubical.Data.Bool.Properties using (isPropBool→Type*)
open import Cubical.Relation.Nullary using (Dec ; yes ; no ; ¬_)
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

import Constructive.Algebra.OrderedField as WeakOF
import Constructive.Algebra.StrictlyOrderedCommRing as StrictOCR
import Constructive.Algebra.StrictlyOrderedField as StrictOF
open import Constructive.DedekindReals
open import Constructive.DedekindReals.Arithmetic
open import Constructive.DedekindReals.Completeness
import Constructive.Rationals as ℚExtra

private
  variable
    ℓ ℓ' : Level

_∈ℙ_ : ⦃ _ : Oracle ⦄ → {X : Type ℓ} → X → ℙ X → Type
x ∈ℙ A = Powerset._∈_ x A

infix 6 _∈ℙ_


module ClassicalResize ⦃ 🤖 : Oracle ⦄ where
  open Oracle 🤖

  small : hProp ℓ → hProp ℓ'
  small P = Bool→Type* (Dec→Bool (decide (P .snd))) , isPropBool→Type*

  to-small : (P : hProp ℓ) → P .fst → small {ℓ = ℓ} {ℓ' = ℓ'} P .fst
  to-small P p with decide (P .snd)
  ... | yes _ = tt*
  ... | no ¬p = Empty.rec (¬p p)

  from-small : (P : hProp ℓ) → small {ℓ = ℓ} {ℓ' = ℓ'} P .fst → P .fst
  from-small P p with decide (P .snd)
  ... | yes q = q
  ... | no ¬p = Empty.rec* p


module StrictlyOrderedFieldStructure ⦃ 🤖 : Oracle ⦄ {ℓ : Level} where
  open Oracle 🤖
  module O = Order {ℓ}
  open Addition {ℓ}
  open Multiplication {ℓ}
  open RationalEmbedding {ℓ}
  module CR = CommRingStructure {ℓ}
  module OCR = OrderedCommRingStructure {ℓ}
  module OF = OrderedFieldStructure {ℓ}

  trichotomy :
    (x y : DedekindReal ℓ) →
    StrictOCR.Trichotomy OCR.DedekindOrderedCommRing x y
  trichotomy x y with decide (O.isProp< x y)
  ... | yes x<y = StrictOCR.lt x<y
  ... | no ¬x<y with decide (O.isProp< y x)
  ... | yes y<x = StrictOCR.gt y<x
  ... | no ¬y<x =
    StrictOCR.eq
      (O.≤-antisym x y
        (O.¬>→≤ x y ¬y<x)
        (O.¬>→≤ y x ¬x<y))

  DedekindStrictlyOrderedCommRing :
    StrictOCR.StrictlyOrderedCommRing (ℓ-suc ℓ) ℓ
  DedekindStrictlyOrderedCommRing =
    OCR.DedekindOrderedCommRing ,
    StrictOCR.strictorderstr trichotomy

  #from≠0 :
    (x : DedekindReal ℓ) →
    ¬ x ≡ 0𝔻 →
    O._#_ x 0𝔻
  #from≠0 x x≢0 with trichotomy x 0𝔻
  ... | StrictOCR.lt x<0 = Sum.inl x<0
  ... | StrictOCR.gt 0<x = Sum.inr 0<x
  ... | StrictOCR.eq x≡0 = Empty.rec (x≢0 x≡0)

  hasInverse :
    (x : DedekindReal ℓ) →
    ¬ x ≡ 0𝔻 →
    Σ[ y ∈ DedekindReal ℓ ] x * y ≡ 1𝔻
  hasInverse x x≢0 =
    WeakOF.IsOrderedField.inv#
      (OF.DedekindOrderedField .snd)
      x
      (#from≠0 x x≢0)

  0≢1 : ¬ 0𝔻 ≡ 1𝔻
  0≢1 0≡1 =
    O.<-irrefl 0𝔻
      (subst (λ x → O._<_ 0𝔻 x) (sym 0≡1) 0𝔻<1𝔻)

  DedekindIsFieldOnStrictlyOrderedCommRing :
    StrictOF.IsFieldOnStrictlyOrderedCommRing DedekindStrictlyOrderedCommRing
  DedekindIsFieldOnStrictlyOrderedCommRing =
    isfield
      (CommRingStr.isCommRing (CR.DedekindCommRing .snd))
      hasInverse
      0≢1

  DedekindStrictlyOrderedField :
    StrictOF.StrictlyOrderedField (ℓ-suc ℓ) ℓ
  DedekindStrictlyOrderedField =
    DedekindStrictlyOrderedCommRing ,
    DedekindIsFieldOnStrictlyOrderedCommRing


module MacNeilleCompleteness ⦃ 🤖 : Oracle ⦄ {ℓ : Level} where
  open Oracle 🤖
  open ClassicalResize ⦃ 🤖 ⦄
  module SOF = StrictlyOrderedFieldStructure ⦃ 🤖 ⦄ {ℓ}
  module O = Order {ℓ}
  module Arch = Archimedean {ℓ}
  open Addition {ℓ}
  module M = MacNeilleCompleteOrderedField SOF.DedekindStrictlyOrderedField
  module E = Extremum SOF.DedekindStrictlyOrderedField
  open E.Supremum

  private
    D : Type (ℓ-suc ℓ)
    D = DedekindReal ℓ

  rawLower : ℙ D → D → hProp (ℓ-suc ℓ)
  rawLower A x =
    ∥ Σ[ a ∈ D ] (a ∈ℙ A) × O._<_ x a ∥₁ ,
    squash₁

  rawUpper : ℙ D → D → hProp (ℓ-suc ℓ)
  rawUpper A x =
    ∥ Σ[ b ∈ D ] ((a : D) → a ∈ℙ A → O._≤_ a b) × O._<_ b x ∥₁ ,
    squash₁

  lowerPred : ℙ D → RealPred ℓ
  lowerPred A x = small (rawLower A x)

  upperPred : ℙ D → RealPred ℓ
  upperPred A x = small (rawUpper A x)

  lower→raw :
    (A : ℙ D) (x : D) →
    x ∈ᴿ lowerPred A →
    rawLower A x .fst
  lower→raw A x = from-small (rawLower A x)

  raw→lower :
    (A : ℙ D) (x : D) →
    rawLower A x .fst →
    x ∈ᴿ lowerPred A
  raw→lower A x = to-small (rawLower A x)

  upper→raw :
    (A : ℙ D) (x : D) →
    x ∈ᴿ upperPred A →
    rawUpper A x .fst
  upper→raw A x = from-small (rawUpper A x)

  raw→upper :
    (A : ℙ D) (x : D) →
    rawUpper A x .fst →
    x ∈ᴿ upperPred A
  raw→upper A x = to-small (rawUpper A x)

  powersetCut :
    (A : ℙ D) →
    isInhabited A →
    E.isUpperBounded A →
    RealValuedCut ℓ
  powersetCut A inhab bound .realLower = lowerPred A
  powersetCut A inhab bound .realUpper = upperPred A
  powersetCut A inhab bound .isRealValuedCut .IsRealValuedCut.real-lower-inhabited =
    Prop.rec squash₁ step inhab
    where
    step : Σ[ a ∈ D ] a ∈ℙ A → ∥ Σ[ x ∈ D ] x ∈ᴿ lowerPred A ∥₁
    step (a , a∈A) =
      Prop.rec squash₁
        (λ (n , q<a) →
          let x = ℚ→𝔻 ℓ (ℚ.- ℚExtra.natMul n ℚExtra.1ℚ) in
          ∣ x , raw→lower A x ∣ a , a∈A , q<a ∣₁ ∣₁)
        (Arch.lower-rational-bound a)
  powersetCut A inhab bound .isRealValuedCut .IsRealValuedCut.real-upper-inhabited =
    Prop.rec squash₁ step bound
    where
    step :
      Σ[ b ∈ D ] ((a : D) → a ∈ℙ A → O._≤_ a b) →
      ∥ Σ[ x ∈ D ] x ∈ᴿ upperPred A ∥₁
    step (b , b-bound) =
      Prop.rec squash₁
        (λ (n , b<q) →
          let x = ℚ→𝔻 ℓ (ℚExtra.natMul n ℚExtra.1ℚ) in
          ∣ x , raw→upper A x ∣ b , b-bound , b<q ∣₁ ∣₁)
        (Arch.upper-rational-bound b)
  powersetCut A inhab bound .isRealValuedCut .IsRealValuedCut.real-lower-closed =
    λ x y x<y y∈L →
      raw→lower A x
        (Prop.rec squash₁
          (λ (a , a∈A , y<a) →
            ∣ a , a∈A , O.<-trans x y a x<y y<a ∣₁)
          (lower→raw A y y∈L))
  powersetCut A inhab bound .isRealValuedCut .IsRealValuedCut.real-upper-closed =
    λ x y x<y x∈U →
      raw→upper A y
        (Prop.rec squash₁
          (λ (b , b-bound , b<x) →
            ∣ b , b-bound , O.<-trans b x y b<x x<y ∣₁)
          (upper→raw A x x∈U))
  powersetCut A inhab bound .isRealValuedCut .IsRealValuedCut.real-lower-rounded =
    λ x x∈L →
      Prop.rec squash₁
        (λ (a , a∈A , x<a) →
          Prop.rec squash₁
            (λ (q , x<q , q<a) →
              let y = ℚ→𝔻 ℓ q in
              ∣ y , x<q , raw→lower A y ∣ a , a∈A , q<a ∣₁ ∣₁)
            (O.rational-between x a x<a))
        (lower→raw A x x∈L)
  powersetCut A inhab bound .isRealValuedCut .IsRealValuedCut.real-upper-rounded =
    λ x x∈U →
      Prop.rec squash₁
        (λ (b , b-bound , b<x) →
          Prop.rec squash₁
            (λ (q , b<q , q<x) →
              let y = ℚ→𝔻 ℓ q in
              ∣ y , q<x , raw→upper A y ∣ b , b-bound , b<q ∣₁ ∣₁)
            (O.rational-between b x b<x))
        (upper→raw A x x∈U)
  powersetCut A inhab bound .isRealValuedCut .IsRealValuedCut.real-disjoint =
    λ x x∈L x∈U →
      Prop.rec2 Empty.isProp⊥
        (λ (a , a∈A , x<a) (b , b-bound , b<x) →
          O.<≤-asym x a x<a
            (O.≤-trans a b x (b-bound a a∈A) (O.<→≤ b x b<x)))
        (lower→raw A x x∈L)
        (upper→raw A x x∈U)
  powersetCut A inhab bound .isRealValuedCut .IsRealValuedCut.real-located
    x y x<y with decide (lowerPred A x .snd)
  ... | yes x∈L = ∣ Sum.inl x∈L ∣₁
  ... | no x∉L =
    ∣ Sum.inr
        (raw→upper A y
          ∣ x
          , (λ a a∈A →
              O.¬>→≤ a x
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
    isDedekindCompleteDedekindReal (powersetCut A inhab bound) .fst
  supremum A inhab bound .bound a a∈A =
    O.¬>→≤ a s no-s<a
    where
    C = powersetCut A inhab bound
    s = isDedekindCompleteDedekindReal C .fst
    s-rep = isDedekindCompleteDedekindReal C .snd .fst

    no-s<a : ¬ O._<_ s a
    no-s<a s<a =
      O.<-irrefl s
        (s-rep .fst s .fst
          (raw→lower A s ∣ a , a∈A , s<a ∣₁))
  supremum A inhab bound .least b b-bound =
    O.¬>→≤ s b no-b<s
    where
    C = powersetCut A inhab bound
    s = isDedekindCompleteDedekindReal C .fst
    s-rep = isDedekindCompleteDedekindReal C .snd .fst

    no-b<s : ¬ O._<_ b s
    no-b<s b<s =
      Prop.rec Empty.isProp⊥
        (λ (a , a∈A , b<a) →
          O.<≤-asym b a b<a (b-bound a a∈A))
        (lower→raw A b (s-rep .fst b .snd b<s))

  isMacNeilleCompleteDedekindReal : M.isMacNeilleComplete
  isMacNeilleCompleteDedekindReal {A = A} =
    supremum A


open StrictlyOrderedFieldStructure public
  using (DedekindStrictlyOrderedField ; DedekindStrictlyOrderedCommRing)

open MacNeilleCompleteness public
  using (isMacNeilleCompleteDedekindReal ; supremum)
