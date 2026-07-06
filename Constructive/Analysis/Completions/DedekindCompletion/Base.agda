{-

Dedekind completion over a linearly ordered field

The cuts are two-sided and located, as in the constructive Dedekind reals.
This module abstracts the rational-cut definition by replacing the rationals
with the carrier of an arbitrary linearly ordered field.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Completions.DedekindCompletion.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

import Constructive.Algebra.LinearlyOrderedCommRing.Base as LinearBase
open import Constructive.Algebra.LinearlyOrderedField
import Constructive.Foundations.Powerset as Powerset

private
  variable
    ℓ ℓ' ℓᴾ : Level


module CompletionBase (𝒦 : LinearlyOrderedField ℓ ℓ') where

  open LinearlyOrderedFieldStr 𝒦

  private
    K : Type ℓ
    K = 𝒦 .fst .fst .fst

  private
    predLevel : Level → Level
    predLevel ℓᴾ = ℓ-max ℓ (ℓ-max ℓ' ℓᴾ)


  Pred : (ℓᴾ : Level) → Type _
  Pred ℓᴾ = Powerset.Pred K (predLevel ℓᴾ)

  open Powerset
    using
      ( _∈_
      ; isProp∈
      ; isSetPred
      ; _⊆_
      ; isProp⊆
      ; ⊆-refl
      ; ⊆-trans
      ; predExt
      )


  record IsDedekindCut (L U : Pred ℓᴾ) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ)) where
    no-eta-equality

    field
      lower-inhabited : ∥ Σ[ q ∈ K ] q ∈ L ∥₁
      upper-inhabited : ∥ Σ[ q ∈ K ] q ∈ U ∥₁

      lower-closed :
        (p q : K) → p < q → q ∈ L → p ∈ L

      upper-closed :
        (p q : K) → p < q → p ∈ U → q ∈ U

      lower-rounded :
        (q : K) → q ∈ L →
        ∥ Σ[ r ∈ K ] (q < r) × (r ∈ L) ∥₁

      upper-rounded :
        (q : K) → q ∈ U →
        ∥ Σ[ r ∈ K ] (r < q) × (r ∈ U) ∥₁

      disjoint :
        (q : K) → q ∈ L → q ∈ U → ⊥

      located :
        (p q : K) → p < q → ∥ (p ∈ L) ⊎ (q ∈ U) ∥₁


  record DedekindCompletion (ℓᴾ : Level) :
      Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))) where
    no-eta-equality

    field
      lower : Pred ℓᴾ
      upper : Pred ℓᴾ
      isDedekindCut : IsDedekindCut lower upper

    open IsDedekindCut isDedekindCut public


  open IsDedekindCut public
  open DedekindCompletion public


  isPropIsDedekindCut : (L U : Pred ℓᴾ) → isProp (IsDedekindCut L U)
  isPropIsDedekindCut L U c d i .IsDedekindCut.lower-inhabited =
    squash₁ (c .IsDedekindCut.lower-inhabited) (d .IsDedekindCut.lower-inhabited) i
  isPropIsDedekindCut L U c d i .IsDedekindCut.upper-inhabited =
    squash₁ (c .IsDedekindCut.upper-inhabited) (d .IsDedekindCut.upper-inhabited) i
  isPropIsDedekindCut L U c d i .IsDedekindCut.lower-closed =
    isPropΠ4 (λ p _ _ _ → isProp∈ L p)
      (c .IsDedekindCut.lower-closed) (d .IsDedekindCut.lower-closed) i
  isPropIsDedekindCut L U c d i .IsDedekindCut.upper-closed =
    isPropΠ4 (λ _ q _ _ → isProp∈ U q)
      (c .IsDedekindCut.upper-closed) (d .IsDedekindCut.upper-closed) i
  isPropIsDedekindCut L U c d i .IsDedekindCut.lower-rounded =
    isPropΠ2 (λ _ _ → squash₁)
      (c .IsDedekindCut.lower-rounded) (d .IsDedekindCut.lower-rounded) i
  isPropIsDedekindCut L U c d i .IsDedekindCut.upper-rounded =
    isPropΠ2 (λ _ _ → squash₁)
      (c .IsDedekindCut.upper-rounded) (d .IsDedekindCut.upper-rounded) i
  isPropIsDedekindCut L U c d i .IsDedekindCut.disjoint =
    isPropΠ3 (λ _ _ _ → Empty.isProp⊥)
      (c .IsDedekindCut.disjoint) (d .IsDedekindCut.disjoint) i
  isPropIsDedekindCut L U c d i .IsDedekindCut.located =
    isPropΠ3 (λ _ _ _ → squash₁)
      (c .IsDedekindCut.located) (d .IsDedekindCut.located) i


  DedekindCompletionPath :
    (x y : DedekindCompletion ℓᴾ) →
    lower x ≡ lower y →
    upper x ≡ upper y →
    x ≡ y
  DedekindCompletionPath x y lower-path upper-path i .lower = lower-path i
  DedekindCompletionPath x y lower-path upper-path i .upper = upper-path i
  DedekindCompletionPath x y lower-path upper-path i .isDedekindCut =
    isProp→PathP
      (λ i → isPropIsDedekindCut (lower-path i) (upper-path i))
      (isDedekindCut x) (isDedekindCut y) i


  completionExt :
    (x y : DedekindCompletion ℓᴾ) →
    lower x ⊆ lower y →
    lower y ⊆ lower x →
    upper x ⊆ upper y →
    upper y ⊆ upper x →
    x ≡ y
  completionExt x y Lx⊆Ly Ly⊆Lx Ux⊆Uy Uy⊆Ux =
    DedekindCompletionPath x y
      (predExt (lower x) (lower y) Lx⊆Ly Ly⊆Lx)
      (predExt (upper x) (upper y) Ux⊆Uy Uy⊆Ux)


  private
    CompletionΣ : (ℓᴾ : Level) → Type _
    CompletionΣ ℓᴾ =
      Σ[ L ∈ Pred ℓᴾ ] Σ[ U ∈ Pred ℓᴾ ] IsDedekindCut L U

    completion→Σ : DedekindCompletion ℓᴾ → CompletionΣ ℓᴾ
    completion→Σ x = lower x , upper x , isDedekindCut x

    Σ→completion : CompletionΣ ℓᴾ → DedekindCompletion ℓᴾ
    Σ→completion (L , U , cut) = record
      { lower = L
      ; upper = U
      ; isDedekindCut = cut
      }

    isSetCompletionΣ : isSet (CompletionΣ ℓᴾ)
    isSetCompletionΣ =
      isOfHLevelΣ 2 isSetPred λ L →
      isOfHLevelΣ 2 isSetPred λ U →
      isProp→isSet (isPropIsDedekindCut L U)


  isSetDedekindCompletion : isSet (DedekindCompletion ℓᴾ)
  isSetDedekindCompletion =
    isSetRetract completion→Σ Σ→completion
      (λ x → DedekindCompletionPath (Σ→completion (completion→Σ x)) x refl refl)
      isSetCompletionΣ


  -- Principal cuts embed the base field into its Dedekind completion.

  K→𝔻 : (ℓᴾ : Level) → K → DedekindCompletion ℓᴾ
  K→𝔻 ℓᴾ x .lower p =
    Lift (ℓ-max ℓ ℓᴾ) (p < x) ,
    isOfHLevelLift 1 isProp<
  K→𝔻 ℓᴾ x .upper p =
    Lift (ℓ-max ℓ ℓᴾ) (x < p) ,
    isOfHLevelLift 1 isProp<
  K→𝔻 ℓᴾ x .isDedekindCut .IsDedekindCut.lower-inhabited =
    ∣ x - 1r , lift q-1<q ∣₁
  K→𝔻 ℓᴾ x .isDedekindCut .IsDedekindCut.upper-inhabited =
    ∣ x + 1r , lift q+1>q ∣₁
  K→𝔻 ℓᴾ x .isDedekindCut .IsDedekindCut.lower-closed =
    λ p r p<r r<x → lift (<-trans p<r (Lift.lower r<x))
  K→𝔻 ℓᴾ x .isDedekindCut .IsDedekindCut.upper-closed =
    λ p r p<r x<p → lift (<-trans (Lift.lower x<p) p<r)
  K→𝔻 ℓᴾ x .isDedekindCut .IsDedekindCut.lower-rounded =
    λ p p<x →
      ∣ middle p x , middle>l (Lift.lower p<x) , lift (middle<r (Lift.lower p<x)) ∣₁
  K→𝔻 ℓᴾ x .isDedekindCut .IsDedekindCut.upper-rounded =
    λ p x<p →
      ∣ middle x p , middle<r (Lift.lower x<p) , lift (middle>l (Lift.lower x<p)) ∣₁
  K→𝔻 ℓᴾ x .isDedekindCut .IsDedekindCut.disjoint =
    λ p p<x x<p → <-asym (Lift.lower p<x) (Lift.lower x<p)
  K→𝔻 ℓᴾ x .isDedekindCut .IsDedekindCut.located p r p<r =
    case-split (trichotomy p x)
    where
    case-split :
      LinearBase.Trichotomy (𝒦 .fst .fst) p x →
      ∥ (p ∈ lower (K→𝔻 ℓᴾ x)) ⊎ (r ∈ upper (K→𝔻 ℓᴾ x)) ∥₁
    case-split (LinearBase.lt p<x) = ∣ Sum.inl (lift p<x) ∣₁
    case-split (LinearBase.eq p≡x) = ∣ Sum.inr (lift (subst (_< r) p≡x p<r)) ∣₁
    case-split (LinearBase.gt x<p) = ∣ Sum.inr (lift (<-trans x<p p<r)) ∣₁
