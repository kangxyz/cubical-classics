{-

Dedekind completeness for Dedekind completions

Dedekind completeness is stated in representation form: every located cut of
Dedekind-completion elements is represented by a unique element.  No Oracle,
LEM, or propositional resizing is used here.

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Completions.DedekindCompletion.Completeness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

open import Constructive.Algebra.LinearlyOrderedField.Archimedean
open import Constructive.Analysis.Completions.DedekindCompletion.Base
open import Constructive.Analysis.Completions.DedekindCompletion.Order
open import Constructive.Foundations.Powerset as Powerset hiding (Pred)

private
  variable
    ℓ ℓ' : Level


module CompletionCompleteness
    (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ')
    (ℓᴾ : Level) where

  private
    𝒦 = 𝒜 .fst

    K : Type ℓ
    K = 𝒦 .fst .fst .fst

  open CompletionBase 𝒦
  module Order = CompletionOrder 𝒦


  completionPredLevel : Level
  completionPredLevel = ℓ-max ℓ (ℓ-max ℓ' ℓᴾ)


  CompletionPred : Type _
  CompletionPred =
    Powerset.Pred (DedekindCompletion ℓᴾ) completionPredLevel

  _∈𝔻_ :
    DedekindCompletion ℓᴾ →
    CompletionPred →
    Type _
  x ∈𝔻 P = Powerset._∈_ x P

  infix 4 _∈𝔻_

  isProp∈𝔻 :
    (P : CompletionPred) →
    (x : DedekindCompletion ℓᴾ) →
    isProp (x ∈𝔻 P)
  isProp∈𝔻 P x = Powerset.isProp∈ P x


  record IsCompletionValuedCut
      (L U : CompletionPred) :
      Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))) where
    no-eta-equality

    field
      completion-lower-inhabited :
        ∥ Σ[ x ∈ DedekindCompletion ℓᴾ ] x ∈𝔻 L ∥₁

      completion-upper-inhabited :
        ∥ Σ[ x ∈ DedekindCompletion ℓᴾ ] x ∈𝔻 U ∥₁

      completion-lower-closed :
        (x y : DedekindCompletion ℓᴾ) →
        Order._<_ {ℓᴾ = ℓᴾ} x y →
        y ∈𝔻 L →
        x ∈𝔻 L

      completion-upper-closed :
        (x y : DedekindCompletion ℓᴾ) →
        Order._<_ {ℓᴾ = ℓᴾ} x y →
        x ∈𝔻 U →
        y ∈𝔻 U

      completion-lower-rounded :
        (x : DedekindCompletion ℓᴾ) →
        x ∈𝔻 L →
        ∥ Σ[ y ∈ DedekindCompletion ℓᴾ ] (Order._<_ {ℓᴾ = ℓᴾ} x y) × (y ∈𝔻 L) ∥₁

      completion-upper-rounded :
        (x : DedekindCompletion ℓᴾ) →
        x ∈𝔻 U →
        ∥ Σ[ y ∈ DedekindCompletion ℓᴾ ] (Order._<_ {ℓᴾ = ℓᴾ} y x) × (y ∈𝔻 U) ∥₁

      completion-disjoint :
        (x : DedekindCompletion ℓᴾ) →
        x ∈𝔻 L →
        x ∈𝔻 U →
        ⊥

      completion-located :
        (x y : DedekindCompletion ℓᴾ) →
        Order._<_ {ℓᴾ = ℓᴾ} x y →
        ∥ (x ∈𝔻 L) ⊎ (y ∈𝔻 U) ∥₁


  record CompletionValuedCut :
      Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))) where
    no-eta-equality

    field
      completionLower : CompletionPred
      completionUpper : CompletionPred
      isCompletionValuedCut :
        IsCompletionValuedCut completionLower completionUpper

    open IsCompletionValuedCut isCompletionValuedCut public


  open CompletionValuedCut public


  representingLower : CompletionValuedCut → Pred ℓᴾ
  representingLower C q =
    (K→𝔻 ℓᴾ q ∈𝔻 completionLower C) ,
    isProp∈𝔻 (completionLower C) (K→𝔻 ℓᴾ q)


  representingUpper : CompletionValuedCut → Pred ℓᴾ
  representingUpper C q =
    (K→𝔻 ℓᴾ q ∈𝔻 completionUpper C) ,
    isProp∈𝔻 (completionUpper C) (K→𝔻 ℓᴾ q)


  isDedekindCutRepresenting :
    (C : CompletionValuedCut) →
    IsDedekindCut {ℓᴾ = ℓᴾ} (representingLower C) (representingUpper C)
  isDedekindCutRepresenting C .IsDedekindCut.lower-inhabited =
    Prop.rec squash₁ from-completion
      (completion-lower-inhabited C)
    where
    from-completion :
      Σ[ x ∈ DedekindCompletion ℓᴾ ] x ∈𝔻 completionLower C →
      ∥ Σ[ q ∈ K ] q ∈ representingLower C ∥₁
    from-completion (x , x∈L) =
      Prop.rec squash₁
        (λ (q , q∈Lx) →
          ∣ q
          , completion-lower-closed C
              (K→𝔻 ℓᴾ q)
              x
              (Order.lower→K< {ℓᴾ = ℓᴾ} x q q∈Lx)
              x∈L
          ∣₁)
        (DedekindCompletion.lower-inhabited x)
  isDedekindCutRepresenting C .IsDedekindCut.upper-inhabited =
    Prop.rec squash₁ from-completion
      (completion-upper-inhabited C)
    where
    from-completion :
      Σ[ x ∈ DedekindCompletion ℓᴾ ] x ∈𝔻 completionUpper C →
      ∥ Σ[ q ∈ K ] q ∈ representingUpper C ∥₁
    from-completion (x , x∈U) =
      Prop.rec squash₁
        (λ (q , q∈Ux) →
          ∣ q
          , completion-upper-closed C
              x
              (K→𝔻 ℓᴾ q)
              (Order.upper→<K {ℓᴾ = ℓᴾ} x q q∈Ux)
              x∈U
          ∣₁)
        (DedekindCompletion.upper-inhabited x)
  isDedekindCutRepresenting C .IsDedekindCut.lower-closed =
    λ p q p<q q∈L →
      completion-lower-closed C
        (K→𝔻 ℓᴾ p)
        (K→𝔻 ℓᴾ q)
        (Order.K→<-pres {ℓᴾ = ℓᴾ} p q p<q)
        q∈L
  isDedekindCutRepresenting C .IsDedekindCut.upper-closed =
    λ p q p<q p∈U →
      completion-upper-closed C
        (K→𝔻 ℓᴾ p)
        (K→𝔻 ℓᴾ q)
        (Order.K→<-pres {ℓᴾ = ℓᴾ} p q p<q)
        p∈U
  isDedekindCutRepresenting C .IsDedekindCut.lower-rounded =
    λ q q∈L →
      Prop.rec squash₁
        (λ (y , q<y , y∈L) →
          Prop.rec squash₁
            (λ (r , q<r , r<y) →
              ∣ r
              , Order.K→<-reflect {ℓᴾ = ℓᴾ} q r q<r
              , completion-lower-closed C
                  (K→𝔻 ℓᴾ r)
                  y
                  r<y
                  y∈L
              ∣₁)
            (Order.basis-between {ℓᴾ = ℓᴾ}
              (K→𝔻 ℓᴾ q)
              y
              q<y))
        (completion-lower-rounded C (K→𝔻 ℓᴾ q) q∈L)
  isDedekindCutRepresenting C .IsDedekindCut.upper-rounded =
    λ q q∈U →
      Prop.rec squash₁
        (λ (y , y<q , y∈U) →
          Prop.rec squash₁
            (λ (r , y<r , r<q) →
              ∣ r
              , Order.K→<-reflect {ℓᴾ = ℓᴾ} r q r<q
              , completion-upper-closed C
                  y
                  (K→𝔻 ℓᴾ r)
                  y<r
                  y∈U
              ∣₁)
            (Order.basis-between {ℓᴾ = ℓᴾ}
              y
              (K→𝔻 ℓᴾ q)
              y<q))
        (completion-upper-rounded C (K→𝔻 ℓᴾ q) q∈U)
  isDedekindCutRepresenting C .IsDedekindCut.disjoint =
    λ q → completion-disjoint C (K→𝔻 ℓᴾ q)
  isDedekindCutRepresenting C .IsDedekindCut.located =
    λ p q p<q →
      Prop.rec squash₁
        (λ where
          (Sum.inl p∈L) → ∣ Sum.inl p∈L ∣₁
          (Sum.inr q∈U) → ∣ Sum.inr q∈U ∣₁)
        (completion-located C
          (K→𝔻 ℓᴾ p)
          (K→𝔻 ℓᴾ q)
          (Order.K→<-pres {ℓᴾ = ℓᴾ} p q p<q))


  representing-completion :
    CompletionValuedCut →
    DedekindCompletion ℓᴾ
  representing-completion C .lower = representingLower C
  representing-completion C .upper = representingUpper C
  representing-completion C .isDedekindCut =
    isDedekindCutRepresenting C


  represented-lower :
    (C : CompletionValuedCut) (x : DedekindCompletion ℓᴾ) →
    (x ∈𝔻 completionLower C → Order._<_ {ℓᴾ = ℓᴾ} x (representing-completion C))
    ×
    (Order._<_ {ℓᴾ = ℓᴾ} x (representing-completion C) → x ∈𝔻 completionLower C)
  represented-lower C x = to , from
    where
    to :
      x ∈𝔻 completionLower C →
      Order._<_ {ℓᴾ = ℓᴾ} x (representing-completion C)
    to x∈L =
      Prop.rec squash₁
        (λ (y , x<y , y∈L) →
          Prop.rec squash₁
            (λ (q , x<q , q<y) →
              ∣ q
              , Order.<K→upper {ℓᴾ = ℓᴾ} x q x<q
              , completion-lower-closed C
                  (K→𝔻 ℓᴾ q)
                  y
                  q<y
                  y∈L
              ∣₁)
            (Order.basis-between {ℓᴾ = ℓᴾ} x y x<y))
        (completion-lower-rounded C x x∈L)

    from :
      Order._<_ {ℓᴾ = ℓᴾ} x (representing-completion C) →
      x ∈𝔻 completionLower C
    from =
      Prop.rec (isProp∈𝔻 (completionLower C) x)
        (λ (q , q∈Ux , q∈L) →
          completion-lower-closed C
            x
            (K→𝔻 ℓᴾ q)
            (Order.upper→<K {ℓᴾ = ℓᴾ} x q q∈Ux)
            q∈L)


  represented-upper :
    (C : CompletionValuedCut) (x : DedekindCompletion ℓᴾ) →
    (x ∈𝔻 completionUpper C → Order._<_ {ℓᴾ = ℓᴾ} (representing-completion C) x)
    ×
    (Order._<_ {ℓᴾ = ℓᴾ} (representing-completion C) x → x ∈𝔻 completionUpper C)
  represented-upper C x = to , from
    where
    to :
      x ∈𝔻 completionUpper C →
      Order._<_ {ℓᴾ = ℓᴾ} (representing-completion C) x
    to x∈U =
      Prop.rec squash₁
        (λ (y , y<x , y∈U) →
          Prop.rec squash₁
            (λ (q , y<q , q<x) →
              ∣ q
              , completion-upper-closed C
                  y
                  (K→𝔻 ℓᴾ q)
                  y<q
                  y∈U
              , Order.K<→lower {ℓᴾ = ℓᴾ} x q q<x
              ∣₁)
            (Order.basis-between {ℓᴾ = ℓᴾ} y x y<x))
        (completion-upper-rounded C x x∈U)

    from :
      Order._<_ {ℓᴾ = ℓᴾ} (representing-completion C) x →
      x ∈𝔻 completionUpper C
    from =
      Prop.rec (isProp∈𝔻 (completionUpper C) x)
        (λ (q , q∈U , q∈Lx) →
          completion-upper-closed C
            (K→𝔻 ℓᴾ q)
            x
            (Order.lower→K< {ℓᴾ = ℓᴾ} x q q∈Lx)
            q∈U)


  representsLower :
    CompletionValuedCut →
    DedekindCompletion ℓᴾ →
    Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ)))
  representsLower C z =
    (x : DedekindCompletion ℓᴾ) →
      (x ∈𝔻 completionLower C → Order._<_ {ℓᴾ = ℓᴾ} x z)
      ×
      (Order._<_ {ℓᴾ = ℓᴾ} x z → x ∈𝔻 completionLower C)


  representsCut :
    CompletionValuedCut →
    DedekindCompletion ℓᴾ →
    Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ)))
  representsCut C z =
    representsLower C z
    ×
    ((x : DedekindCompletion ℓᴾ) →
      (x ∈𝔻 completionUpper C → Order._<_ {ℓᴾ = ℓᴾ} z x)
      ×
      (Order._<_ {ℓᴾ = ℓᴾ} z x → x ∈𝔻 completionUpper C))


  -- Dedekind completeness means that every located cut whose elements are
  -- themselves elements of the completion is represented by a unique element.
  -- The representative `z` realizes the lower side as `x < z` and the upper
  -- side as `z < x`.
  isDedekindComplete :
    Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ)))
  isDedekindComplete =
    (C : CompletionValuedCut) →
    Σ[ z ∈ DedekindCompletion ℓᴾ ]
      representsCut C z
      ×
      ((z' : DedekindCompletion ℓᴾ) → representsCut C z' → z' ≡ z)


  representing-completion-unique :
    (C : CompletionValuedCut) (z : DedekindCompletion ℓᴾ) →
    representsLower C z →
    z ≡ representing-completion C
  representing-completion-unique C z z-rep =
    Order.≤-antisym {ℓᴾ = ℓᴾ} z (representing-completion C) z≤rep rep≤z
    where
    z≤rep : Order._≤_ {ℓᴾ = ℓᴾ} z (representing-completion C)
    z≤rep q q∈Lz =
      z-rep (K→𝔻 ℓᴾ q) .snd
        (Order.lower→K< {ℓᴾ = ℓᴾ} z q q∈Lz)

    rep≤z : Order._≤_ {ℓᴾ = ℓᴾ} (representing-completion C) z
    rep≤z q q∈Lrep =
      Order.K<→lower {ℓᴾ = ℓᴾ} z q
        (z-rep (K→𝔻 ℓᴾ q) .fst q∈Lrep)


  representing-completion-representsLower :
    (C : CompletionValuedCut) →
    representsLower C (representing-completion C)
  representing-completion-representsLower C x =
    represented-lower C x


  representing-completion-representsCut :
    (C : CompletionValuedCut) →
    representsCut C (representing-completion C)
  representing-completion-representsCut C =
    representing-completion-representsLower C ,
    represented-upper C


  isDedekindCompleteDedekindCompletion :
    isDedekindComplete
  isDedekindCompleteDedekindCompletion C =
    representing-completion C ,
    representing-completion-representsCut C ,
    λ z z-rep → representing-completion-unique C z (z-rep .fst)
