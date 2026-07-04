{-

Constructive Dedekind completeness for Dedekind cuts.

This module proves the representation form of Dedekind completeness: a
located cut whose elements are Dedekind reals is represented by a unique
Dedekind real.  No LEM or resizing is used here.

-}
{-# OPTIONS --safe #-}
module Cubical.DedekindCut.Completeness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Rationals using (ℚ)
import Cubical.Data.Rationals as ℚ
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)

open import Cubical.DedekindCut
import Cubical.Rationals as ℚExtra

private
  variable
    ℓ : Level


RealPred : (ℓ : Level) → Type (ℓ-suc ℓ)
RealPred ℓ = DedekindCut ℓ → hProp ℓ

_∈ᴿ_ : DedekindCut ℓ → RealPred ℓ → Type ℓ
x ∈ᴿ P = P x .fst

infix 4 _∈ᴿ_

isProp∈ᴿ : (P : RealPred ℓ) → (x : DedekindCut ℓ) → isProp (x ∈ᴿ P)
isProp∈ᴿ P x = P x .snd


record isRealValuedCut (L U : RealPred ℓ) : Type (ℓ-suc ℓ) where
  no-eta-equality

  field
    real-lower-inhabited :
      ∥ Σ[ x ∈ DedekindCut ℓ ] x ∈ᴿ L ∥₁

    real-upper-inhabited :
      ∥ Σ[ x ∈ DedekindCut ℓ ] x ∈ᴿ U ∥₁

    real-lower-closed :
      (x y : DedekindCut ℓ) →
      Order._<_ {ℓ = ℓ} x y →
      y ∈ᴿ L →
      x ∈ᴿ L

    real-upper-closed :
      (x y : DedekindCut ℓ) →
      Order._<_ {ℓ = ℓ} x y →
      x ∈ᴿ U →
      y ∈ᴿ U

    real-lower-rounded :
      (x : DedekindCut ℓ) →
      x ∈ᴿ L →
      ∥ Σ[ y ∈ DedekindCut ℓ ] (Order._<_ {ℓ = ℓ} x y) × (y ∈ᴿ L) ∥₁

    real-upper-rounded :
      (x : DedekindCut ℓ) →
      x ∈ᴿ U →
      ∥ Σ[ y ∈ DedekindCut ℓ ] (Order._<_ {ℓ = ℓ} y x) × (y ∈ᴿ U) ∥₁

    real-disjoint :
      (x : DedekindCut ℓ) →
      x ∈ᴿ L →
      x ∈ᴿ U →
      ⊥

    real-located :
      (x y : DedekindCut ℓ) →
      Order._<_ {ℓ = ℓ} x y →
      ∥ (x ∈ᴿ L) ⊎ (y ∈ᴿ U) ∥₁


record RealValuedCut (ℓ : Level) : Type (ℓ-suc ℓ) where
  no-eta-equality

  field
    realLower : RealPred ℓ
    realUpper : RealPred ℓ
    is-real-cut : isRealValuedCut realLower realUpper

  open isRealValuedCut is-real-cut public


open RealValuedCut public


representingLower : {ℓ : Level} → RealValuedCut ℓ → ℚPred ℓ
representingLower {ℓ = ℓ} C q =
  (ℚ→DedekindCutAt ℓ q ∈ᴿ realLower C) ,
  isProp∈ᴿ (realLower C) (ℚ→DedekindCutAt ℓ q)


representingUpper : {ℓ : Level} → RealValuedCut ℓ → ℚPred ℓ
representingUpper {ℓ = ℓ} C q =
  (ℚ→DedekindCutAt ℓ q ∈ᴿ realUpper C) ,
  isProp∈ᴿ (realUpper C) (ℚ→DedekindCutAt ℓ q)


representing-is-cut :
  {ℓ : Level} →
  (C : RealValuedCut ℓ) →
  isDedekindCut (representingLower C) (representingUpper C)
representing-is-cut {ℓ = ℓ} C .isDedekindCut.lower-inhabited =
  Prop.rec squash₁ from-real
    (real-lower-inhabited C)
  where
  module Arch = Archimedean {ℓ}

  from-real :
    Σ[ x ∈ DedekindCut ℓ ] x ∈ᴿ realLower C →
    ∥ Σ[ q ∈ ℚ ] q ∈ representingLower C ∥₁
  from-real (x , x∈L) =
    Prop.rec squash₁
      (λ (n , q<x) →
        let q = ℚ.- ℚExtra.natMul n ℚExtra.1ℚ in
        ∣ q
        , real-lower-closed C
            (ℚ→DedekindCutAt ℓ q)
            x
            q<x
            x∈L
        ∣₁)
      (Arch.lower-rational-bound x)
representing-is-cut {ℓ = ℓ} C .isDedekindCut.upper-inhabited =
  Prop.rec squash₁ from-real
    (real-upper-inhabited C)
  where
  module Arch = Archimedean {ℓ}

  from-real :
    Σ[ x ∈ DedekindCut ℓ ] x ∈ᴿ realUpper C →
    ∥ Σ[ q ∈ ℚ ] q ∈ representingUpper C ∥₁
  from-real (x , x∈U) =
    Prop.rec squash₁
      (λ (n , x<q) →
        let q = ℚExtra.natMul n ℚExtra.1ℚ in
        ∣ q
        , real-upper-closed C
            x
            (ℚ→DedekindCutAt ℓ q)
            x<q
            x∈U
        ∣₁)
      (Arch.upper-rational-bound x)
representing-is-cut {ℓ = ℓ} C .isDedekindCut.lower-closed =
  λ p q p<q q∈L →
    real-lower-closed C
      (ℚ→DedekindCutAt ℓ p)
      (ℚ→DedekindCutAt ℓ q)
      (RationalEmbeddingAt.ℚ→<-pres {ℓ = ℓ} p q p<q)
      q∈L
representing-is-cut {ℓ = ℓ} C .isDedekindCut.upper-closed =
  λ p q p<q p∈U →
    real-upper-closed C
      (ℚ→DedekindCutAt ℓ p)
      (ℚ→DedekindCutAt ℓ q)
      (RationalEmbeddingAt.ℚ→<-pres {ℓ = ℓ} p q p<q)
      p∈U
representing-is-cut {ℓ = ℓ} C .isDedekindCut.lower-rounded =
  λ q q∈L →
    Prop.rec squash₁
      (λ (y , q<y , y∈L) →
        Prop.rec squash₁
          (λ (r , q<r , r<y) →
            ∣ r
            , RationalEmbeddingAt.ℚ→<-reflect {ℓ = ℓ} q r q<r
            , real-lower-closed C
                (ℚ→DedekindCutAt ℓ r)
                y
                r<y
                y∈L
            ∣₁)
          (Order.rational-between
            (ℚ→DedekindCutAt ℓ q)
            y
            q<y))
      (real-lower-rounded C (ℚ→DedekindCutAt ℓ q) q∈L)
representing-is-cut {ℓ = ℓ} C .isDedekindCut.upper-rounded =
  λ q q∈U →
    Prop.rec squash₁
      (λ (y , y<q , y∈U) →
        Prop.rec squash₁
          (λ (r , y<r , r<q) →
            ∣ r
            , RationalEmbeddingAt.ℚ→<-reflect {ℓ = ℓ} r q r<q
            , real-upper-closed C
                y
                (ℚ→DedekindCutAt ℓ r)
                y<r
                y∈U
            ∣₁)
          (Order.rational-between
            y
            (ℚ→DedekindCutAt ℓ q)
            y<q))
      (real-upper-rounded C (ℚ→DedekindCutAt ℓ q) q∈U)
representing-is-cut {ℓ = ℓ} C .isDedekindCut.disjoint =
  λ q → real-disjoint C (ℚ→DedekindCutAt ℓ q)
representing-is-cut {ℓ = ℓ} C .isDedekindCut.located =
  λ p q p<q →
    Prop.rec squash₁
      (λ where
        (Sum.inl p∈L) → ∣ Sum.inl p∈L ∣₁
        (Sum.inr q∈U) → ∣ Sum.inr q∈U ∣₁)
      (real-located C
        (ℚ→DedekindCutAt ℓ p)
        (ℚ→DedekindCutAt ℓ q)
        (RationalEmbeddingAt.ℚ→<-pres {ℓ = ℓ} p q p<q))


representing-cut : {ℓ : Level} → RealValuedCut ℓ → DedekindCut ℓ
representing-cut C .lower = representingLower C
representing-cut C .upper = representingUpper C
representing-cut C .is-cut = representing-is-cut C


represented-lower :
  {ℓ : Level} →
  (C : RealValuedCut ℓ) (x : DedekindCut ℓ) →
  (x ∈ᴿ realLower C → Order._<_ {ℓ = ℓ} x (representing-cut C))
  ×
  (Order._<_ {ℓ = ℓ} x (representing-cut C) → x ∈ᴿ realLower C)
represented-lower {ℓ = ℓ} C x = to , from
  where
  module O = Order {ℓ}

  to :
    x ∈ᴿ realLower C →
    O._<_ x (representing-cut C)
  to x∈L =
    Prop.rec squash₁
      (λ (y , x<y , y∈L) →
        Prop.rec squash₁
          (λ (q , x<q , q<y) →
            ∣ q
            , O.<ℚ→upper x q x<q
            , real-lower-closed C
                (ℚ→DedekindCutAt ℓ q)
                y
                q<y
                y∈L
            ∣₁)
          (O.rational-between x y x<y))
      (real-lower-rounded C x x∈L)

  from :
    O._<_ x (representing-cut C) →
    x ∈ᴿ realLower C
  from =
    Prop.rec (isProp∈ᴿ (realLower C) x)
      (λ (q , q∈Ux , q∈L) →
        real-lower-closed C
          x
          (ℚ→DedekindCutAt ℓ q)
          (O.upper→<ℚ x q q∈Ux)
          q∈L)


represented-upper :
  {ℓ : Level} →
  (C : RealValuedCut ℓ) (x : DedekindCut ℓ) →
  (x ∈ᴿ realUpper C → Order._<_ {ℓ = ℓ} (representing-cut C) x)
  ×
  (Order._<_ {ℓ = ℓ} (representing-cut C) x → x ∈ᴿ realUpper C)
represented-upper {ℓ = ℓ} C x = to , from
  where
  module O = Order {ℓ}

  to :
    x ∈ᴿ realUpper C →
    O._<_ (representing-cut C) x
  to x∈U =
    Prop.rec squash₁
      (λ (y , y<x , y∈U) →
        Prop.rec squash₁
          (λ (q , y<q , q<x) →
            ∣ q
            , real-upper-closed C
                y
                (ℚ→DedekindCutAt ℓ q)
                y<q
                y∈U
            , O.ℚ<→lower x q q<x
            ∣₁)
          (O.rational-between y x y<x))
      (real-upper-rounded C x x∈U)

  from :
    O._<_ (representing-cut C) x →
    x ∈ᴿ realUpper C
  from =
    Prop.rec (isProp∈ᴿ (realUpper C) x)
      (λ (q , q∈U , q∈Lx) →
        real-upper-closed C
          (ℚ→DedekindCutAt ℓ q)
          x
          (O.lower→ℚ< x q q∈Lx)
          q∈U)


representsLower :
  {ℓ : Level} →
  RealValuedCut ℓ →
  DedekindCut ℓ →
  Type (ℓ-suc ℓ)
representsLower C z =
  (x : DedekindCut _) →
    (x ∈ᴿ realLower C → Order._<_ x z)
    ×
    (Order._<_ x z → x ∈ᴿ realLower C)


representing-cut-unique :
  {ℓ : Level} →
  (C : RealValuedCut ℓ) (z : DedekindCut ℓ) →
  representsLower C z →
  z ≡ representing-cut C
representing-cut-unique {ℓ = ℓ} C z z-rep =
  O.≤-antisym z (representing-cut C) z≤rep rep≤z
  where
  module O = Order {ℓ}

  z≤rep : O._≤_ z (representing-cut C)
  z≤rep q q∈Lz =
    z-rep (ℚ→DedekindCutAt ℓ q) .snd
      (O.lower→ℚ< z q q∈Lz)

  rep≤z : O._≤_ (representing-cut C) z
  rep≤z q q∈Lrep =
    O.ℚ<→lower z q
      (z-rep (ℚ→DedekindCutAt ℓ q) .fst q∈Lrep)


representing-cut-representsLower :
  {ℓ : Level} →
  (C : RealValuedCut ℓ) →
  representsLower C (representing-cut C)
representing-cut-representsLower C x = represented-lower C x
