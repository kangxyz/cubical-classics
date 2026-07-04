{-

Constructive Dedekind completeness for constructive Dedekind reals

Dedekind completeness is stated in representation form: every located cut of
Dedekind reals is represented by a unique Dedekind real.  No LEM or resizing
is used here.

-}
{-# OPTIONS --safe #-}
module Constructive.DedekindReals.Completeness where

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

open import Constructive.DedekindReals
import Constructive.Rationals as ℚExtra

private
  variable
    ℓ : Level


RealPred : (ℓ : Level) → Type (ℓ-suc ℓ)
RealPred ℓ = DedekindReal ℓ → hProp ℓ

_∈ᴿ_ : DedekindReal ℓ → RealPred ℓ → Type ℓ
x ∈ᴿ P = P x .fst

infix 4 _∈ᴿ_

isProp∈ᴿ : (P : RealPred ℓ) → (x : DedekindReal ℓ) → isProp (x ∈ᴿ P)
isProp∈ᴿ P x = P x .snd


record IsRealValuedCut (L U : RealPred ℓ) : Type (ℓ-suc ℓ) where
  no-eta-equality

  field
    real-lower-inhabited :
      ∥ Σ[ x ∈ DedekindReal ℓ ] x ∈ᴿ L ∥₁

    real-upper-inhabited :
      ∥ Σ[ x ∈ DedekindReal ℓ ] x ∈ᴿ U ∥₁

    real-lower-closed :
      (x y : DedekindReal ℓ) →
      Order._<_ {ℓ = ℓ} x y →
      y ∈ᴿ L →
      x ∈ᴿ L

    real-upper-closed :
      (x y : DedekindReal ℓ) →
      Order._<_ {ℓ = ℓ} x y →
      x ∈ᴿ U →
      y ∈ᴿ U

    real-lower-rounded :
      (x : DedekindReal ℓ) →
      x ∈ᴿ L →
      ∥ Σ[ y ∈ DedekindReal ℓ ] (Order._<_ {ℓ = ℓ} x y) × (y ∈ᴿ L) ∥₁

    real-upper-rounded :
      (x : DedekindReal ℓ) →
      x ∈ᴿ U →
      ∥ Σ[ y ∈ DedekindReal ℓ ] (Order._<_ {ℓ = ℓ} y x) × (y ∈ᴿ U) ∥₁

    real-disjoint :
      (x : DedekindReal ℓ) →
      x ∈ᴿ L →
      x ∈ᴿ U →
      ⊥

    real-located :
      (x y : DedekindReal ℓ) →
      Order._<_ {ℓ = ℓ} x y →
      ∥ (x ∈ᴿ L) ⊎ (y ∈ᴿ U) ∥₁


record RealValuedCut (ℓ : Level) : Type (ℓ-suc ℓ) where
  no-eta-equality

  field
    realLower : RealPred ℓ
    realUpper : RealPred ℓ
    isRealValuedCut : IsRealValuedCut realLower realUpper

  open IsRealValuedCut isRealValuedCut public


open RealValuedCut public


representingLower : {ℓ : Level} → RealValuedCut ℓ → ℚPred ℓ
representingLower {ℓ = ℓ} C q =
  (ℚ→𝔻 ℓ q ∈ᴿ realLower C) ,
  isProp∈ᴿ (realLower C) (ℚ→𝔻 ℓ q)


representingUpper : {ℓ : Level} → RealValuedCut ℓ → ℚPred ℓ
representingUpper {ℓ = ℓ} C q =
  (ℚ→𝔻 ℓ q ∈ᴿ realUpper C) ,
  isProp∈ᴿ (realUpper C) (ℚ→𝔻 ℓ q)


isDedekindRealRepresenting :
  {ℓ : Level} →
  (C : RealValuedCut ℓ) →
  IsDedekindReal (representingLower C) (representingUpper C)
isDedekindRealRepresenting {ℓ = ℓ} C .IsDedekindReal.lower-inhabited =
  Prop.rec squash₁ from-real
    (real-lower-inhabited C)
  where
  module Arch = Archimedean {ℓ}

  from-real :
    Σ[ x ∈ DedekindReal ℓ ] x ∈ᴿ realLower C →
    ∥ Σ[ q ∈ ℚ ] q ∈ representingLower C ∥₁
  from-real (x , x∈L) =
    Prop.rec squash₁
      (λ (n , q<x) →
        let q = ℚ.- ℚExtra.natMul n ℚExtra.1ℚ in
        ∣ q
        , real-lower-closed C
            (ℚ→𝔻 ℓ q)
            x
            q<x
            x∈L
        ∣₁)
      (Arch.lower-rational-bound x)
isDedekindRealRepresenting {ℓ = ℓ} C .IsDedekindReal.upper-inhabited =
  Prop.rec squash₁ from-real
    (real-upper-inhabited C)
  where
  module Arch = Archimedean {ℓ}

  from-real :
    Σ[ x ∈ DedekindReal ℓ ] x ∈ᴿ realUpper C →
    ∥ Σ[ q ∈ ℚ ] q ∈ representingUpper C ∥₁
  from-real (x , x∈U) =
    Prop.rec squash₁
      (λ (n , x<q) →
        let q = ℚExtra.natMul n ℚExtra.1ℚ in
        ∣ q
        , real-upper-closed C
            x
            (ℚ→𝔻 ℓ q)
            x<q
            x∈U
        ∣₁)
      (Arch.upper-rational-bound x)
isDedekindRealRepresenting {ℓ = ℓ} C .IsDedekindReal.lower-closed =
  λ p q p<q q∈L →
    real-lower-closed C
      (ℚ→𝔻 ℓ p)
      (ℚ→𝔻 ℓ q)
      (RationalEmbedding.ℚ→<-pres {ℓ = ℓ} p q p<q)
      q∈L
isDedekindRealRepresenting {ℓ = ℓ} C .IsDedekindReal.upper-closed =
  λ p q p<q p∈U →
    real-upper-closed C
      (ℚ→𝔻 ℓ p)
      (ℚ→𝔻 ℓ q)
      (RationalEmbedding.ℚ→<-pres {ℓ = ℓ} p q p<q)
      p∈U
isDedekindRealRepresenting {ℓ = ℓ} C .IsDedekindReal.lower-rounded =
  λ q q∈L →
    Prop.rec squash₁
      (λ (y , q<y , y∈L) →
        Prop.rec squash₁
          (λ (r , q<r , r<y) →
            ∣ r
            , RationalEmbedding.ℚ→<-reflect {ℓ = ℓ} q r q<r
            , real-lower-closed C
                (ℚ→𝔻 ℓ r)
                y
                r<y
                y∈L
            ∣₁)
          (Order.rational-between
            (ℚ→𝔻 ℓ q)
            y
            q<y))
      (real-lower-rounded C (ℚ→𝔻 ℓ q) q∈L)
isDedekindRealRepresenting {ℓ = ℓ} C .IsDedekindReal.upper-rounded =
  λ q q∈U →
    Prop.rec squash₁
      (λ (y , y<q , y∈U) →
        Prop.rec squash₁
          (λ (r , y<r , r<q) →
            ∣ r
            , RationalEmbedding.ℚ→<-reflect {ℓ = ℓ} r q r<q
            , real-upper-closed C
                y
                (ℚ→𝔻 ℓ r)
                y<r
                y∈U
            ∣₁)
          (Order.rational-between
            y
            (ℚ→𝔻 ℓ q)
            y<q))
      (real-upper-rounded C (ℚ→𝔻 ℓ q) q∈U)
isDedekindRealRepresenting {ℓ = ℓ} C .IsDedekindReal.disjoint =
  λ q → real-disjoint C (ℚ→𝔻 ℓ q)
isDedekindRealRepresenting {ℓ = ℓ} C .IsDedekindReal.located =
  λ p q p<q →
    Prop.rec squash₁
      (λ where
        (Sum.inl p∈L) → ∣ Sum.inl p∈L ∣₁
        (Sum.inr q∈U) → ∣ Sum.inr q∈U ∣₁)
      (real-located C
        (ℚ→𝔻 ℓ p)
        (ℚ→𝔻 ℓ q)
        (RationalEmbedding.ℚ→<-pres {ℓ = ℓ} p q p<q))


representing-real : {ℓ : Level} → RealValuedCut ℓ → DedekindReal ℓ
representing-real C .lower = representingLower C
representing-real C .upper = representingUpper C
representing-real C .isDedekindReal = isDedekindRealRepresenting C


represented-lower :
  {ℓ : Level} →
  (C : RealValuedCut ℓ) (x : DedekindReal ℓ) →
  (x ∈ᴿ realLower C → Order._<_ {ℓ = ℓ} x (representing-real C))
  ×
  (Order._<_ {ℓ = ℓ} x (representing-real C) → x ∈ᴿ realLower C)
represented-lower {ℓ = ℓ} C x = to , from
  where
  module O = Order {ℓ}

  to :
    x ∈ᴿ realLower C →
    O._<_ x (representing-real C)
  to x∈L =
    Prop.rec squash₁
      (λ (y , x<y , y∈L) →
        Prop.rec squash₁
          (λ (q , x<q , q<y) →
            ∣ q
            , O.<ℚ→upper x q x<q
            , real-lower-closed C
                (ℚ→𝔻 ℓ q)
                y
                q<y
                y∈L
            ∣₁)
          (O.rational-between x y x<y))
      (real-lower-rounded C x x∈L)

  from :
    O._<_ x (representing-real C) →
    x ∈ᴿ realLower C
  from =
    Prop.rec (isProp∈ᴿ (realLower C) x)
      (λ (q , q∈Ux , q∈L) →
        real-lower-closed C
          x
          (ℚ→𝔻 ℓ q)
          (O.upper→<ℚ x q q∈Ux)
          q∈L)


represented-upper :
  {ℓ : Level} →
  (C : RealValuedCut ℓ) (x : DedekindReal ℓ) →
  (x ∈ᴿ realUpper C → Order._<_ {ℓ = ℓ} (representing-real C) x)
  ×
  (Order._<_ {ℓ = ℓ} (representing-real C) x → x ∈ᴿ realUpper C)
represented-upper {ℓ = ℓ} C x = to , from
  where
  module O = Order {ℓ}

  to :
    x ∈ᴿ realUpper C →
    O._<_ (representing-real C) x
  to x∈U =
    Prop.rec squash₁
      (λ (y , y<x , y∈U) →
        Prop.rec squash₁
          (λ (q , y<q , q<x) →
            ∣ q
            , real-upper-closed C
                y
                (ℚ→𝔻 ℓ q)
                y<q
                y∈U
            , O.ℚ<→lower x q q<x
            ∣₁)
          (O.rational-between y x y<x))
      (real-upper-rounded C x x∈U)

  from :
    O._<_ (representing-real C) x →
    x ∈ᴿ realUpper C
  from =
    Prop.rec (isProp∈ᴿ (realUpper C) x)
      (λ (q , q∈U , q∈Lx) →
        real-upper-closed C
          (ℚ→𝔻 ℓ q)
          x
          (O.lower→ℚ< x q q∈Lx)
          q∈U)


representsLower :
  {ℓ : Level} →
  RealValuedCut ℓ →
  DedekindReal ℓ →
  Type (ℓ-suc ℓ)
representsLower {ℓ = ℓ} C z =
  (x : DedekindReal ℓ) →
    (x ∈ᴿ realLower C → Order._<_ x z)
    ×
    (Order._<_ x z → x ∈ᴿ realLower C)


representsCut :
  {ℓ : Level} →
  RealValuedCut ℓ →
  DedekindReal ℓ →
  Type (ℓ-suc ℓ)
representsCut {ℓ = ℓ} C z =
  representsLower C z
  ×
  ((x : DedekindReal ℓ) →
    (x ∈ᴿ realUpper C → Order._<_ z x)
    ×
    (Order._<_ z x → x ∈ᴿ realUpper C))


-- Dedekind completeness, in this same-universe constructive form, says that
-- every located cut whose elements are Dedekind reals is represented by a
-- unique Dedekind real.  A representative `z` means exactly that the lower
-- side of the real-valued cut is the predicate `x < z`, and the upper side is
-- the predicate `z < x`.
isDedekindComplete : {ℓ : Level} → Type (ℓ-suc ℓ)
isDedekindComplete {ℓ = ℓ} =
  (C : RealValuedCut ℓ) →
  Σ[ z ∈ DedekindReal ℓ ]
    representsCut C z
    ×
    ((z' : DedekindReal ℓ) → representsCut C z' → z' ≡ z)


representing-real-unique :
  {ℓ : Level} →
  (C : RealValuedCut ℓ) (z : DedekindReal ℓ) →
  representsLower C z →
  z ≡ representing-real C
representing-real-unique {ℓ = ℓ} C z z-rep =
  O.≤-antisym z (representing-real C) z≤rep rep≤z
  where
  module O = Order {ℓ}

  z≤rep : O._≤_ z (representing-real C)
  z≤rep q q∈Lz =
    z-rep (ℚ→𝔻 ℓ q) .snd
      (O.lower→ℚ< z q q∈Lz)

  rep≤z : O._≤_ (representing-real C) z
  rep≤z q q∈Lrep =
    O.ℚ<→lower z q
      (z-rep (ℚ→𝔻 ℓ q) .fst q∈Lrep)


representing-real-representsLower :
  {ℓ : Level} →
  (C : RealValuedCut ℓ) →
  representsLower C (representing-real C)
representing-real-representsLower C x = represented-lower C x


representing-real-representsCut :
  {ℓ : Level} →
  (C : RealValuedCut ℓ) →
  representsCut C (representing-real C)
representing-real-representsCut C =
  representing-real-representsLower C ,
  represented-upper C


isDedekindCompleteDedekindReal : {ℓ : Level} → isDedekindComplete {ℓ = ℓ}
isDedekindCompleteDedekindReal C =
  representing-real C ,
  representing-real-representsCut C ,
  λ z z-rep → representing-real-unique C z (z-rep .fst)
