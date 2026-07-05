{-

Arithmetic for constructive Dedekind completions

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.DedekindCompletion.Arithmetic.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Relation.Nullary
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Algebra.LinearlyOrderedCommRing
open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedes
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.DedekindCompletion

private
  variable
    ℓ ℓ' ℓᴾ : Level


private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (p δ nδ : 𝓡 .fst) → p + (nδ + δ) ≡ (p + δ) + nδ
    helper1 _ _ _ = solve! 𝓡

    helper2 : (δ : 𝓡 .fst) → δ + 0r ≡ δ
    helper2 _ = solve! 𝓡

    helper3 : (p δ : 𝓡 .fst) → (p + δ) + δ ≡ p + (δ + δ)
    helper3 _ _ = solve! 𝓡

    helper4 : (p q : 𝓡 .fst) → p + (q - p) ≡ q
    helper4 _ _ = solve! 𝓡


module ArithmeticBase (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') where

  𝒦 : LinearlyOrderedField ℓ ℓ'
  𝒦 = 𝒜 .fst

  archimedes : isArchimedean (𝒦 .fst)
  archimedes = 𝒜 .snd

  private
    K : Type ℓ
    K = CompletionBase.Carrier 𝒦

  open CompletionBase 𝒦
  module O = CompletionOrder 𝒦
  open LinearlyOrderedFieldStr 𝒦
  open Helpers (LinearlyOrderedCommRing→CommRing (𝒦 .fst))


  module Approximation {ℓᴾ : Level} where

    CloseBounds : DedekindCompletion ℓᴾ → K → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
    CloseBounds x ε =
      Σ[ p ∈ K ] Σ[ q ∈ K ]
        (p ∈ lower x) ×
        (q ∈ upper x) ×
        (p < q) ×
        (q < p + ε)

    BoundedCloseBounds : DedekindCompletion ℓᴾ → K → K → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴾ))
    BoundedCloseBounds x ε u =
      Σ[ p ∈ K ] Σ[ q ∈ K ]
        (p ∈ lower x) ×
        (q ∈ upper x) ×
        (p < q) ×
        (q < p + ε) ×
        (q ≤ u)

    private
      bounded→close :
        (x : DedekindCompletion ℓᴾ) (ε u : K) →
        BoundedCloseBounds x ε u → CloseBounds x ε
      bounded→close x ε u (p , q , p∈Lx , q∈Ux , p<q , q<p+ε , _) =
        p , q , p∈Lx , q∈Ux , p<q , q<p+ε

    bounded-rounded-upper-close :
      (x : DedekindCompletion ℓᴾ) (ε p q u : K) →
      p ∈ lower x →
      q ∈ upper x →
      q ≤ p + ε →
      q ≤ u →
      ∥ BoundedCloseBounds x ε u ∥₁
    bounded-rounded-upper-close x ε p q u p∈Lx q∈Ux q≤p+ε q≤u =
      Prop.rec squash₁
        (λ (r , r<q , r∈Ux) →
          ∣ p , r
          , p∈Lx
          , r∈Ux
          , O.lower<upper x p r p∈Lx r∈Ux
          , <≤-trans r<q q≤p+ε
          , <-≤-weaken (<≤-trans r<q q≤u)
          ∣₁)
        (CompletionBase.upper-rounded {𝒦 = 𝒦} x q q∈Ux)

    bounded-close-from-< :
      (x : DedekindCompletion ℓᴾ) (ε p q u : K) →
      p ∈ lower x →
      q ∈ upper x →
      q < p + ε →
      q ≤ u →
      ∥ BoundedCloseBounds x ε u ∥₁
    bounded-close-from-< x ε p q u p∈Lx q∈Ux q<p+ε q≤u =
      bounded-rounded-upper-close x ε p q u p∈Lx q∈Ux
        (<-≤-weaken q<p+ε)
        q≤u

    step-bound :
      (p δ : K) (n : ℕ) →
      p + (suc (suc n) ⋆ δ) ≡ (p + δ) + (suc n ⋆ δ)
    step-bound p δ n =
      (λ i → p + sucn⋆q≡n⋆q+q (suc n) δ i) ∙
      helper1 p δ (suc n ⋆ δ)

    δ+0≡δ : (δ : K) → δ + 0r ≡ δ
    δ+0≡δ = helper2

    δ<δ+δ : (δ : K) → δ > 0r → δ < δ + δ
    δ<δ+δ δ δ>0 =
      subst (_< δ + δ) (+IdL δ) (+-rPres< δ>0)

    n⋆δ<sn⋆δ : (n : ℕ) (δ : K) → δ > 0r → n ⋆ δ < suc n ⋆ δ
    n⋆δ<sn⋆δ n δ δ>0 =
      subst (n ⋆ δ <_) (sym (sucn⋆q≡n⋆q+q n δ))
        (subst (_< n ⋆ δ + δ) (δ+0≡δ (n ⋆ δ))
          (+-lPres< {z = n ⋆ δ} δ>0))

    bounded-scan-close :
      (x : DedekindCompletion ℓᴾ) (ε δ : K) →
      δ > 0r →
      δ + δ ≡ ε →
      (n : ℕ) (p q u : K) →
      p ∈ lower x →
      q ∈ upper x →
      q ≤ p + (suc n ⋆ δ) →
      q ≤ u →
      ∥ BoundedCloseBounds x ε u ∥₁
    bounded-scan-close x ε δ δ>0 δ+δ≡ε zero p q u p∈Lx q∈Ux q≤p+δ q≤u =
      bounded-close-from-< x ε p q u p∈Lx q∈Ux q<p+ε q≤u
      where
      q≤p+δ' : q ≤ p + δ
      q≤p+δ' =
        subst (λ r → q ≤ p + r)
          (1⋆q≡q δ)
          q≤p+δ

      δ<ε : δ < ε
      δ<ε =
        <≤-trans (δ<δ+δ δ δ>0) (≤-refl δ+δ≡ε)

      p+δ<p+ε : p + δ < p + ε
      p+δ<p+ε = +-lPres< δ<ε

      q<p+ε : q < p + ε
      q<p+ε =
        ≤<-trans q≤p+δ' p+δ<p+ε
    bounded-scan-close x ε δ δ>0 δ+δ≡ε (suc n) p q u p∈Lx q∈Ux q≤bound q≤u =
      Prop.rec squash₁ step
        (CompletionBase.located {𝒦 = 𝒦} x p₁ p₂ p₁<p₂)
      where
      p₁ : K
      p₁ = p + δ

      p₂ : K
      p₂ = p₁ + δ

      p₁<p₂ : p₁ < p₂
      p₁<p₂ =
        subst (_< p₂) (δ+0≡δ p₁) (+-lPres< {z = p₁} δ>0)

      p₂≡p+ε : p₂ ≡ p + ε
      p₂≡p+ε =
        helper3 p δ ∙ cong (p +_) δ+δ≡ε

      p₂≤p+ε : p₂ ≤ p + ε
      p₂≤p+ε = ≤-refl p₂≡p+ε

      q≤shifted : q ≤ p₁ + (suc n ⋆ δ)
      q≤shifted =
        subst (λ r → q ≤ r)
          (step-bound p δ n)
          q≤bound

      close-with-p₂ :
        p₂ ∈ upper x →
        ∥ BoundedCloseBounds x ε u ∥₁
      close-with-p₂ p₂∈Ux with trichotomy p₂ q
      ... | lt p₂<q =
        bounded-rounded-upper-close x ε p p₂ u p∈Lx p₂∈Ux
          p₂≤p+ε
          (<-≤-weaken (<≤-trans p₂<q q≤u))
      ... | eq p₂≡q =
        bounded-rounded-upper-close x ε p p₂ u p∈Lx p₂∈Ux
          p₂≤p+ε
          (≤-trans (≤-refl p₂≡q) q≤u)
      ... | gt q<p₂ =
        bounded-rounded-upper-close x ε p q u p∈Lx q∈Ux
          (<-≤-weaken (subst (λ r → q < r) p₂≡p+ε q<p₂))
          q≤u

      step :
        (p₁ ∈ lower x) ⊎ (p₂ ∈ upper x) →
        ∥ BoundedCloseBounds x ε u ∥₁
      step (Sum.inl p₁∈Lx) =
        bounded-scan-close x ε δ δ>0 δ+δ≡ε n p₁ q u
          p₁∈Lx q∈Ux q≤shifted q≤u
      step (Sum.inr p₂∈Ux) =
        close-with-p₂ p₂∈Ux

    bounded-close-bounds :
      (x : DedekindCompletion ℓᴾ) (ε u : K) →
      ε > 0r →
      u ∈ upper x →
      ∥ BoundedCloseBounds x ε u ∥₁
    bounded-close-bounds x ε u ε>0 u∈Ux =
      Prop.rec squash₁ initial
        (CompletionBase.lower-inhabited {𝒦 = 𝒦} x)
      where
      δ : K
      δ = middle 0r ε

      δ>0 : δ > 0r
      δ>0 = middle>l ε>0

      δ+δ≡ε : δ + δ ≡ ε
      δ+δ≡ε = x/2+x/2≡x ε

      initial :
        Σ[ p ∈ K ] p ∈ lower x →
        ∥ BoundedCloseBounds x ε u ∥₁
      initial (p , p∈Lx) =
        bounded-scan-close x ε δ δ>0 δ+δ≡ε n p u u
          p∈Lx u∈Ux u≤p+sucnδ (≤-refl refl)
        where
        n : ℕ
        n = fst (archimedes (u - p) δ δ>0)

        u-p<nδ : u - p < n ⋆ δ
        u-p<nδ = snd (archimedes (u - p) δ δ>0)

        u<p+nδ : u < p + (n ⋆ δ)
        u<p+nδ =
          -MoveLToR<' u-p<nδ

        p+nδ<p+sucnδ :
          p + (n ⋆ δ) < p + (suc n ⋆ δ)
        p+nδ<p+sucnδ =
          +-lPres< (n⋆δ<sn⋆δ n δ δ>0)

        u<p+sucnδ : u < p + (suc n ⋆ δ)
        u<p+sucnδ =
          <-trans u<p+nδ p+nδ<p+sucnδ

        u≤p+sucnδ : u ≤ p + (suc n ⋆ δ)
        u≤p+sucnδ =
          <-≤-weaken u<p+sucnδ

    close-bounds :
      (x : DedekindCompletion ℓᴾ) (ε : K) →
      ε > 0r →
      ∥ CloseBounds x ε ∥₁
    close-bounds x ε ε>0 =
      Prop.rec squash₁
        (λ (u , u∈Ux) →
          Prop.rec squash₁
            (λ close → ∣ bounded→close x ε u close ∣₁)
            (bounded-close-bounds x ε u ε>0 u∈Ux))
        (CompletionBase.upper-inhabited {𝒦 = 𝒦} x)


  module Addition {ℓᴾ : Level} where
    open Approximation {ℓᴾ}

    0𝔻 : DedekindCompletion ℓᴾ
    0𝔻 = K→𝔻 ℓᴾ 0r

    1𝔻 : DedekindCompletion ℓᴾ
    1𝔻 = K→𝔻 ℓᴾ 1r

    addLower : DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ → Pred ℓᴾ
    addLower x y q =
      ∥ Σ[ r ∈ K ] Σ[ s ∈ K ]
        (r ∈ lower x) ×
        (s ∈ lower y) ×
        (q < r + s) ∥₁ ,
      squash₁

    addUpper : DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ → Pred ℓᴾ
    addUpper x y q =
      ∥ Σ[ r ∈ K ] Σ[ s ∈ K ]
        (r ∈ upper x) ×
        (s ∈ upper y) ×
        (r + s < q) ∥₁ ,
      squash₁

    private
      sum-close-upper< :
        (lx ly ux uy η p q : K) →
        ux < lx + η →
        uy < ly + η →
        lx + ly ≤ p →
        η + η ≡ q - p →
        p < q →
        ux + uy < q
      sum-close-upper< lx ly ux uy η p q ux<lx+η uy<ly+η lx+ly≤p η+η≡q-p p<q =
        <≤-trans ux+uy<lx+ly+η+η lx+ly+η+η≤q
        where
        ux+uy<lx+η+ly+η : ux + uy < (lx + η) + (ly + η)
        ux+uy<lx+η+ly+η = +-Pres< ux<lx+η uy<ly+η

        regroup : (lx + η) + (ly + η) ≡ (lx + ly) + (η + η)
        regroup = solve! (LinearlyOrderedCommRing→CommRing (𝒦 .fst))

        ux+uy<lx+ly+η+η : ux + uy < (lx + ly) + (η + η)
        ux+uy<lx+ly+η+η =
          subst (ux + uy <_) regroup ux+uy<lx+η+ly+η

        lx+ly+η+η≤p+η+η : (lx + ly) + (η + η) ≤ p + (η + η)
        lx+ly+η+η≤p+η+η = +-rPres≤ lx+ly≤p

        p+η+η≡q : p + (η + η) ≡ q
        p+η+η≡q =
          cong (p +_) η+η≡q-p ∙
          helper4 p q

        lx+ly+η+η≤q : (lx + ly) + (η + η) ≤ q
        lx+ly+η+η≤q =
          ≤-trans lx+ly+η+η≤p+η+η (≤-refl p+η+η≡q)

    isDedekindCut+ :
      (x y : DedekindCompletion ℓᴾ) →
      IsDedekindCut (addLower x y) (addUpper x y)
    isDedekindCut+ x y .IsDedekindCut.lower-inhabited =
      Prop.rec2 squash₁
        (λ (p , p∈Lx) (q , q∈Ly) →
          ∣ (p + q) - 1r
          , ∣ p , q , p∈Lx , q∈Ly , q-1<q ∣₁
          ∣₁)
        (CompletionBase.lower-inhabited {𝒦 = 𝒦} x)
        (CompletionBase.lower-inhabited {𝒦 = 𝒦} y)
    isDedekindCut+ x y .IsDedekindCut.upper-inhabited =
      Prop.rec2 squash₁
        (λ (p , p∈Ux) (q , q∈Uy) →
          ∣ (p + q) + 1r
          , ∣ p , q , p∈Ux , q∈Uy , q+1>q ∣₁
          ∣₁)
        (CompletionBase.upper-inhabited {𝒦 = 𝒦} x)
        (CompletionBase.upper-inhabited {𝒦 = 𝒦} y)
    isDedekindCut+ x y .IsDedekindCut.lower-closed =
      λ p q p<q →
        Prop.rec squash₁
          (λ (r , s , r∈Lx , s∈Ly , q<r+s) →
            ∣ r , s , r∈Lx , s∈Ly
            , <-trans p<q q<r+s
            ∣₁)
    isDedekindCut+ x y .IsDedekindCut.upper-closed =
      λ p q p<q →
        Prop.rec squash₁
          (λ (r , s , r∈Ux , s∈Uy , r+s<p) →
            ∣ r , s , r∈Ux , s∈Uy
            , <-trans r+s<p p<q
            ∣₁)
    isDedekindCut+ x y .IsDedekindCut.lower-rounded =
      λ q →
        Prop.rec squash₁
          (λ (r , s , r∈Lx , s∈Ly , q<r+s) →
            let m = middle q (r + s) in
            ∣ m
            , middle>l q<r+s
            , ∣ r , s , r∈Lx , s∈Ly , middle<r q<r+s ∣₁
            ∣₁)
    isDedekindCut+ x y .IsDedekindCut.upper-rounded =
      λ q →
        Prop.rec squash₁
          (λ (r , s , r∈Ux , s∈Uy , r+s<q) →
            let m = middle (r + s) q in
            ∣ m
            , middle<r r+s<q
            , ∣ r , s , r∈Ux , s∈Uy , middle>l r+s<q ∣₁
            ∣₁)
    isDedekindCut+ x y .IsDedekindCut.disjoint =
      λ q →
        Prop.rec2 Empty.isProp⊥
          (λ (lx , ly , lx∈Lx , ly∈Ly , q<lx+ly)
             (ux , uy , ux∈Ux , uy∈Uy , ux+uy<q) →
            let
              lx<ux : lx < ux
              lx<ux = O.lower<upper x lx ux lx∈Lx ux∈Ux

              ly<uy : ly < uy
              ly<uy = O.lower<upper y ly uy ly∈Ly uy∈Uy

              lx+ly<ux+uy : lx + ly < ux + uy
              lx+ly<ux+uy = +-Pres< lx<ux ly<uy

              q<q : q < q
              q<q =
                <-trans q<lx+ly
                  (<-trans lx+ly<ux+uy ux+uy<q)
            in
            <-arefl q<q refl)
    isDedekindCut+ x y .IsDedekindCut.located =
      located-add
      where
      q-p : K → K → K
      q-p p q = q - p

      0<q-p : (p q : K) → p < q → q-p p q > 0r
      0<q-p p q p<q = <→Diff>0 p<q

      η : K → K → K
      η p q = middle 0r (q-p p q)

      0<η : (p q : K) → p < q → η p q > 0r
      0<η p q p<q = middle>l (0<q-p p q p<q)

      η+η≡q-p : (p q : K) → η p q + η p q ≡ q-p p q
      η+η≡q-p p q = x/2+x/2≡x (q-p p q)

      located-from-close :
        (p q : K) →
        p < q →
        CloseBounds x (η p q) →
        CloseBounds y (η p q) →
        ∥ (p ∈ addLower x y) ⊎ (q ∈ addUpper x y) ∥₁
      located-from-close p q p<q
        (lx , ux , lx∈Lx , ux∈Ux , _ , ux<lx+η)
        (ly , uy , ly∈Ly , uy∈Uy , _ , uy<ly+η)
        with trichotomy p (lx + ly)
      ... | lt p<lx+ly =
        ∣ Sum.inl ∣ lx , ly , lx∈Lx , ly∈Ly , p<lx+ly ∣₁ ∣₁
      ... | eq p≡lx+ly =
        ∣ Sum.inr
            ∣ ux , uy , ux∈Ux , uy∈Uy
            , sum-close-upper<
                lx ly ux uy (η p q) p q
                ux<lx+η
                uy<ly+η
                (≤-refl (sym p≡lx+ly))
                (η+η≡q-p p q)
                p<q
            ∣₁
        ∣₁
      ... | gt lx+ly<p =
        ∣ Sum.inr
            ∣ ux , uy , ux∈Ux , uy∈Uy
            , sum-close-upper<
                lx ly ux uy (η p q) p q
                ux<lx+η
                uy<ly+η
                (<-≤-weaken lx+ly<p)
                (η+η≡q-p p q)
                p<q
            ∣₁
        ∣₁

      located-add :
        (p q : K) →
        p < q →
        ∥ (p ∈ addLower x y) ⊎ (q ∈ addUpper x y) ∥₁
      located-add p q p<q =
        Prop.rec2 squash₁ (located-from-close p q p<q)
          (close-bounds x (η p q) (0<η p q p<q))
          (close-bounds y (η p q) (0<η p q p<q))

    _+𝔻_ : DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ → DedekindCompletion ℓᴾ
    (x +𝔻 y) .lower = addLower x y
    (x +𝔻 y) .upper = addUpper x y
    (x +𝔻 y) .isDedekindCut = isDedekindCut+ x y

    infixl 6 _+𝔻_

    +-comm :
      (x y : DedekindCompletion ℓᴾ) →
      x +𝔻 y ≡ y +𝔻 x
    +-comm x y =
      completionExt (x +𝔻 y) (y +𝔻 x)
        (lower⊆ x y)
        (lower⊆ y x)
        (upper⊆ x y)
        (upper⊆ y x)
      where
      lower⊆ :
        (x y : DedekindCompletion ℓᴾ) →
        addLower x y ⊆ addLower y x
      lower⊆ x y q =
        Prop.rec squash₁
          (λ (r , s , r∈Lx , s∈Ly , q<r+s) →
            ∣ s , r , s∈Ly , r∈Lx
            , subst (λ t → q < t) (+Comm r s) q<r+s
            ∣₁)

      upper⊆ :
        (x y : DedekindCompletion ℓᴾ) →
        addUpper x y ⊆ addUpper y x
      upper⊆ x y q =
        Prop.rec squash₁
          (λ (r , s , r∈Ux , s∈Uy , r+s<q) →
            ∣ s , r , s∈Uy , r∈Ux
            , subst (λ t → t < q) (+Comm r s) r+s<q
            ∣₁)

    +-assoc :
      (x y z : DedekindCompletion ℓᴾ) →
      x +𝔻 (y +𝔻 z) ≡ (x +𝔻 y) +𝔻 z
    +-assoc x y z =
      completionExt (x +𝔻 (y +𝔻 z)) ((x +𝔻 y) +𝔻 z)
        (lower⊆₁ x y z)
        (lower⊆₂ x y z)
        (upper⊆₁ x y z)
        (upper⊆₂ x y z)
      where
      lower⊆₁ :
        (x y z : DedekindCompletion ℓᴾ) →
        addLower x (y +𝔻 z) ⊆ addLower (x +𝔻 y) z
      lower⊆₁ x y z q =
        Prop.rec squash₁
          (λ (r , s , r∈Lx , s∈Ly+z , q<r+s) →
            Prop.rec squash₁
              (λ (t , u , t∈Ly , u∈Lz , s<t+u) →
                let
                  q<r+tu : q < r + (t + u)
                  q<r+tu =
                    <-trans q<r+s (+-lPres< {z = r} s<t+u)

                  q<rt+u : q < (r + t) + u
                  q<rt+u =
                    subst (q <_) (+Assoc r t u) q<r+tu
                in
                Prop.rec squash₁
                  (λ (r' , r<r' , r'∈Lx) →
                    ∣ r + t , u
                    , ∣ r' , t , r'∈Lx , t∈Ly , +-rPres< {z = t} r<r' ∣₁
                    , u∈Lz
                    , q<rt+u
                    ∣₁)
                  (CompletionBase.lower-rounded {𝒦 = 𝒦} x r r∈Lx))
              s∈Ly+z)

      lower⊆₂ :
        (x y z : DedekindCompletion ℓᴾ) →
        addLower (x +𝔻 y) z ⊆ addLower x (y +𝔻 z)
      lower⊆₂ x y z q =
        Prop.rec squash₁
          (λ (a , u , a∈Lx+y , u∈Lz , q<a+u) →
            Prop.rec squash₁
              (λ (r , t , r∈Lx , t∈Ly , a<r+t) →
                let
                  a+u<rt+u : a + u < (r + t) + u
                  a+u<rt+u = +-rPres< {z = u} a<r+t

                  q<rt+u : q < (r + t) + u
                  q<rt+u = <-trans q<a+u a+u<rt+u

                  q<r+tu : q < r + (t + u)
                  q<r+tu =
                    subst (q <_) (sym (+Assoc r t u)) q<rt+u
                in
                Prop.rec squash₁
                  (λ (t' , t<t' , t'∈Ly) →
                    ∣ r , t + u
                    , r∈Lx
                    , ∣ t' , u , t'∈Ly , u∈Lz , +-rPres< {z = u} t<t' ∣₁
                    , q<r+tu
                    ∣₁)
                  (CompletionBase.lower-rounded {𝒦 = 𝒦} y t t∈Ly))
              a∈Lx+y)

      upper⊆₁ :
        (x y z : DedekindCompletion ℓᴾ) →
        addUpper x (y +𝔻 z) ⊆ addUpper (x +𝔻 y) z
      upper⊆₁ x y z q =
        Prop.rec squash₁
          (λ (r , s , r∈Ux , s∈Uy+z , r+s<q) →
            Prop.rec squash₁
              (λ (t , u , t∈Uy , u∈Uz , t+u<s) →
                let
                  r+tu<r+s : r + (t + u) < r + s
                  r+tu<r+s =
                    +-lPres< {z = r} t+u<s

                  rt+u<r+s : (r + t) + u < r + s
                  rt+u<r+s =
                    subst (_< r + s) (+Assoc r t u) r+tu<r+s

                  rt+u<q : (r + t) + u < q
                  rt+u<q = <-trans rt+u<r+s r+s<q
                in
                Prop.rec squash₁
                  (λ (r' , r'<r , r'∈Ux) →
                    ∣ r + t , u
                    , ∣ r' , t , r'∈Ux , t∈Uy , +-rPres< {z = t} r'<r ∣₁
                    , u∈Uz
                    , rt+u<q
                    ∣₁)
                  (CompletionBase.upper-rounded {𝒦 = 𝒦} x r r∈Ux))
              s∈Uy+z)

      upper⊆₂ :
        (x y z : DedekindCompletion ℓᴾ) →
        addUpper (x +𝔻 y) z ⊆ addUpper x (y +𝔻 z)
      upper⊆₂ x y z q =
        Prop.rec squash₁
          (λ (a , u , a∈Ux+y , u∈Uz , a+u<q) →
            Prop.rec squash₁
              (λ (r , t , r∈Ux , t∈Uy , r+t<a) →
                let
                  rt+u<a+u : (r + t) + u < a + u
                  rt+u<a+u = +-rPres< {z = u} r+t<a

                  rt+u<q : (r + t) + u < q
                  rt+u<q = <-trans rt+u<a+u a+u<q

                  r+tu<q : r + (t + u) < q
                  r+tu<q =
                    subst (_< q) (sym (+Assoc r t u)) rt+u<q
                in
                Prop.rec squash₁
                  (λ (u' , u'<u , u'∈Uz) →
                    ∣ r , t + u
                    , r∈Ux
                    , ∣ t , u' , t∈Uy , u'∈Uz , +-lPres< {z = t} u'<u ∣₁
                    , r+tu<q
                    ∣₁)
                  (CompletionBase.upper-rounded {𝒦 = 𝒦} z u u∈Uz))
              a∈Ux+y)

    +-idR :
      (x : DedekindCompletion ℓᴾ) →
      x +𝔻 0𝔻 ≡ x
    +-idR x =
      completionExt (x +𝔻 0𝔻) x
        lower⊆
        lower⊇
        upper⊆
        upper⊇
      where
      lower⊆ : addLower x 0𝔻 ⊆ lower x
      lower⊆ q =
        Prop.rec (isProp∈ (lower x) q)
          (λ (r , s , r∈Lx , s<0 , q<r+s) →
            CompletionBase.lower-closed {𝒦 = 𝒦} x q r
              (<-trans q<r+s (+-rNeg→< (Lift.lower s<0)))
              r∈Lx)

      lower⊇ : lower x ⊆ addLower x 0𝔻
      lower⊇ q q∈Lx =
        Prop.rec squash₁
          (λ (r , q<r , r∈Lx) →
            let
              q-r<0 : q - r < 0r
              q-r<0 = <→Diff<0 q<r

              s : K
              s = middle (q - r) 0r

              q-r<s : q - r < s
              q-r<s = middle>l q-r<0

              s<0 : s < 0r
              s<0 = middle<r q-r<0

              q<r+s : q < r + s
              q<r+s =
                subst (q <_) (+Comm s r) (-MoveLToR< q-r<s)
            in
            ∣ r , s , r∈Lx , lift s<0 , q<r+s ∣₁)
          (CompletionBase.lower-rounded {𝒦 = 𝒦} x q q∈Lx)

      upper⊆ : addUpper x 0𝔻 ⊆ upper x
      upper⊆ q =
        Prop.rec (isProp∈ (upper x) q)
          (λ (r , s , r∈Ux , 0<s , r+s<q) →
            CompletionBase.upper-closed {𝒦 = 𝒦} x r q
              (<-trans (+-rPos→> (Lift.lower 0<s)) r+s<q)
              r∈Ux)

      upper⊇ : upper x ⊆ addUpper x 0𝔻
      upper⊇ q q∈Ux =
        Prop.rec squash₁
          (λ (r , r<q , r∈Ux) →
            let
              0<q-r : q - r > 0r
              0<q-r = <→Diff>0 r<q

              s : K
              s = middle 0r (q - r)

              0<s : s > 0r
              0<s = middle>l 0<q-r

              s<q-r : s < q - r
              s<q-r = middle<r 0<q-r

              r+s<q : r + s < q
              r+s<q = -MoveRToL<' s<q-r
            in
            ∣ r , s , r∈Ux , lift 0<s , r+s<q ∣₁)
          (CompletionBase.upper-rounded {𝒦 = 𝒦} x q q∈Ux)

    +-idL :
      (x : DedekindCompletion ℓᴾ) →
      0𝔻 +𝔻 x ≡ x
    +-idL x = +-comm 0𝔻 x ∙ +-idR x
