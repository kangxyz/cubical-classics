{-

Archimedean approximation for Dedekind completions

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.DedekindCompletion.Approximation where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.HITs.PropositionalTruncation as Prop
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Algebra.LinearlyOrderedCommRing
open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedean
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.Algebra.LinearlyOrderedField.Archimedean
open import Constructive.DedekindCompletion.Base
open import Constructive.DedekindCompletion.Order
open import Constructive.Foundations.Powerset hiding (Pred)

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


module CompletionApproximation
  (𝒜 : ArchimedeanLinearlyOrderedField ℓ ℓ') {ℓᴾ : Level} where

  𝒦 : LinearlyOrderedField ℓ ℓ'
  𝒦 = 𝒜 .fst

  archimedean : isArchimedean (𝒦 .fst)
  archimedean = 𝒜 .snd

  private
    K : Type ℓ
    K = 𝒦 .fst .fst .fst

    module O = CompletionOrder 𝒦

  open CompletionBase 𝒦
  open LinearlyOrderedFieldStr 𝒦
  open Helpers (LinearlyOrderedCommRing→CommRing (𝒦 .fst))

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
      n = fst (archimedean (u - p) δ δ>0)

      u-p<nδ : u - p < n ⋆ δ
      u-p<nδ = snd (archimedean (u - p) δ δ>0)

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
