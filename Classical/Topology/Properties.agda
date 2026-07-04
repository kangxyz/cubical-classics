{-

This file contains:
- The notion of closed subset;
- Basics of open covering;
- Basics of compactness.

-}
{-# OPTIONS --safe #-}
module Classical.Topology.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.PropositionalTruncation.Monad

open import Classical.Axioms

open import Classical.Foundations.Powerset
open import Classical.Topology.Base

private
  variable
    ℓ : Level


module _ ⦃ 🤖 : Oracle ⦄ where

  open Topology


  module _ {X : Type ℓ} ⦃ 𝒯 : Topology X ⦄ where

    {-

      The Open and Closed Subset

    -}

    Open : ℙ ℙ X
    Open = 𝒯 .openset

    Closed : ℙ ℙ X
    Closed A = Open (∁ A)

    isOpenSub : ℙ X → Type _
    isOpenSub U = U ∈ Open

    isClosedSub : ℙ X → Type _
    isClosedSub A = ∁ A ∈ Open

    isOpenSub∁ : {A : ℙ X} → isClosedSub A → isOpenSub (∁ A)
    isOpenSub∁ p = p

    isClosedSub∁ : {A : ℙ X} → isOpenSub A → isClosedSub (∁ A)
    isClosedSub∁ = subst (_∈ Open) (sym (∁-Unip _))


    {-

      Open Covering

    -}

    -- We say `𝒰 covers K` if the members of 𝒰 are all open, and their union contains K.

    _covers_ : ℙ ℙ X → ℙ X → Type _
    _covers_ 𝒰 A = A ⊆ union 𝒰 × 𝒰 ⊆ Open

    union∈Open : {𝒰 : ℙ ℙ X} → 𝒰 ⊆ Open → union 𝒰 ∈ Open
    union∈Open = 𝒯 .∪-close

    ∈cover : {x : X}{A : ℙ X}{𝒰 : ℙ ℙ X} → x ∈ A → 𝒰 covers A → ∥ Σ[ U ∈ ℙ X ] x ∈ U × U ∈ 𝒰 ∥₁
    ∈cover x∈A 𝒰covA = ∈union→∃ (𝒰covA .fst x∈A)


    {-

      Compactness

    -}

    -- A subset K is compact
    -- if every open cover 𝒰 of K merely has a finite subcover.

    isCompactSub : ℙ X → Type _
    isCompactSub K =
      {𝒰 : ℙ ℙ X} → 𝒰 covers K → ∥ Σ[ 𝒰₀ ∈ ℙ ℙ X ] 𝒰₀ ⊆ 𝒰 × isFinSub 𝒰₀ × 𝒰₀ covers K ∥₁

    isCompact : Type _
    isCompact = isCompactSub total

    isPropIsCompactSub : {A : ℙ X} → isProp (isCompactSub A)
    isPropIsCompactSub = isPropImplicitΠ (λ _ → isPropΠ (λ _ → squash₁))


    -- A closed subset contained in a compact subset is itself compact.

    isClosedInCompact→isCompact :
      {A K : ℙ X} → A ⊆ K → isClosedSub A → isCompactSub K → isCompactSub A
    isClosedInCompact→isCompact {A = A} {K = K} A⊆K ∁A∈Open takefinK {𝒰 = 𝒰} 𝒰covA = ∃𝒰₀
      where

      𝒰+∁A : ℙ ℙ X
      𝒰+∁A = 𝒰 ∪ [ ∁ A ]

      𝒰+∁A-covK : 𝒰+∁A covers K
      𝒰+∁A-covK .fst {x = x} x∈K = case-split (∈A+∈∁A A)
        where
        case-split : (x ∈ A) ⊎ (x ∈ ∁ A) → _
        case-split (inl x∈A) = ∈union∪[A] (inl (𝒰covA .fst x∈A))
        case-split (inr x∈∁A) = ∈union∪[A] (inr x∈∁A)
      𝒰+∁A-covK .snd = ⊆→⊆∪ {C = Open} (𝒰covA .snd) (A∈S→[A]⊆S {S = Open} ∁A∈Open)

      a∈U+U∈𝒰+∁A→U∈𝒰 : {x : X}{U : ℙ X} → x ∈ A → x ∈ U → U ∈ 𝒰+∁A → U ∈ 𝒰
      a∈U+U∈𝒰+∁A→U∈𝒰 {x = x} {U = U} x∈A x∈U U∈𝒰+∁A = case-split (∈A∪B→∈A+∈B 𝒰 [ ∁ A ] U∈𝒰+∁A)
        where
        case-split : (U ∈ 𝒰) ⊎ (U ∈ [ ∁ A ]) → U ∈ 𝒰
        case-split (inl U∈𝒰) = U∈𝒰
        case-split (inr U∈[∁A]) = Empty.rec (∈∁→¬∈ {A = A} x∈∁A x∈A)
          where
          x∈∁A : x ∈ ∁ A
          x∈∁A = proof _ , isProp∈ (∁ A) by do
            ∁A≡U ← y∈[x]→∥x≡y∥ U∈[∁A]
            return (subst (x ∈_) (sym ∁A≡U) x∈U)

      module _ (𝒰' : ℙ ℙ X)(𝒰'⊆𝒰+∁A : 𝒰' ⊆ 𝒰+∁A)(fin𝒰' : isFinSub 𝒰')(𝒰'covK : 𝒰' covers K) where

        cov-prop : ℙ X → hProp _
        cov-prop U = ∥ Σ[ x ∈ X ] (x ∈ A) × (x ∈ U) × (U ∈ 𝒰') ∥₁ , squash₁

        𝒰₀ = specify cov-prop

        𝒰₀⊆𝒰' : 𝒰₀ ⊆ 𝒰'
        𝒰₀⊆𝒰' U∈𝒰₀ =
          proof _ , isProp∈ 𝒰' by do
          (x , x∈A , x∈U , U∈𝒰') ← ∈→Inhab cov-prop U∈𝒰₀
          return U∈𝒰'

        𝒰₀⊆𝒰 : 𝒰₀ ⊆ 𝒰
        𝒰₀⊆𝒰 U∈𝒰₀ =
          proof _ , isProp∈ 𝒰 by do
          (x , x∈A , x∈U , U∈𝒰') ← ∈→Inhab cov-prop U∈𝒰₀
          return (a∈U+U∈𝒰+∁A→U∈𝒰 x∈A x∈U (𝒰'⊆𝒰+∁A U∈𝒰'))

        fin𝒰₀ : isFinSub 𝒰₀
        fin𝒰₀ = isFinSub⊆ 𝒰₀⊆𝒰' fin𝒰'

        𝒰₀covA : 𝒰₀ covers A
        𝒰₀covA .fst {x = x} x∈A = ∃→∈union ∃U
          where
          ∃U : ∥ Σ[ U ∈ ℙ X ] (x ∈ U) × (U ∈ 𝒰₀) ∥₁
          ∃U = do
            (U , x∈U , U∈𝒰') ← ∈union→∃ (𝒰'covK .fst (A⊆K x∈A))
            return (U , x∈U , Inhab→∈ cov-prop ∣ x , x∈A , x∈U , U∈𝒰' ∣₁)

        𝒰₀covA .snd U∈𝒰₀ = 𝒰covA .snd (𝒰₀⊆𝒰 U∈𝒰₀)

        Σ𝒰₀ : Σ[ 𝒰₀ ∈ ℙ ℙ X ] 𝒰₀ ⊆ 𝒰 × isFinSub 𝒰₀ × 𝒰₀ covers A
        Σ𝒰₀ = 𝒰₀ , 𝒰₀⊆𝒰 , fin𝒰₀ , 𝒰₀covA

      ∃𝒰₀ : ∥ Σ[ 𝒰₀ ∈ ℙ ℙ X ] 𝒰₀ ⊆ 𝒰 × isFinSub 𝒰₀ × 𝒰₀ covers A ∥₁
      ∃𝒰₀ = do
        (𝒰' , 𝒰'⊆𝒰+∁A , fin𝒰' , 𝒰'covK) ← takefinK 𝒰+∁A-covK
        return (Σ𝒰₀ 𝒰' 𝒰'⊆𝒰+∁A fin𝒰' 𝒰'covK)
