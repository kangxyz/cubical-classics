{-

Infinitary Operations

-}
{-# OPTIONS --safe #-}
module Classical.Foundations.Powerset.BigOps where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Nullary

open import Classical.Axioms
open import Classical.Preliminary.Logic
open import Classical.Foundations.Powerset.Base
open import Classical.Foundations.Powerset.Membership
open import Classical.Foundations.Powerset.Boolean
open import Classical.Foundations.Powerset.Properties

private
  variable
    ℓ : Level
    X : Type ℓ


module _ ⦃ 🤖 : Oracle ⦄ where


  {-

    Arbitrary Union

  -}

  -- Union of arbitrary collection of subsets

  union : ℙ (ℙ X) → ℙ X
  union {X = X} S = specify λ x → ∥ Σ[ A ∈ ℙ X ] (x ∈ A) × (A ∈ S) ∥₁ , squash₁


  module _
    {S : ℙ (ℙ X)}{x : X} where

    ∈union→∃ : x ∈ union S → ∥ Σ[ A ∈ ℙ X ] (x ∈ A) × (A ∈ S) ∥₁
    ∈union→∃ = ∈→Inhab (λ x → ∥ Σ[ A ∈ ℙ X ] (x ∈ A) × (A ∈ S) ∥₁ , squash₁)

    ∃→∈union : ∥ Σ[ A ∈ ℙ X ] (x ∈ A) × (A ∈ S) ∥₁ → x ∈ union S
    ∃→∈union = Inhab→∈ λ x → ∥ Σ[ A ∈ ℙ X ] (x ∈ A) × (A ∈ S) ∥₁ , squash₁

    ∉union : ((A : ℙ X) → A ∈ S → x ∉ A) → x ∉ union S
    ∉union p = ¬∈→∉ {A = union S} (¬map ∈union→∃ helper)
      where
      helper : ¬ ∥ Σ[ A ∈ ℙ X ] (x ∈ A) × (A ∈ S) ∥₁
      helper = Prop.rec isProp⊥ (λ (A , x∈A , A∈S) → explode∈ {A = A} x∈A (p _ A∈S))


  ⊆union : {S : ℙ (ℙ X)}{A B : ℙ X} → A ⊆ B → B ∈ S → A ⊆ union S
  ⊆union A⊆B B∈S x∈A = ∃→∈union ∣ _  , A⊆B x∈A , B∈S ∣₁


  union∅ : union {X = X} ∅ ≡ ∅
  union∅ = A≡∅ (λ U → ∉union (helper U))
    where
    helper : (x : X) → (A : ℙ X) → A ∈ ∅ → x ∉ A
    helper _ A A∈∅ = explode∈ {x = A} A∈∅ (x∉∅ {x = A})

  union⊆ : {S : ℙ (ℙ X)}{A : ℙ X} → ((U : ℙ X) → U ∈ S → U ⊆ A) → union S ⊆ A
  union⊆ {X = X} {S = S} {A = A} U∈S→U⊆A {x = x} x∈∪S = helper (∈union→∃ x∈∪S)
    where
    helper : ∥ Σ[ N ∈ ℙ X ] (x ∈ N) × (N ∈ S) ∥₁ → x ∈ A
    helper = Prop.rec (isProp∈ A) (λ (_ , x∈N , N∈S) → ∈⊆-trans {B = A} x∈N (U∈S→U⊆A _ N∈S))

  union∪ : {S T : ℙ (ℙ X)} → union (S ∪ T) ≡ union S ∪ union T
  union∪ {S = S} {T = T} = bi⊆→≡ ∪-S∪T⊆∪S-∪-∪T ∪S-∪-∪T⊆∪-S∪T
    where
    ∪-S∪T⊆∪S-∪-∪T : union (S ∪ T) ⊆ union S ∪ union T
    ∪-S∪T⊆∪S-∪-∪T x∈∪-S∪T = ∈A+∈B→∈A∪B (union S) (union T) do
      (A , x∈A , A∈S∪T) ← ∈union→∃ x∈∪-S∪T
      return (
        case ∈A∪B→∈A+∈B S T A∈S∪T of λ
        { (inl A∈S) → inl (∃→∈union ∣ A , x∈A , A∈S ∣₁)
        ; (inr A∈T) → inr (∃→∈union ∣ A , x∈A , A∈T ∣₁) })

    ∪S-∪-∪T⊆∪-S∪T : union S ∪ union T ⊆ union (S ∪ T)
    ∪S-∪-∪T⊆∪-S∪T x∈∪S-∪-∪T = ∃→∈union
      (case ∈A∪B→∈A+∈B (union S) (union T) x∈∪S-∪-∪T of λ
        { (inl x∈S) → do (A , x∈A , x∈S) ← ∈union→∃ x∈S ; return (A , x∈A , ∪-left∈  S T x∈S)
        ; (inr x∈T) → do (A , x∈A , x∈T) ← ∈union→∃ x∈T ; return (A , x∈A , ∪-right∈ S T x∈T) })


  union∪-left⊆ : {S T : ℙ (ℙ X)} → union S ⊆ union (S ∪ T)
  union∪-left⊆ {S = S} {T = T} x∈∪S = ∃→∈union do
    (A , x∈A , A∈S) ← ∈union→∃ x∈∪S
    return (A , x∈A , ∪-left∈ S T A∈S)

  union∪-right⊆ : {S T : ℙ (ℙ X)} → union T ⊆ union (S ∪ T)
  union∪-right⊆ {S = S} {T = T} x∈∪T = ∃→∈union do
    (A , x∈A , A∈T) ← ∈union→∃ x∈∪T
    return (A , x∈A , ∪-right∈ S T A∈T)


  union[A]⊆A : {A : ℙ X} → union [ A ] ⊆ A
  union[A]⊆A {A = A} {x = x} x∈∪[A] =
    proof _ , isProp∈ A by do
    (B , x∈B , B∈[A]) ← ∈union→∃ x∈∪[A]
    A≡B ← y∈[x]→∥x≡y∥ B∈[A]
    return (subst (x ∈_) (sym A≡B) x∈B)

  A⊆union[A] : {A : ℙ X} → A ⊆ union [ A ]
  A⊆union[A] {A = A} x∈A = ∃→∈union ∣ A , x∈A , x∈[x] ∣₁

  union[A] : {A : ℙ X} → union [ A ] ≡ A
  union[A] = bi⊆→≡ union[A]⊆A A⊆union[A]

  ∈union∪[A] : {S : ℙ (ℙ X)}{A : ℙ X}{x : X}
    → (x ∈ union S) ⊎ (x ∈ A) → x ∈ union (S ∪ [ A ])
  ∈union∪[A] (inl x∈∪S) = union∪-left⊆ x∈∪S
  ∈union∪[A] (inr x∈A) = union∪-right⊆ (A⊆union[A] x∈A)

  union∪[A] : {S : ℙ (ℙ X)}{A : ℙ X} → union (S ∪ [ A ]) ≡ (union S) ∪ A
  union∪[A] {S = S} {A = A} = union∪ ∙ (λ i → (union S) ∪ union[A] {A = A} i)
