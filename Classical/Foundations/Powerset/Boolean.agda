{-

Boolean Algebraic Operations

This part doesn't need impredicativity actually.

-}
{-# OPTIONS --safe #-}
module Classical.Foundations.Powerset.Boolean where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation as Prop

open import Classical.Axioms
open import Classical.Foundations.Powerset.Base
open import Classical.Foundations.Powerset.Membership
open import Solvers.Bool
  using (v0; v1; v2; v3; trueᵇ; falseᵇ; ¬ᵇ_; _∧ᵇ_; _∨ᵇ_;
         _≡ᵖ_; _≡ᵖtrue; _≡ᵖfalse; _∨ᵖ_; _→ᵖ_;
         solveᵖ₁; solveᵖ₂; solveᵖ₃; solveᵖ₄)
open import Solvers.Powerset
  using (p0; p1; p2; p3; ∅ᵖ; totalᵖ; ∁ᵖ_; _∪ᵖ_; _∩ᵖ_;
         solveℙ₁; solveℙ₂; solveℙ₃; solveℙ₄)

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ


module _ ⦃ 🤖 : Oracle ⦄ where


  {-

    Empty and Total Subset

  -}

  x∉∅ : {x : X} → x ∉ ∅
  x∉∅ = refl

  x∈total : {x : X} → x ∈ total
  x∈total = refl

  ∅⊆A : {A : ℙ X} → ∅ ⊆ A
  ∅⊆A x∈∅ = Empty.rec (false≢true x∈∅)

  A⊆total : {A : ℙ X} → A ⊆ total
  A⊆total _ = refl

  A⊆∅ : {A : ℙ X} → ((x : X) → x ∉ A) → A ⊆ ∅
  A⊆∅ p x∈A = Empty.rec (true≢false (sym x∈A ∙ p _))

  total⊆A : {A : ℙ X} → ((x : X) → x ∈ A) → total ⊆ A
  total⊆A p _ = p _

  A⊆∅→A≡∅ : {A : ℙ X} → A ⊆ ∅ → A ≡ ∅
  A⊆∅→A≡∅ {A = A} A⊆∅ = bi⊆→≡ A⊆∅ (∅⊆A {A = A})

  A≡∅ : {A : ℙ X} → ((x : X) → x ∉ A) → A ≡ ∅
  A≡∅ {A = A} p = A⊆∅→A≡∅ (A⊆∅ p)

  A≡total : {A : ℙ X} → ((x : X) → x ∈ A) → A ≡ total
  A≡total {A = A} p = bi⊆→≡ (A⊆total {A = A}) (total⊆A p)

  ¬x∈∅ : (x : X) → x ∈ ∅ → ⊥
  ¬x∈∅ x x∈∅ = false≢true x∈∅


  {-

    Complement

  -}

  ∁-Unip : (A : ℙ X) → ∁ ∁ A ≡ A
  ∁-Unip = solveℙ₁ (∁ᵖ (∁ᵖ p0)) p0

  ∉→∈∁ : {x : X}{A : ℙ X} → x ∉ A → x ∈ (∁ A)
  ∉→∈∁ {x = x} {A = A} =
    solveᵖ₁ ((v0 ≡ᵖfalse) →ᵖ ((¬ᵇ v0) ≡ᵖtrue)) (A x)

  ∈∁→∉ : {x : X}{A : ℙ X} → x ∈ (∁ A) → x ∉ A
  ∈∁→∉ {x = x} {A = A} =
    solveᵖ₁ (((¬ᵇ v0) ≡ᵖtrue) →ᵖ (v0 ≡ᵖfalse)) (A x)

  ∈A+∈∁A : {x : X}(A : ℙ X) → (x ∈ A) ⊎ (x ∈ ∁ A)
  ∈A+∈∁A {x = x} A =
    solveᵖ₁ ((v0 ≡ᵖtrue) ∨ᵖ ((¬ᵇ v0) ≡ᵖtrue)) (A x)


  {-

    Binary Union

  -}

  ∪-lZero : (A : ℙ X) → total ∪ A ≡ total
  ∪-lZero = solveℙ₁ (totalᵖ ∪ᵖ p0) totalᵖ

  ∪-rZero : (A : ℙ X) → A ∪ total ≡ total
  ∪-rZero = solveℙ₁ (p0 ∪ᵖ totalᵖ) totalᵖ

  ∪-lUnit : (A : ℙ X) → ∅ ∪ A ≡ A
  ∪-lUnit = solveℙ₁ (∅ᵖ ∪ᵖ p0) p0

  ∪-rUnit : (A : ℙ X) → A ∪ ∅ ≡ A
  ∪-rUnit = solveℙ₁ (p0 ∪ᵖ ∅ᵖ) p0

  ∪-Comm : (A B : ℙ X) → A ∪ B ≡ B ∪ A
  ∪-Comm = solveℙ₂ (p0 ∪ᵖ p1) (p1 ∪ᵖ p0)

  ∪-Assoc : (A B C : ℙ X) → A ∪ (B ∪ C) ≡ (A ∪ B) ∪ C
  ∪-Assoc = solveℙ₃ (p0 ∪ᵖ (p1 ∪ᵖ p2)) ((p0 ∪ᵖ p1) ∪ᵖ p2)

  ∪-Idem : (A : ℙ X) → A ∪ A ≡ A
  ∪-Idem = solveℙ₁ (p0 ∪ᵖ p0) p0

  ∪-left∈ : {x : X}(A B : ℙ X) → x ∈ A → x ∈ (A ∪ B)
  ∪-left∈ {x = x} A B =
    solveᵖ₂ ((v0 ≡ᵖtrue) →ᵖ ((v0 ∨ᵇ v1) ≡ᵖtrue)) (A x) (B x)

  ∪-right∈ : {x : X}(A B : ℙ X) → x ∈ B → x ∈ (A ∪ B)
  ∪-right∈ {x = x} A B =
    solveᵖ₂ ((v1 ≡ᵖtrue) →ᵖ ((v0 ∨ᵇ v1) ≡ᵖtrue)) (A x) (B x)

  ∪-left⊆ : (A B : ℙ X) → A ⊆ (A ∪ B)
  ∪-left⊆ A B = ∪-left∈ A B

  ∪-right⊆ : (A B : ℙ X) → B ⊆ (A ∪ B)
  ∪-right⊆ A B = ∪-right∈ A B

  ∈A∪B→∈A+∈B : {x : X}(A B : ℙ X) → x ∈ (A ∪ B) → (x ∈ A) ⊎ (x ∈ B)
  ∈A∪B→∈A+∈B {x = x} A B =
    solveᵖ₂ (((v0 ∨ᵇ v1) ≡ᵖtrue) →ᵖ ((v0 ≡ᵖtrue) ∨ᵖ (v1 ≡ᵖtrue))) (A x) (B x)

  ∈A+∈B→∈A∪B : {x : X}(A B : ℙ X) → ∥ (x ∈ A) ⊎ (x ∈ B) ∥₁ → x ∈ (A ∪ B)
  ∈A+∈B→∈A∪B {x = x} A B =
    Prop.rec (isProp∈ (A ∪ B))
      (solveᵖ₂ (((v0 ≡ᵖtrue) ∨ᵖ (v1 ≡ᵖtrue)) →ᵖ ((v0 ∨ᵇ v1) ≡ᵖtrue)) (A x) (B x))

  ⊆→⊆∪ : {A B C : ℙ X} → A ⊆ C → B ⊆ C → A ∪ B ⊆ C
  ⊆→⊆∪ {A = A} {B = B} {C = C} A⊆C B⊆C {x = x} =
    solveᵖ₃
      (((v0 ≡ᵖtrue) →ᵖ (v2 ≡ᵖtrue)) →ᵖ
       ((v1 ≡ᵖtrue) →ᵖ (v2 ≡ᵖtrue)) →ᵖ
       (((v0 ∨ᵇ v1) ≡ᵖtrue) →ᵖ (v2 ≡ᵖtrue)))
      (A x) (B x) (C x) A⊆C B⊆C


  {-

    Binary Intersection

  -}

  ∩-lZero : (A : ℙ X) → ∅ ∩ A ≡ ∅
  ∩-lZero = solveℙ₁ (∅ᵖ ∩ᵖ p0) ∅ᵖ

  ∩-rZero : (A : ℙ X) → A ∩ ∅ ≡ ∅
  ∩-rZero = solveℙ₁ (p0 ∩ᵖ ∅ᵖ) ∅ᵖ

  ∩-lUnit : (A : ℙ X) → total ∩ A ≡ A
  ∩-lUnit = solveℙ₁ (totalᵖ ∩ᵖ p0) p0

  ∩-rUnit : (A : ℙ X) → A ∩ total ≡ A
  ∩-rUnit = solveℙ₁ (p0 ∩ᵖ totalᵖ) p0

  ∩-Comm : (A B : ℙ X) → A ∩ B ≡ B ∩ A
  ∩-Comm = solveℙ₂ (p0 ∩ᵖ p1) (p1 ∩ᵖ p0)

  ∩-Assoc : (A B C : ℙ X) → A ∩ (B ∩ C) ≡ (A ∩ B) ∩ C
  ∩-Assoc = solveℙ₃ (p0 ∩ᵖ (p1 ∩ᵖ p2)) ((p0 ∩ᵖ p1) ∩ᵖ p2)

  ∩-Idem : (A : ℙ X) → A ∩ A ≡ A
  ∩-Idem = solveℙ₁ (p0 ∩ᵖ p0) p0

  ∈→∈∩ : {x : X}(A B : ℙ X) → x ∈ A → x ∈ B → x ∈ (A ∩ B)
  ∈→∈∩ {x = x} A B =
    solveᵖ₂ ((v0 ≡ᵖtrue) →ᵖ (v1 ≡ᵖtrue) →ᵖ ((v0 ∧ᵇ v1) ≡ᵖtrue)) (A x) (B x)

  ⊆→⊆∩ : {C : ℙ X}(A B : ℙ X) → C ⊆ A → C ⊆ B → C ⊆ (A ∩ B)
  ⊆→⊆∩ {C = C} A B C⊆A C⊆B {x = x} =
    solveᵖ₃
      (((v0 ≡ᵖtrue) →ᵖ (v1 ≡ᵖtrue)) →ᵖ
       ((v0 ≡ᵖtrue) →ᵖ (v2 ≡ᵖtrue)) →ᵖ
       ((v0 ≡ᵖtrue) →ᵖ ((v1 ∧ᵇ v2) ≡ᵖtrue)))
      (C x) (A x) (B x) C⊆A C⊆B

  left∈-∩ : {x : X}(A B : ℙ X) → x ∈ (A ∩ B) → x ∈ A
  left∈-∩ {x = x} A B =
    solveᵖ₂ (((v0 ∧ᵇ v1) ≡ᵖtrue) →ᵖ (v0 ≡ᵖtrue)) (A x) (B x)

  right∈-∩ : {x : X}(A B : ℙ X) → x ∈ (A ∩ B) → x ∈ B
  right∈-∩ {x = x} A B =
    solveᵖ₂ (((v0 ∧ᵇ v1) ≡ᵖtrue) →ᵖ (v1 ≡ᵖtrue)) (A x) (B x)

  ⊆→∩⊆ : (A B C : ℙ X) → A ⊆ B → (A ∩ C) ⊆ (B ∩ C)
  ⊆→∩⊆ A B C A⊆B {x = x} =
    solveᵖ₃
      (((v0 ≡ᵖtrue) →ᵖ (v1 ≡ᵖtrue)) →ᵖ
       (((v0 ∧ᵇ v2) ≡ᵖtrue) →ᵖ ((v1 ∧ᵇ v2) ≡ᵖtrue)))
      (A x) (B x) (C x) A⊆B

  A⊆B+B∩C≡∅→A∩C≡∅ : {A B C : ℙ X} → A ⊆ B → B ∩ C ≡ ∅ → A ∩ C ≡ ∅
  A⊆B+B∩C≡∅→A∩C≡∅ {A = A} {B = B} {C = C} A⊆B B∩C≡∅ i x =
    solveᵖ₃
      (((v0 ≡ᵖtrue) →ᵖ (v1 ≡ᵖtrue)) →ᵖ
       ((v1 ∧ᵇ v2) ≡ᵖfalse) →ᵖ
       ((v0 ∧ᵇ v2) ≡ᵖfalse))
      (A x) (B x) (C x) A⊆B (λ j → B∩C≡∅ j x) i

  A⊆B→A∩B≡A : {A B : ℙ X} → A ⊆ B → A ∩ B ≡ A
  A⊆B→A∩B≡A {A = A} {B = B} A⊆B i x =
    solveᵖ₂
      (((v0 ≡ᵖtrue) →ᵖ (v1 ≡ᵖtrue)) →ᵖ ((v0 ∧ᵇ v1) ≡ᵖ v0))
      (A x) (B x) A⊆B i


  {-

    Algebraic Laws of Boolean Algebra

  -}

  -- Absorption laws

  ∪-∩-Absorp : (A B : ℙ X) → A ∪ (A ∩ B) ≡ A
  ∪-∩-Absorp = solveℙ₂ (p0 ∪ᵖ (p0 ∩ᵖ p1)) p0

  ∩-∪-Absorp : (A B : ℙ X) → A ∩ (A ∪ B) ≡ A
  ∩-∪-Absorp = solveℙ₂ (p0 ∩ᵖ (p0 ∪ᵖ p1)) p0


  -- Distribution laws

  ∪-∩-rDist : (A B C : ℙ X) → A ∪ (B ∩ C) ≡ (A ∪ B) ∩ (A ∪ C)
  ∪-∩-rDist = solveℙ₃ (p0 ∪ᵖ (p1 ∩ᵖ p2)) ((p0 ∪ᵖ p1) ∩ᵖ (p0 ∪ᵖ p2))

  ∩-∪-rDist : (A B C : ℙ X) → A ∩ (B ∪ C) ≡ (A ∩ B) ∪ (A ∩ C)
  ∩-∪-rDist = solveℙ₃ (p0 ∩ᵖ (p1 ∪ᵖ p2)) ((p0 ∩ᵖ p1) ∪ᵖ (p0 ∩ᵖ p2))

  ∪-∩-lDist : (A B C : ℙ X) → (A ∩ B) ∪ C ≡ (A ∪ C) ∩ (B ∪ C)
  ∪-∩-lDist = solveℙ₃ ((p0 ∩ᵖ p1) ∪ᵖ p2) ((p0 ∪ᵖ p2) ∩ᵖ (p1 ∪ᵖ p2))

  ∩-∪-lDist : (A B C : ℙ X) → (A ∪ B) ∩ C ≡ (A ∩ C) ∪ (B ∩ C)
  ∩-∪-lDist = solveℙ₃ ((p0 ∪ᵖ p1) ∩ᵖ p2) ((p0 ∩ᵖ p2) ∪ᵖ (p1 ∩ᵖ p2))


  -- Complementation laws

  ∪-Compt : (A : ℙ X) → A ∪ (∁ A) ≡ total
  ∪-Compt = solveℙ₁ (p0 ∪ᵖ ∁ᵖ p0) totalᵖ

  ∩-Compt : (A : ℙ X) → A ∩ (∁ A) ≡ ∅
  ∩-Compt = solveℙ₁ (p0 ∩ᵖ ∁ᵖ p0) ∅ᵖ


  -- de Morgan laws

  ∪-∩-deMorgan : (A B : ℙ X) → (∁ A) ∪ (∁ B) ≡ ∁ (A ∩ B)
  ∪-∩-deMorgan = solveℙ₂ ((∁ᵖ p0) ∪ᵖ (∁ᵖ p1)) (∁ᵖ (p0 ∩ᵖ p1))

  ∩-∪-deMorgan : (A B : ℙ X) → (∁ A) ∩ (∁ B) ≡ ∁ (A ∪ B)
  ∩-∪-deMorgan = solveℙ₂ ((∁ᵖ p0) ∩ᵖ (∁ᵖ p1)) (∁ᵖ (p0 ∪ᵖ p1))


  {-

    Facts relating non-intersecting subsets and complementary subsets

  -}

  →∩∅ : {A B : ℙ X} → ((x : X) → x ∈ A → x ∉ B) → A ∩ B ≡ ∅
  →∩∅ {A = A} {B = B} p i x =
    solveᵖ₂ (((v0 ≡ᵖtrue) →ᵖ (v1 ≡ᵖfalse)) →ᵖ ((v0 ∧ᵇ v1) ≡ᵖfalse))
      (A x) (B x) (p x) i

  →∩∅' : {A B : ℙ X} → ((x : X) → x ∈ A → x ∈ B → ⊥) → A ∩ B ≡ ∅
  →∩∅' {B = B} p = →∩∅ (λ x x∈A → ¬∈→∉ {A = B} (p x x∈A))

  A∩B=∅→A⊆∁B : {A B : ℙ X} → A ∩ B ≡ ∅ → A ⊆ (∁ B)
  A∩B=∅→A⊆∁B {A = A} {B = B} A∩B≡∅ {x = x} x∈A =
    solveᵖ₂
      (((v0 ∧ᵇ v1) ≡ᵖfalse) →ᵖ (v0 ≡ᵖtrue) →ᵖ ((¬ᵇ v1) ≡ᵖtrue))
      (A x) (B x) (λ i → A∩B≡∅ i x) x∈A

  A∩B=∅→B⊆∁A : {A B : ℙ X} → A ∩ B ≡ ∅ → B ⊆ (∁ A)
  A∩B=∅→B⊆∁A {A = A} {B = B} A∩B≡∅ {x = x} x∈B =
    solveᵖ₂
      (((v0 ∧ᵇ v1) ≡ᵖfalse) →ᵖ (v1 ≡ᵖtrue) →ᵖ ((¬ᵇ v0) ≡ᵖtrue))
      (A x) (B x) (λ i → A∩B≡∅ i x) x∈B

  A⊆∁B→A∩B=∅ : {A B : ℙ X} → A ⊆ (∁ B) → A ∩ B ≡ ∅
  A⊆∁B→A∩B=∅ {A = A} {B = B} A⊆∁B i x =
    solveᵖ₂
      (((v0 ≡ᵖtrue) →ᵖ ((¬ᵇ v1) ≡ᵖtrue)) →ᵖ ((v0 ∧ᵇ v1) ≡ᵖfalse))
      (A x) (B x) A⊆∁B i

  B⊆∁A→A∩B=∅ : {A B : ℙ X} → B ⊆ (∁ A) → A ∩ B ≡ ∅
  B⊆∁A→A∩B=∅ {A = A} {B = B} B⊆∁A i x =
    solveᵖ₂
      (((v1 ≡ᵖtrue) →ᵖ ((¬ᵇ v0) ≡ᵖtrue)) →ᵖ ((v0 ∧ᵇ v1) ≡ᵖfalse))
      (A x) (B x) B⊆∁A i

  ∪∩-disjoint : {A B C D : ℙ X} → A ∩ C ≡ ∅ → B ∩ D ≡ ∅ → (A ∪ B) ∩ (C ∩ D) ≡ ∅
  ∪∩-disjoint {A = A} {B = B} {C = C} {D = D} A∩C≡∅ B∩D≡∅ i x =
    solveᵖ₄
      (((v0 ∧ᵇ v2) ≡ᵖfalse) →ᵖ
       ((v1 ∧ᵇ v3) ≡ᵖfalse) →ᵖ
       (((v0 ∨ᵇ v1) ∧ᵇ (v2 ∧ᵇ v3)) ≡ᵖfalse))
      (A x) (B x) (C x) (D x)
      (λ j → A∩C≡∅ j x) (λ j → B∩D≡∅ j x) i


  {-

    Specification and algebraic operations

  -}

  module _
    (P : X → hProp ℓ)(Q : X → hProp ℓ') where

    ∈-∪→Inhab⊎ : (x : X) → x ∈ specify P ∪ specify Q → P x .fst ⊎ Q x .fst
    ∈-∪→Inhab⊎ x x∈∪ with ∈A∪B→∈A+∈B (specify P) (specify Q) x∈∪
    ... | inl p = inl (∈→Inhab P p)
    ... | inr q = inr (∈→Inhab Q q)

    Inhab⊎→∈-∪ : (x : X) → ∥ P x .fst ⊎ Q x .fst ∥₁ → x ∈ specify P ∪ specify Q
    Inhab⊎→∈-∪ x =
      Prop.rec (isProp∈ (specify P ∪ specify Q))
      (λ { (inl p) → ∪-left∈  (specify P) (specify Q) (Inhab→∈ P p)
         ; (inr q) → ∪-right∈ (specify P) (specify Q) (Inhab→∈ Q q) })
