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

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ

  or-and-absorp : ∀ x y → x or (x and y) ≡ x
  or-and-absorp true  true  = refl
  or-and-absorp true  false = refl
  or-and-absorp false true  = refl
  or-and-absorp false false = refl

  and-or-absorp : ∀ x y → x and (x or y) ≡ x
  and-or-absorp true  true  = refl
  and-or-absorp true  false = refl
  and-or-absorp false true  = refl
  and-or-absorp false false = refl

  or-and-dist : ∀ x y z → x or (y and z) ≡ (x or y) and (x or z)
  or-and-dist true  true  true  = refl
  or-and-dist true  true  false = refl
  or-and-dist true  false true  = refl
  or-and-dist true  false false = refl
  or-and-dist false true  true  = refl
  or-and-dist false true  false = refl
  or-and-dist false false true  = refl
  or-and-dist false false false = refl

  and-or-dist : ∀ x y z → x and (y or z) ≡ (x and y) or (x and z)
  and-or-dist true  true  true  = refl
  and-or-dist true  true  false = refl
  and-or-dist true  false true  = refl
  and-or-dist true  false false = refl
  and-or-dist false true  true  = refl
  and-or-dist false true  false = refl
  and-or-dist false false true  = refl
  and-or-dist false false false = refl

  or-compt : ∀ x → x or (not x) ≡ true
  or-compt true  = refl
  or-compt false = refl

  and-compt : ∀ x → x and (not x) ≡ false
  and-compt true  = refl
  and-compt false = refl

  or-and-deMorgan : ∀ x y → (not x) or (not y) ≡ not (x and y)
  or-and-deMorgan true  true  = refl
  or-and-deMorgan true  false = refl
  or-and-deMorgan false true  = refl
  or-and-deMorgan false false = refl

  and-or-deMorgan : ∀ x y → (not x) and (not y) ≡ not (x or y)
  and-or-deMorgan true  true  = refl
  and-or-deMorgan true  false = refl
  and-or-deMorgan false true  = refl
  and-or-deMorgan false false = refl

  and-cancelˡ : ∀ x y → x and y ≡ true → x ≡ true
  and-cancelˡ true  true  _ = refl
  and-cancelˡ true  false _ = refl
  and-cancelˡ false true  p = Empty.rec (false≢true p)
  and-cancelˡ false false p = Empty.rec (false≢true p)

  and-cancelʳ : ∀ x y → x and y ≡ true → y ≡ true
  and-cancelʳ true  true  _ = refl
  and-cancelʳ true  false p = Empty.rec (false≢true p)
  and-cancelʳ false true  _ = refl
  and-cancelʳ false false p = Empty.rec (false≢true p)

  and-forceˡ : ∀ x y → x and y ≡ false → x ≡ true → y ≡ false
  and-forceˡ true  true  p _ = Empty.rec (true≢false p)
  and-forceˡ true  false _ _ = refl
  and-forceˡ false true  _ q = Empty.rec (false≢true q)
  and-forceˡ false false _ _ = refl

  and-absorpˡ : ∀ x y → x ≡ false → x and y ≡ false
  and-absorpˡ true  true  p = Empty.rec (true≢false p)
  and-absorpˡ true  false _ = refl
  and-absorpˡ false true  _ = refl
  and-absorpˡ false false _ = refl

  or-dichotomy : ∀ x y → x or y ≡ true → (x ≡ true) ⊎ (y ≡ true)
  or-dichotomy true _ _ = inl refl
  or-dichotomy false true _ = inr refl
  or-dichotomy false false p = Empty.rec (false≢true p)

  or≡true : ∀ x y → (x ≡ true) ⊎ (y ≡ true) → x or y ≡ true
  or≡true true  true  _ = refl
  or≡true true  false _ = refl
  or≡true false true  _ = refl
  or≡true false false (inl p) = Empty.rec (false≢true p)
  or≡true false false (inr p) = Empty.rec (false≢true p)


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
  ∁-Unip A i x = notnot (A x) i

  ∉→∈∁ : {x : X}{A : ℙ X} → x ∉ A → x ∈ (∁ A)
  ∉→∈∁ x∉A i = not (x∉A i)

  ∈∁→∉ : {x : X}{A : ℙ X} → x ∈ (∁ A) → x ∉ A
  ∈∁→∉ x∈∁A = sym (notnot _) ∙ cong not x∈∁A


  {-

    Binary Union

  -}

  ∪-lZero : (A : ℙ X) → total ∪ A ≡ total
  ∪-lZero A i x = or-zeroˡ (A x) i

  ∪-rZero : (A : ℙ X) → A ∪ total ≡ total
  ∪-rZero A i x = or-zeroʳ (A x) i

  ∪-lUnit : (A : ℙ X) → ∅ ∪ A ≡ A
  ∪-lUnit A i x = or-identityˡ (A x) i

  ∪-rUnit : (A : ℙ X) → A ∪ ∅ ≡ A
  ∪-rUnit A i x = or-identityʳ (A x) i

  ∪-Comm : (A B : ℙ X) → A ∪ B ≡ B ∪ A
  ∪-Comm A B i x = or-comm (A x) (B x) i

  ∪-Assoc : (A B C : ℙ X) → A ∪ (B ∪ C) ≡ (A ∪ B) ∪ C
  ∪-Assoc A B C i x = or-assoc (A x) (B x) (C x) i

  ∪-Idem : (A : ℙ X) → A ∪ A ≡ A
  ∪-Idem A i x = or-idem (A x) i

  ∪-left∈ : {x : X}(A B : ℙ X) → x ∈ A → x ∈ (A ∪ B)
  ∪-left∈ {x = x} _ B x∈A = (λ i → x∈A i or B x) ∙ or-zeroˡ true

  ∪-right∈ : {x : X}(A B : ℙ X) → x ∈ B → x ∈ (A ∪ B)
  ∪-right∈ {x = x} A _ x∈B = (λ i → A x or x∈B i) ∙ or-zeroʳ _

  ∪-left⊆ : (A B : ℙ X) → A ⊆ (A ∪ B)
  ∪-left⊆ A B = ∪-left∈ A B

  ∪-right⊆ : (A B : ℙ X) → B ⊆ (A ∪ B)
  ∪-right⊆ A B = ∪-right∈ A B

  ∈A∪B→∈A+∈B : {x : X}(A B : ℙ X) → x ∈ (A ∪ B) → (x ∈ A) ⊎ (x ∈ B)
  ∈A∪B→∈A+∈B {x = x} A B x∈A∪B = or-dichotomy (A x) (B x) x∈A∪B

  ∈A+∈B→∈A∪B : {x : X}(A B : ℙ X) → ∥ (x ∈ A) ⊎ (x ∈ B) ∥₁ → x ∈ (A ∪ B)
  ∈A+∈B→∈A∪B {x = x} A B = Prop.rec (isProp∈ (A ∪ B)) (λ ∈A+∈B → or≡true (A x) (B x) ∈A+∈B)

  ⊆→⊆∪ : {A B C : ℙ X} → A ⊆ C → B ⊆ C → A ∪ B ⊆ C
  ⊆→⊆∪ {A = A} {B = B} A⊆C B⊆C x∈A∪B with ∈A∪B→∈A+∈B A B x∈A∪B
  ... | inl x∈A = A⊆C x∈A
  ... | inr x∈B = B⊆C x∈B


  {-

    Binary Intersection

  -}

  ∩-lZero : (A : ℙ X) → ∅ ∩ A ≡ ∅
  ∩-lZero A i x = and-zeroˡ (A x) i

  ∩-rZero : (A : ℙ X) → A ∩ ∅ ≡ ∅
  ∩-rZero A i x = and-zeroʳ (A x) i

  ∩-lUnit : (A : ℙ X) → total ∩ A ≡ A
  ∩-lUnit A i x = and-identityˡ (A x) i

  ∩-rUnit : (A : ℙ X) → A ∩ total ≡ A
  ∩-rUnit A i x = and-identityʳ (A x) i

  ∩-Comm : (A B : ℙ X) → A ∩ B ≡ B ∩ A
  ∩-Comm A B i x = and-comm (A x) (B x) i

  ∩-Assoc : (A B C : ℙ X) → A ∩ (B ∩ C) ≡ (A ∩ B) ∩ C
  ∩-Assoc A B C i x = and-assoc (A x) (B x) (C x) i

  ∩-Idem : (A : ℙ X) → A ∩ A ≡ A
  ∩-Idem A i x = and-idem (A x) i

  ∈→∈∩ : {x : X}(A B : ℙ X) → x ∈ A → x ∈ B → x ∈ (A ∩ B)
  ∈→∈∩ A B x∈A x∈B i = x∈A i and x∈B i

  ⊆→⊆∩ : {C : ℙ X}(A B : ℙ X) → C ⊆ A → C ⊆ B → C ⊆ (A ∩ B)
  ⊆→⊆∩ A B C⊆A C⊆B x∈C = ∈→∈∩ A B (C⊆A x∈C) (C⊆B x∈C)

  left∈-∩ : {x : X}(A B : ℙ X) → x ∈ (A ∩ B) → x ∈ A
  left∈-∩ {x = x} A B x∈A∩B = and-cancelˡ (A x) (B x) x∈A∩B

  right∈-∩ : {x : X}(A B : ℙ X) → x ∈ (A ∩ B) → x ∈ B
  right∈-∩ {x = x} A B x∈A∩B = and-cancelʳ (A x) (B x) x∈A∩B

  ⊆→∩⊆ : (A B C : ℙ X) → A ⊆ B → (A ∩ C) ⊆ (B ∩ C)
  ⊆→∩⊆ A B C A⊆B x∈A∩C = ∈→∈∩ B C (A⊆B (left∈-∩ A C x∈A∩C)) (right∈-∩ A C x∈A∩C)

  A⊆B+B∩C≡∅→A∩C≡∅ : {A B C : ℙ X} → A ⊆ B → B ∩ C ≡ ∅ → A ∩ C ≡ ∅
  A⊆B+B∩C≡∅→A∩C≡∅ {A = A} {B = B} {C = C} A⊆B B∩V≡∅ = A⊆∅→A≡∅ (subst ((A ∩ C) ⊆_) B∩V≡∅ (⊆→∩⊆ A B C A⊆B))

  A⊆B→A∩B≡A : {A B : ℙ X} → A ⊆ B → A ∩ B ≡ A
  A⊆B→A∩B≡A {A = A} {B = B} A⊆B = bi⊆→≡ (left∈-∩ A B) A⊆A∩B
    where
    A⊆A∩B : A ⊆ A ∩ B
    A⊆A∩B x∈A = ∈→∈∩ A B x∈A (A⊆B x∈A)


  {-

    Algebraic Laws of Boolean Algebra

  -}

  -- Absorption laws

  ∪-∩-Absorp : (A B : ℙ X) → A ∪ (A ∩ B) ≡ A
  ∪-∩-Absorp A B i x = or-and-absorp (A x) (B x) i

  ∩-∪-Absorp : (A B : ℙ X) → A ∩ (A ∪ B) ≡ A
  ∩-∪-Absorp A B i x = and-or-absorp (A x) (B x) i


  -- Distribution laws

  ∪-∩-rDist : (A B C : ℙ X) → A ∪ (B ∩ C) ≡ (A ∪ B) ∩ (A ∪ C)
  ∪-∩-rDist A B C i x = or-and-dist (A x) (B x) (C x) i

  ∩-∪-rDist : (A B C : ℙ X) → A ∩ (B ∪ C) ≡ (A ∩ B) ∪ (A ∩ C)
  ∩-∪-rDist A B C i x = and-or-dist (A x) (B x) (C x) i

  ∪-∩-lDist : (A B C : ℙ X) → (A ∩ B) ∪ C ≡ (A ∪ C) ∩ (B ∪ C)
  ∪-∩-lDist A B C = ∪-Comm (A ∩ B) C
    ∙ ∪-∩-rDist C A B ∙ (λ i → ∪-Comm C A i ∩ ∪-Comm C B i)

  ∩-∪-lDist : (A B C : ℙ X) → (A ∪ B) ∩ C ≡ (A ∩ C) ∪ (B ∩ C)
  ∩-∪-lDist A B C = ∩-Comm (A ∪ B) C
    ∙ ∩-∪-rDist C A B ∙ (λ i → ∩-Comm C A i ∪ ∩-Comm C B i)


  -- Complementation laws

  ∪-Compt : (A : ℙ X) → A ∪ (∁ A) ≡ total
  ∪-Compt A i x = or-compt (A x) i

  ∩-Compt : (A : ℙ X) → A ∩ (∁ A) ≡ ∅
  ∩-Compt A i x = and-compt (A x) i


  -- de Morgan laws

  ∪-∩-deMorgan : (A B : ℙ X) → (∁ A) ∪ (∁ B) ≡ ∁ (A ∩ B)
  ∪-∩-deMorgan A B i x = or-and-deMorgan (A x) (B x) i

  ∩-∪-deMorgan : (A B : ℙ X) → (∁ A) ∩ (∁ B) ≡ ∁ (A ∪ B)
  ∩-∪-deMorgan A B i x = and-or-deMorgan (A x) (B x) i


  {-

    Facts relating non-intersecting subsets and complementary subsets

  -}

  →∩∅ : {A B : ℙ X} → ((x : X) → x ∈ A → x ∉ B) → A ∩ B ≡ ∅
  →∩∅ {A = A} {B = B} p i x with dichotomy∈ x A
  ... | yeah x∈A = x∈A i and p x x∈A i
  ... | nope x∉A = and-absorpˡ (A x) (B x) x∉A i

  →∩∅' : {A B : ℙ X} → ((x : X) → x ∈ A → x ∈ B → ⊥) → A ∩ B ≡ ∅
  →∩∅' {B = B} p = →∩∅ (λ x x∈A → ¬∈→∉ {A = B} (p x x∈A))

  A∩B=∅→A⊆∁B : {A B : ℙ X} → A ∩ B ≡ ∅ → A ⊆ (∁ B)
  A∩B=∅→A⊆∁B {A = A} {B = B} A∩B≡∅ {x = x} x∈A =
    ∉→∈∁ {A = B} (and-forceˡ (A x) (B x) (λ i → A∩B≡∅ i x) x∈A)

  A∩B=∅→B⊆∁A : {A B : ℙ X} → A ∩ B ≡ ∅ → B ⊆ (∁ A)
  A∩B=∅→B⊆∁A {A = A} {B} A∩B≡∅ = A∩B=∅→A⊆∁B {A = B} (∩-Comm B A ∙ A∩B≡∅)

  A⊆∁B→A∩B=∅ : {A B : ℙ X} → A ⊆ (∁ B) → A ∩ B ≡ ∅
  A⊆∁B→A∩B=∅ {X = X} {A = A} {B = B} A⊆∁B = →∩∅ helper
    where
    helper : (x : X) → x ∈ A → x ∉ B
    helper x x∈A = ∈∁→∉ {A = B} (A⊆∁B x∈A)

  B⊆∁A→A∩B=∅ : {A B : ℙ X} → B ⊆ (∁ A) → A ∩ B ≡ ∅
  B⊆∁A→A∩B=∅ {A = A} {B} B⊆∁A = ∩-Comm A B ∙ A⊆∁B→A∩B=∅ B⊆∁A


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
