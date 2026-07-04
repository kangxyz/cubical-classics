{-

Extremum, namely Supremum and Infimum of Subsets

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.Extremum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Nullary

open import Classical.Axioms
open import Classical.Preliminary.Logic
open import Classical.Foundations.Powerset
open import Constructive.Algebra.OrderedField
open import Constructive.Algebra.StrictlyOrderedCommRing
  using (Trichotomy ; lt ; eq ; gt)

private
  variable
    ℓ ℓ' : Level


module Extremum ⦃ 🤖 : Oracle ⦄ (𝒦 : OrderedField ℓ ℓ') where

  open Oracle 🤖

  open OrderedFieldStr 𝒦

  private
      K = 𝒦 .fst .fst .fst

      variable
        p q : K


  {-

    Boundedness of Subsets

  -}

  isUpperBounded : ℙ K → Type (ℓ-max ℓ ℓ')
  isUpperBounded A = ∥ Σ[ b ∈ K ] ((r : K) → r ∈ A → r ≤ b) ∥₁

  isLowerBounded : ℙ K → Type (ℓ-max ℓ ℓ')
  isLowerBounded A = ∥ Σ[ b ∈ K ] ((r : K) → r ∈ A → b ≤ r) ∥₁


  {-

    Supremum and Infimum of Subsets

  -}

  record Supremum (A : ℙ K) : Type (ℓ-max ℓ ℓ') where
    field
      sup : K
      bound : (r : K) → r ∈ A → r ≤ sup
      least : (b : K) → ((r : K) → r ∈ A → r ≤ b) → b ≥ sup

  record Infimum (A : ℙ K) : Type (ℓ-max ℓ ℓ') where
    field
      inf : K
      bound : (r : K) → r ∈ A → inf ≤ r
      most  : (b : K) → ((r : K) → r ∈ A → b ≤ r) → b ≤ inf

  open Supremum
  open Infimum


  -- Uniqueness of Extremum

  isPropSupremum : (A : ℙ K) → isProp (Supremum A)
  isPropSupremum A s t i .sup = ≤-asym (s .least _ (t .bound)) (t .least _ (s .bound)) i
  isPropSupremum A s t i .bound =
    isProp→PathP (λ i → isPropΠ2 (λ r _ → isProp≤ {x = r} {y = isPropSupremum A s t i .sup})) (s .bound) (t .bound) i
  isPropSupremum A s t i .least =
    isProp→PathP (λ i → isPropΠ2 (λ b _ → isProp≤ {x = isPropSupremum A s t i .sup} {y = b})) (s .least) (t .least) i

  isPropInfimum : (A : ℙ K) → isProp (Infimum A)
  isPropInfimum A s t i .inf = ≤-asym (t .most _ (s .bound)) (s .most _ (t .bound)) i
  isPropInfimum A s t i .bound =
    isProp→PathP (λ i → isPropΠ2 (λ r _ → isProp≤ {x = isPropInfimum A s t i .inf} {y = r})) (s .bound) (t .bound) i
  isPropInfimum A s t i .most  =
    isProp→PathP (λ i → isPropΠ2 (λ b _ → isProp≤ {x = b} {y = isPropInfimum A s t i .inf})) (s .most)  (t .most)  i


  {-

    Basic Properties

  -}

  <sup→∃∈ : {A : ℙ K}(q : K)(boundary : Supremum A) → q < boundary .sup → ∥ Σ[ x ∈ K ] (q < x) × (x ∈ A) ∥₁
  <sup→∃∈ {A = A} q boundary q<sup with decide (squash₁ {A = Σ[ x ∈ K ] (q < x) × (x ∈ A)})
  ... | yes p = p
  ... | no ¬p = Empty.rec (<≤-asym q<sup (boundary .least _ (λ r r∈A → case-split r (trichotomy q r) r∈A)))
    where
    case-split : (x : K) → Trichotomy (𝒦 .fst .fst) q x → x ∈ A → x ≤ q
    case-split _ (eq q≡x) _ = ≤-refl (sym q≡x)
    case-split _ (gt q>x) _ = <-≤-weaken q>x
    case-split x (lt q<x) x∈A = Empty.rec (¬∃×→∀→¬ (λ _ → isProp<) (λ _ → isProp∈ A) ¬p x q<x x∈A)

  >sup→¬∈ : {A : ℙ K}(q : K)(boundary : Supremum A) → q > boundary .sup → ¬ q ∈ A
  >sup→¬∈ {A = A} q boundary q>sup q∈A with decide (isProp∈ A)
  ... | yes q∈A = <≤-asym q>sup (boundary .bound q q∈A)
  ... | no ¬q∈A = ¬q∈A q∈A

  ⊆→sup≤ : {A B : ℙ K} → A ⊆ B → (SupA : Supremum A)(SupB : Supremum B) → SupA .sup ≤ SupB .sup
  ⊆→sup≤ {A = A} {B = B} A⊆B SupA SupB = SupA .least _ (λ r r∈A → SupB .bound r (A⊆B r∈A))


  >inf→∃∈ : {A : ℙ K}(q : K)(boundary : Infimum A) → q > boundary .inf → ∥ Σ[ x ∈ K ] (x < q) × (x ∈ A) ∥₁
  >inf→∃∈ {A = A} q boundary q>inf with decide (squash₁ {A = Σ[ x ∈ K ] (x < q) × (x ∈ A)})
  ... | yes p = p
  ... | no ¬p = Empty.rec (<≤-asym q>inf (boundary .most _ (λ r r∈A → case-split r (trichotomy q r) r∈A)))
    where
    case-split : (x : K) → Trichotomy (𝒦 .fst .fst) q x → x ∈ A → q ≤ x
    case-split _ (eq q≡x) _ = ≤-refl q≡x
    case-split _ (lt q<x) _ = <-≤-weaken q<x
    case-split x (gt q>x) x∈A = Empty.rec (¬∃×→∀→¬ (λ _ → isProp<) (λ _ → isProp∈ A) ¬p x q>x x∈A)

  <inf→¬∈ : {A : ℙ K}(q : K)(boundary : Infimum A) → q < boundary .inf → ¬ q ∈ A
  <inf→¬∈ {A = A} q boundary q<inf q∈A with decide (isProp∈ A)
  ... | yes q∈A = <≤-asym q<inf (boundary .bound q q∈A)
  ... | no ¬q∈A = ¬q∈A q∈A


  -- By definition, if a subset admits extremum, it must be inhabited and bounded.

  Sup→Inhabited : {A : ℙ K} → Supremum A → isInhabited A
  Sup→Inhabited {A = A} Sup with decide (isPropIsInhabited A)
  ... | yes q∈A = q∈A
  ... | no ¬q∈A = Empty.rec (<≤-asym q-1<q (Sup .least _ (allBound (Sup .sup - 1r))))
    where
    allBound : (x y : K) → y ∈ A → y ≤ x
    allBound x y y∈A = Empty.rec (¬isInhabited→¬x∈A ¬q∈A y y∈A)

  Sup→isUpperBounded : {A : ℙ K} → Supremum A → isUpperBounded A
  Sup→isUpperBounded Sup = ∣ Sup .sup , Sup .bound ∣₁


  -- Supremum of { x | x ≤ b } is just b itself.

  module _ (b : K) where

    prop-≤b : K → hProp _
    prop-≤b x = (x ≤ b) , isProp≤

    sub-≤b : ℙ K
    sub-≤b = specify prop-≤b

    b∈sub : b ∈ sub-≤b
    b∈sub = Inhab→∈ prop-≤b (≤-refl refl)

    Sup≤b : Supremum sub-≤b
    Sup≤b .sup = b
    Sup≤b .bound r = ∈→Inhab prop-≤b
    Sup≤b .least _ h = h _ b∈sub

    Sup≤b≡b : (Sup : Supremum sub-≤b) → Sup .sup ≡ b
    Sup≤b≡b Sup i = isPropSupremum sub-≤b Sup Sup≤b i .sup


  -- If the subset is bounded by some element, its extremum is bounded by the same one.

  supUpperBounded : {A : ℙ K}(b : K)(Sup : Supremum A) → ((x : K) → x ∈ A → x ≤ b) → Sup .sup ≤ b
  supUpperBounded {A = A} b Sup b≥x∈A = ⊆→sup≤ A⊆[x≤b] Sup (Sup≤b b)
    where
    A⊆[x≤b] : A ⊆ sub-≤b b
    A⊆[x≤b] x∈A = Inhab→∈ (prop-≤b b) (b≥x∈A _ x∈A)

  supLowerBounded : {A : ℙ K}(b : K)(Sup : Supremum A) → ((x : K) → x ∈ A → b ≤ x) → Sup .sup ≥ b
  supLowerBounded b Sup b≤x∈A =
    proof _ , isProp≤ by do
    (x , x∈A) ← Sup→Inhabited Sup
    return (≤-trans (b≤x∈A x x∈A) (Sup .bound x x∈A))


  {-

    Taking - x for all x ∈ some subset and reverse its extremum

  -}

  module _ (A : ℙ K) where

    -prop : K → hProp _
    -prop x = - x ∈ A , isProp∈ A

    -ℙ : ℙ K
    -ℙ = specify -prop


  x∈A→-x∈-A : (A : ℙ K){x : K} → x ∈ A → - x ∈ -ℙ A
  x∈A→-x∈-A A {x = x} x∈A = Inhab→∈ (-prop A) (subst (_∈ A) (sym (-Idempotent x)) x∈A)

  -ℙ-Idem : (A : ℙ K) → -ℙ (-ℙ A) ≡ A
  -ℙ-Idem A = bi⊆→≡ ⊆-helper ⊇helper
    where
    ⊆-helper : {x : K} → x ∈ -ℙ (-ℙ A) → x ∈ A
    ⊆-helper {x = x} x∈ =
      subst (_∈ A) (-Idempotent x) (∈→Inhab (-prop A) (∈→Inhab (-prop (-ℙ A)) x∈))

    ⊇helper : {x : K} → x ∈ A → x ∈ -ℙ (-ℙ A)
    ⊇helper {x = x} x∈ =
      Inhab→∈ (-prop (-ℙ A)) (Inhab→∈ (-prop A) (subst (_∈ A) (sym (-Idempotent x)) x∈))


  isInhabited- : (A : ℙ K) → isInhabited A → isInhabited (-ℙ A)
  isInhabited- A = Prop.map (λ (x , x∈A) → - x , x∈A→-x∈-A A x∈A)


  isUpperBounded→isLowerBounded : (A : ℙ K) → isUpperBounded A → isLowerBounded (-ℙ A)
  isUpperBounded→isLowerBounded A =
    Prop.map (λ (b , b≥r∈A) → - b , (λ r r∈-A → -lReverse≤ (b≥r∈A _ (∈→Inhab (-prop A) r∈-A))))

  isLowerBounded→isUpperBounded : (A : ℙ K) → isLowerBounded A → isUpperBounded (-ℙ A)
  isLowerBounded→isUpperBounded A =
    Prop.map (λ (b , b≤r∈A) → - b , (λ r r∈-A → -rReverse≤ (b≤r∈A _ (∈→Inhab (-prop A) r∈-A))))


  Sup→Inf- : (A : ℙ K) → Supremum A → Infimum (-ℙ A)
  Sup→Inf- A Sup .inf = - Sup .sup
  Sup→Inf- A Sup .bound r r∈-A = -lReverse≤ (Sup .bound _ (∈→Inhab (-prop A) r∈-A))
  Sup→Inf- A Sup .most  b b≤r∈-A = -rReverse≤ (Sup .least _ -b≥r∈-A)
    where
    -b≥r∈-A : (r : K) → r ∈ A → - b ≥ r
    -b≥r∈-A r r∈A = -rReverse≤ (b≤r∈-A _ (x∈A→-x∈-A A r∈A))

  Inf→Sup- : (A : ℙ K) → Infimum A → Supremum (-ℙ A)
  Inf→Sup- A Inf .sup = - Inf .inf
  Inf→Sup- A Inf .bound r r∈-A = -rReverse≤ (Inf .bound _ (∈→Inhab (-prop A) r∈-A))
  Inf→Sup- A Inf .least b b≥r∈-A = -lReverse≤ (Inf .most  _ -b≤r∈-A)
    where
    -b≤r∈-A : (r : K) → r ∈ A → - b ≤ r
    -b≤r∈-A r r∈A = -lReverse≤ (b≥r∈-A _ (x∈A→-x∈-A A r∈A))

  Sup→Inf : (A : ℙ K) → Supremum (-ℙ A) → Infimum A
  Sup→Inf A Sup = subst Infimum (-ℙ-Idem A) (Sup→Inf- _ Sup)

  Inf→Sup : (A : ℙ K) → Infimum (-ℙ A) → Supremum A
  Inf→Sup A Sup = subst Supremum (-ℙ-Idem A) (Inf→Sup- _ Sup)
