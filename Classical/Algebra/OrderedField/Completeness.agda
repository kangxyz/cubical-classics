{-

MacNeille Completeness of Ordered Fields

`isMacNeilleComplete` is the supremum principle for powersets:
every inhabited subset with an upper bound has a least upper bound.

For linearly ordered fields, this is the usual real-analysis
Dedekind completeness, i.e. the least-upper-bound property. The name
MacNeille is used here because the cut construction is the
Dedekind-MacNeille completion of the underlying order. Constructively,
this should be kept separate from other Dedekind-cut completeness notions.

-}
{-# OPTIONS --safe #-}
module Classical.Algebra.OrderedField.Completeness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Relation.Nullary
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection

open import Classical.Axioms
open import Classical.Preliminary.Logic
open import Classical.Foundations.Powerset
open import Constructive.Algebra.OrderedCommRing.Morphism
open import Constructive.Algebra.StrictlyOrderedCommRing
open import Constructive.Algebra.StrictlyOrderedCommRing.Morphism
open import Constructive.Algebra.StrictlyOrderedCommRing.Archimedes
open import Constructive.Algebra.StrictlyOrderedField
open import Constructive.Algebra.StrictlyOrderedField.Morphism
open import Classical.Algebra.OrderedField.Extremum

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    𝒦  : OrderedField ℓ   ℓ'
    𝒦' : OrderedField ℓ'' ℓ'''

private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (b ε : 𝓡 .fst) → (b - ε) + ε ≡ b
    helper1 _ _ = solve! 𝓡


module MacNeilleCompleteOrderedField ⦃ 🤖 : Oracle ⦄ (𝒦 : OrderedField ℓ ℓ') where

  open Oracle 🤖

  private
    K = 𝒦 .fst .fst .fst

    variable
      p q : K

  open OrderedFieldStr 𝒦

  open Extremum 𝒦
  open Supremum
  open Infimum


  {-

    The Supremum Principle / MacNeille Completeness

  -}

  isMacNeilleComplete : Type (ℓ-max ℓ ℓ')
  isMacNeilleComplete = {A : ℙ K} → isInhabited A → isUpperBounded A → Supremum A

  isPropIsMacNeilleComplete : isProp isMacNeilleComplete
  isPropIsMacNeilleComplete = isPropImplicitΠ (λ _ → isPropΠ2 (λ _ _ → isPropSupremum _))


  isLowerMacNeilleComplete : Type (ℓ-max ℓ ℓ')
  isLowerMacNeilleComplete = {A : ℙ K} → isInhabited A → isLowerBounded A → Infimum A


  -- Equivalence of upper/lower MacNeille completeness

  isMacNeilleComplete→isLowerMacNeilleComplete : isMacNeilleComplete → isLowerMacNeilleComplete
  isMacNeilleComplete→isLowerMacNeilleComplete getSup inhab bound =
    Sup→Inf _ (getSup (isInhabited- _ inhab) (isLowerBounded→isUpperBounded _ bound))

  isLowerMacNeilleComplete→isMacNeilleComplete : isLowerMacNeilleComplete → isMacNeilleComplete
  isLowerMacNeilleComplete→isMacNeilleComplete getInf inhab bound =
    Inf→Sup _ (getInf (isInhabited- _ inhab) (isUpperBounded→isLowerBounded _ bound))


  {-

    MacNeille Completeness Implies the Archimedean Property

  -}


  private

    module _
      (getSup : isMacNeilleComplete)(q ε : K)(ε>0 : ε > 0r)
      (insurmountable' : (n : ℕ) → ¬ n ⋆ ε > q)
      where

      insurmountable : (n : ℕ) → n ⋆ ε ≤ q
      insurmountable n = ¬<→≥ (insurmountable' n)

      P : K → hProp _
      P q = ∥ Σ[ n ∈ ℕ ] n ⋆ ε > q ∥₁ , squash₁

      bounded : ℙ K
      bounded = specify P

      0∈bounded : 0r ∈ bounded
      0∈bounded = Inhab→∈ P ∣ 1 , subst (_> 0r) (sym (1⋆q≡q _)) ε>0 ∣₁

      q-bound : (x : K) → x ∈ bounded → x < q
      q-bound x x∈b =
        proof _ , isProp< by do
        (n , nε>q) ← ∈→Inhab P x∈b
        return (<≤-trans nε>q (insurmountable n))

      q-bound' : (x : K) → x ∈ bounded → x ≤ q
      q-bound' x x∈b = <-≤-weaken (q-bound x x∈b)

      boundary : Supremum bounded
      boundary = getSup ∣ 0r , 0∈bounded ∣₁ ∣ q , q-bound' ∣₁

      module _ (p : K)(p>q-ε : boundary .sup - ε < p)(p∈A : p ∈ bounded) where

        ∥n⋆ε>p+ε∥ : ∥ Σ[ n ∈ ℕ ] n ⋆ ε > p + ε ∥₁
        ∥n⋆ε>p+ε∥ = do
          (n , n⋆ε>p) ← ∈→Inhab P p∈A
          return (suc n ,
            subst (_> p + ε) (sym (sucn⋆q≡n⋆q+q n _)) (+-rPres< {z = ε} n⋆ε>p))

        open Helpers (StrictlyOrderedCommRing→CommRing (𝒦 .fst))

        q<p+ε : p + ε > boundary .sup
        q<p+ε = subst (_< p + ε) (helper1 _ _) (+-rPres< {z = ε} p>q-ε)

        no-way' : ⊥
        no-way' = <≤-asym q<p+ε (boundary .bound _ (Inhab→∈ P ∥n⋆ε>p+ε∥))

      q-ε<sup : boundary .sup - ε < boundary .sup
      q-ε<sup = -rPos→< ε>0

      no-way : ⊥
      no-way = proof _ , isProp⊥ by do
        (p , p>q-ε , p∈A) ← <sup→∃∈ _ boundary q-ε<sup
        return (no-way' _ p>q-ε p∈A)


  -- A MacNeille complete ordered field is Archimedean.

  isMacNeilleComplete→isArchimedean∥∥ : isMacNeilleComplete → isArchimedean∥∥ (𝒦 .fst)
  isMacNeilleComplete→isArchimedean∥∥ getSup q ε ε>0 = ¬∀¬→∃ (no-way getSup q ε ε>0)

  isMacNeilleComplete→isArchimedean : isMacNeilleComplete → isArchimedean (𝒦 .fst)
  isMacNeilleComplete→isArchimedean getSup = isArchimedean∥∥→isArchimedean (𝒦 .fst) (isMacNeilleComplete→isArchimedean∥∥ getSup)


module _ ⦃ 🤖 : Oracle ⦄ where

  open MacNeilleCompleteOrderedField

  MacNeilleCompleteOrderedField : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
  MacNeilleCompleteOrderedField ℓ ℓ' = Σ[ 𝒦 ∈ OrderedField ℓ ℓ' ] isMacNeilleComplete 𝒦


  module MacNeilleCompleteOrderedFieldStr (𝒦 : MacNeilleCompleteOrderedField ℓ ℓ') where

  -- TODO: Basic corollaries of MacNeille completeness.


  {-

    Homomorphism between MacNeille complete ordered fields

  -}

  module MacNeilleCompleteOrderedFieldHom (f : OrderedFieldHom 𝒦 𝒦')
    (getSup  : isMacNeilleComplete 𝒦 )
    (getSup' : isMacNeilleComplete 𝒦')
    where

    open OrderedFieldStr 𝒦
    open OrderedFieldStr 𝒦' using ()
      renaming ( _<_ to _<'_ ; _≤_ to _≤'_
               ; _>_ to _>'_ ; _≥_ to _≥'_
               ; isProp< to isProp<'
               ; trichotomy to trichotomy'
               ; <-asym  to <'-asym
               ; <-trans to <'-trans
               ; is-set  to is-set')
    open OrderedCommRingHom           f
    open OrderedCommRingHomProperties {𝓡 = 𝒦 .fst} {𝓡' = 𝒦' .fst} f
    open OrderedFieldHomStr {𝒦' = 𝒦} {𝒦 = 𝒦'} f

    private
      K  = 𝒦  .fst .fst .fst
      K' = 𝒦' .fst .fst .fst
      isSetK  = is-set
      isSetK' = is-set'
      f-map = ring-hom .fst


    findBetween : isDense
    findBetween = isArchimedean→isDense (isMacNeilleComplete→isArchimedean _ getSup')

    open Extremum 𝒦
    open Supremum

    module _ (y : K') where

      P : K → hProp _
      P x = (f-map x <' y) , isProp<'

      bounded : ℙ K
      bounded = specify P

      bounded-inhab : isInhabited bounded
      bounded-inhab = do
        (r , fr<y) ←
          isUnbounded→isLowerUnbounded
          (isArchimedean→isUnbounded
          (isMacNeilleComplete→isArchimedean _ getSup')) y
        return (r , Inhab→∈ P fr<y)

      bounded-is-bounded : isUpperBounded bounded
      bounded-is-bounded = do
        (r , y<fr) ←
          isArchimedean→isUnbounded
          (isMacNeilleComplete→isArchimedean _ getSup') y
        return (r , λ s s∈b →
          <-≤-weaken (homRefl< s r (<'-trans (∈→Inhab P s∈b) y<fr)))

      boundary : Supremum bounded
      boundary = getSup bounded-inhab bounded-is-bounded

      x = boundary .sup

      fiber-path : f-map x ≡ y
      fiber-path = case-split (trichotomy' (f-map x) y)
        where
        case-split : Trichotomy (𝒦' .fst .fst) (f-map x) y → f-map x ≡ y
        case-split (eq fx≡y) = fx≡y
        case-split (lt fx<y) = Empty.rec (
          proof _ , isProp⊥ by do
          (r , fx<fr , fr<y) ← findBetween fx<y
          return (<≤-asym (homRefl< x r fx<fr) (boundary .bound r (Inhab→∈ P fr<y))))
        case-split (gt fx>y) = Empty.rec (
          proof _ , isProp⊥ by do
          (r , y<fr , fr<fx) ← findBetween fx>y
          (s , r<s , s∈b) ← <sup→∃∈ r boundary (homRefl< r x fr<fx)
          return (<'-asym (<'-trans y<fr (homPres< r s r<s)) (∈→Inhab P s∈b)))


    isEmbedding-f : isEmbedding f-map
    isEmbedding-f = injEmbedding isSetK' (λ p → homRefl≡ _ _ p)

    isSurjection-f : isSurjection f-map
    isSurjection-f y = ∣ _ , fiber-path y ∣₁

    -- A homomorphism between MacNeille complete ordered fields is always an isomorphism.

    isEquiv-f : isEquiv f-map
    isEquiv-f = isEmbedding×isSurjection→isEquiv (isEmbedding-f , isSurjection-f)

    isOrderedFieldEquivMacNeilleComplete : isOrderedFieldEquiv {𝒦 = 𝒦} {𝒦' = 𝒦'} f
    isOrderedFieldEquivMacNeilleComplete = isEquiv-f


  {-

    SIP for MacNeille Complete Ordered Fields

  -}

  open MacNeilleCompleteOrderedField
  open MacNeilleCompleteOrderedFieldHom

  uaMacNeilleCompleteOrderedField : (𝒦 𝒦' : MacNeilleCompleteOrderedField ℓ ℓ') → OrderedFieldHom (𝒦 .fst) (𝒦' .fst) → 𝒦 ≡ 𝒦'
  uaMacNeilleCompleteOrderedField 𝒦 𝒦' f i .fst =
    uaOrderedField {𝒦 = 𝒦 .fst} {𝒦' = 𝒦' .fst} {f = f} (isOrderedFieldEquivMacNeilleComplete f (𝒦 .snd) (𝒦' .snd)) i
  uaMacNeilleCompleteOrderedField 𝒦 𝒦' f i .snd =
    isProp→PathP (λ i → isPropIsMacNeilleComplete (uaMacNeilleCompleteOrderedField 𝒦 𝒦' f i .fst)) (𝒦 .snd) (𝒦' .snd) i
