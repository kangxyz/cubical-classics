{-

The universal property of classical Dedekind cuts

-}
{-# OPTIONS --safe --lossy-unification #-}
module Classical.DedekindCut.UniversalProperty where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels hiding (extend)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Nullary
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection

open import Classical.Axioms
open import Classical.Foundations.Powerset
open import Classical.Preliminary.Logic

open import Constructive.Algebra.OrderedCommRing.Morphism
open import Constructive.Algebra.LinearlyOrderedCommRing
import Constructive.Algebra.LinearlyOrderedCommRing.Morphism as LinearMorphism
open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedean
open import Constructive.Algebra.LinearlyOrderedField
open import Constructive.Algebra.LinearlyOrderedField.Morphism
open import Classical.Algebra.OrderedField.Extremum
open import Classical.Algebra.OrderedField.Completeness
open import Classical.DedekindCut.Base
open import Classical.DedekindCut.Algebra
open import Classical.DedekindCut.Order
open import Classical.DedekindCut.Multiplication

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (x y : 𝓡 .fst) → (x · (- y)) ≡ - (x · y)
    helper1 _ _ = solve! 𝓡

    helper2 : (x y : 𝓡 .fst) → ((- x) · y) ≡ - (x · y)
    helper2 _ _ = solve! 𝓡


module UniversalProperty ⦃ 🤖 : Oracle ⦄
  (𝒦  : LinearlyOrderedField ℓ ℓ')(archimedean : isArchimedean (𝒦 .fst .fst)) where

  open Oracle 🤖

  open MacNeilleCompleteOrderedField

  module _
    (𝒦' : MacNeilleCompleteOrderedField ℓ'' ℓ''')(f : LinearlyOrderedFieldHom 𝒦 (𝒦' .fst)) where


    open LinearlyOrderedFieldStr 𝒦
    open Basics   𝒦
    open Algebra  𝒦 archimedean
    open Order    𝒦 archimedean
    open Multiplication 𝒦 archimedean
    open DedekindCut

    open LinearlyOrderedFieldStr (𝒦' .fst) using ()
      renaming ( _+_ to _+'_ ; -_ to -'_ ; _-_ to _-'_
               ; 0r to 0r' ; 1r to 1r'
               ; _·_ to _·'_
               ; +IdL to +IdL' ; +IdR to +IdR'
               ; +InvL to +InvL'
               ; +Assoc to +Assoc'
               ; 0LeftAnnihilates  to 0LeftAnnihilates'
               ; 0RightAnnihilates to 0RightAnnihilates'
               ; _<_ to _<'_ ; _≤_ to _≤'_
               ; _>_ to _>'_ ; _≥_ to _≥'_
               ; _>0 to _>0'_
               ; isProp< to isProp<'
               ; isProp≤ to isProp≤'
               ; trichotomy to trichotomy'
               ; <-asym   to <'-asym
               ; <-arefl  to <'-arefl
               ; ≤-refl   to ≤-refl'
               ; ≤≃¬> to ≤'≃¬>
               ; <-≤-weaken to <-≤-weaken'
               ; Diff>0→< to Diff>0→<'
               ; <≤-total to <≤-total'
               ; <≤-trans to <≤-trans'
               ; ≤<-trans to ≤<-trans'
               ; <≤-asym  to <≤-asym'
               ; ¬<→≥ to ¬<→≥'
               ; +-Pres< to +-Pres<'
               ; ·-PosPres≥0>0 to ·-PosPres≥0>0'
               ; ·-PosPres> to ·-PosPres>'
               ; <-+-Decompose to <-+-Decompose'
               ; <-·-Decompose to <-·-Decompose')
    open OrderedCommRingHom           f
    open LinearMorphism.OrderedCommRingHomProperties {𝓡 = 𝒦 .fst} {𝓡' = 𝒦' .fst .fst} f
    open LinearlyOrderedFieldHomStr {𝒦' = 𝒦} {𝒦 = 𝒦' .fst} f
    open IsCommRingHom (ring-hom .snd)
    module 𝕂LO = LinearlyOrderedCommRingStr 𝕂LinearlyOrderedCommRing

    private
      K  = 𝒦  .fst .fst .fst
      K' = 𝒦' .fst .fst .fst .fst
      f-map = ring-hom .fst

    getSup = 𝒦' .snd
    findBetween = isArchimedean→isDense (isMacNeilleComplete→isArchimedean _ (𝒦' .snd))

    open Extremum (𝒦' .fst)
    open Supremum


    module _ (a : 𝕂) where

      map-prop : K' → hProp _
      map-prop x = ((q : K) → q ∈ a .upper → x <' f-map q) , isPropΠ2 (λ _ _ → isProp<')

      map-sub : ℙ K'
      map-sub = specify map-prop

      private
        map-sub-inhab : isInhabited map-sub
        map-sub-inhab = do
          (q , q<r∈upper) ← a .lower-inhab
          return (f-map q , Inhab→∈ map-prop (λ p p∈upper → homPres< _ _ (q<r∈upper _ p∈upper)))

        map-sub-bound : isUpperBounded map-sub
        map-sub-bound = do
          (q , q∈upper) ← a .upper-inhab
          return (f-map q , (λ r r∈map → <-≤-weaken' (∈→Inhab map-prop r∈map _ q∈upper)))

      map-sup : Supremum map-sub
      map-sup = getSup map-sub-inhab map-sub-bound

      map-helper : K'
      map-helper = map-sup .sup


      >sup-helper : (x : K') → ¬ x ∈ map-sub → ∥ Σ[ q ∈ K ] q ∈ a .upper × (f-map q <' x) ∥₁
      >sup-helper x ¬∈sub = do
        (q , q∈a , ¬sup<fq) ← ¬∀→∃¬2 (λ _ _ → isProp<') (¬map (Inhab→∈ map-prop) ¬∈sub)
        (r , r<q , r∈upper) ← a .upper-round q q∈a
        return (r , r∈upper , <≤-trans' (homPres< r q r<q) (¬<→≥' ¬sup<fq))

      >map-helper : (x : K') → x >' map-helper → ∥ Σ[ q ∈ K ] q ∈ a .upper × (f-map q <' x) ∥₁
      >map-helper x x>sup = >sup-helper x (>sup→¬∈ x map-sup x>sup)


      private
        ∈-helper :  ¬ map-helper ∈ map-sub → ⊥
        ∈-helper ¬∈sub =
          proof _ , isProp⊥ by do
          (q , q∈a , sup>fq) ← >sup-helper _ ¬∈sub
          (x , fq<x , x∈sub) ← <sup→∃∈ _ map-sup sup>fq
          return (<'-asym fq<x (∈→Inhab map-prop x∈sub q q∈a))

      map∈sub : map-helper ∈ map-sub
      map∈sub with decide (isProp∈ map-sub)
      ... | yes ∈sub = ∈sub
      ... | no ¬∈sub = Empty.rec (∈-helper ¬∈sub)

      map-helper< : (q : K) → q ∈ a .upper → map-helper <' f-map q
      map-helper< = ∈→Inhab map-prop map∈sub


    module _ (q : K) where

      comp-helper : (x : K') → x ∈ map-sub (K→𝕂 q) → x ≤' f-map q
      comp-helper x x∈sub with <≤-total' (f-map q) x
      ... | inr x≤fq = x≤fq
      ... | inl x>fq = Empty.rec (
        proof _ , isProp⊥ by do
        (r , fq<fr , fr<x) ← findBetween x>fq
        return (<'-asym fr<x (∈→Inhab (map-prop (K→𝕂 q)) x∈sub r (Inhab→∈ (q <P_) (homRefl< _ _ fq<fr)))))

      comp-helper' : (x : K') → x ≤' f-map q → x ∈ map-sub (K→𝕂 q)
      comp-helper' x x≤fq =
        Inhab→∈ (map-prop (K→𝕂 q)) (λ r r∈q → ≤<-trans' x≤fq (homPres< q r (∈→Inhab (q <P_) r∈q)))

      comp-prop : K' → hProp _
      comp-prop x = (x ≤' f-map q) , isProp≤'

      comp-sub : ℙ K'
      comp-sub = specify comp-prop

      comp-path : comp-sub ≡ map-sub (K→𝕂 q)
      comp-path = bi⊆→≡ ⊆helper ⊇helper
        where
        ⊆helper : comp-sub ⊆ map-sub (K→𝕂 q)
        ⊆helper x∈comp = comp-helper' _ (∈→Inhab comp-prop x∈comp)

        ⊇helper : map-sub (K→𝕂 q) ⊆ comp-sub
        ⊇helper x∈sub = Inhab→∈ comp-prop (comp-helper _ x∈sub)

      compSup : Supremum comp-sub
      compSup .sup = f-map q
      compSup .bound r r∈comp = ∈→Inhab comp-prop r∈comp
      compSup .least b b≥r∈comp = b≥r∈comp _ fq∈comp
        where
        fq∈comp : f-map q ∈ comp-sub
        fq∈comp = Inhab→∈ comp-prop (≤-refl' refl)

      map-comp : map-helper (K→𝕂 q) ≡ f-map q
      map-comp i =
        isProp→PathP (λ i → isPropSupremum (comp-path i)) compSup (map-sup (K→𝕂 q)) (~ i) .sup


    module _ (a : 𝕂)(b : 𝕂) where

      map-sub-⊆ : a ≥𝕂 b → map-sub b ⊆ map-sub a
      map-sub-⊆ a≥b {x = x} x∈subb =
        Inhab→∈ (map-prop a) (λ r r∈a → ∈→Inhab (map-prop b) x∈subb _ (lower a≥b r∈a))

      map-helper-pres≥ : a ≥𝕂 b → map-helper a ≥' map-helper b
      map-helper-pres≥ a≥b = ⊆→sup≤ (map-sub-⊆ a≥b) (map-sup b) (map-sup a)

      map-helper-pres> : a >𝕂 b → map-helper a >' map-helper b
      map-helper-pres> a>b with <≤-total' (map-helper b) (map-helper a)
      ... | inl fb<fa = fb<fa
      ... | inr fa≤fb = Empty.rec (
        proof _ , isProp⊥ by do
        (q , q<r∈a , q∈b)  ← a>b
        let fq∈suba : f-map q ∈ map-sub a
            fq∈suba = Inhab→∈ (map-prop a) (λ r r∈a → homPres< _ _ (q<r∈a r r∈a))
            fa≥fq : map-helper a ≥' f-map q
            fa≥fq = map-sup a .bound _ fq∈suba
            fq>fb : f-map q >' map-helper b
            fq>fb = map-helper< b _ q∈b
            fb<fa : map-helper b <' map-helper a
            fb<fa = <≤-trans' fq>fb fa≥fq
        return (<≤-asym' fb<fa fa≤fb))


    module _ (a b : 𝕂) where

      fa+fb≤ : (q : K) → q ∈ (a +𝕂 b) .upper → map-helper a +' map-helper b <' f-map q
      fa+fb≤ q q∈a+b =
        proof _ , isProp<' by do
        (s , t , s∈a , t∈b , q≡s+t) ← ∈→Inhab (+upper a b) q∈a+b
        return (subst (map-helper a +' map-helper b <'_)
          (sym (pres+ s t) ∙ (λ i → f-map (q≡s+t (~ i))))
          (+-Pres<' (map-helper< a s s∈a) (map-helper< b t t∈b)))

      fa+fb≤fa+b : map-helper a +' map-helper b ≤' map-helper (a +𝕂 b)
      fa+fb≤fa+b = map-sup (a +𝕂 b) .bound _ (Inhab→∈ (map-prop (a +𝕂 b)) fa+fb≤)

      ¬fa+fb<fa+b : ¬ map-helper a +' map-helper b <' map-helper (a +𝕂 b)
      ¬fa+fb<fa+b fa+fb<fa+b =
        proof _ , isProp⊥ by do
        let (s , t , fa<s , fb<t , fa+b≡s+t) =
              <-+-Decompose' (map-helper a) (map-helper b) _ fa+fb<fa+b
        (p , p∈a , fp<s) ← >map-helper a s fa<s
        (q , q∈b , fq<t) ← >map-helper b t fb<t
        let fp+q<fa+b : f-map (p + q) <' map-helper (a +𝕂 b)
            fp+q<fa+b = transport (λ i → pres+ p q (~ i) <' fa+b≡s+t (~ i)) (+-Pres<' fp<s fq<t)
            p+q∈a+b : (p + q) ∈ (a +𝕂 b) .upper
            p+q∈a+b = Inhab→∈ (+upper a b) ∣ p , q , p∈a , q∈b , refl ∣₁
        return (<'-asym fp+q<fa+b (map-helper< (a +𝕂 b) _ p+q∈a+b))

      map-pres+ : map-helper (a +𝕂 b) ≡ map-helper a +' map-helper b
      map-pres+ = case-split (trichotomy' _ _)
        where
        case-split : Trichotomy (𝒦' .fst .fst .fst) _ _ → _
        case-split (lt fa+b<fa+fb) = Empty.rec (<≤-asym' fa+b<fa+fb fa+fb≤fa+b)
        case-split (eq fa+b≡fa+fb) = fa+b≡fa+fb
        case-split (gt fa+b>fa+fb) = Empty.rec (¬fa+fb<fa+b fa+b>fa+fb)


    map-pres0 : map-helper 𝟘 ≡ 0r'
    map-pres0 = map-comp 0r ∙ pres0

    map-pres1 : map-helper 𝟙 ≡ 1r'
    map-pres1 = map-comp 1r ∙ pres1

    map-pres- : (a : 𝕂) → map-helper (-𝕂 a) ≡ -' map-helper a
    map-pres- a = sym (+IdL' _)
      ∙ (λ i → +InvL' (map-helper a) (~ i) +' map-helper (-𝕂 a))
      ∙ sym (+Assoc' _ _ _) ∙ (λ i → (-' map-helper a) +' fa+f-a≡0 i) ∙ +IdR' _
      where
      fa+f-a≡0 : map-helper a +' map-helper (-𝕂 a) ≡ 0r'
      fa+f-a≡0 = sym (map-pres+ a (-𝕂 a)) ∙ (λ i → map-helper (+𝕂InvR a i)) ∙ map-pres0


    map-helper-pres≥0 : (a : 𝕂) → a ≥𝕂 𝟘 → map-helper a ≥' 0r'
    map-helper-pres≥0 a a≥0 = subst (map-helper a ≥'_) map-pres0 (map-helper-pres≥ a 𝟘 a≥0)

    map-helper-pres>0 : (a : 𝕂) → a >𝕂 𝟘 → map-helper a >' 0r'
    map-helper-pres>0 a a>0 = subst (map-helper a >'_) map-pres0 (map-helper-pres> a 𝟘 a>0)

    map-pres>0 : (a : 𝕂) → a >𝕂 𝟘 → LinearlyOrderedCommRingStr._>0 (𝒦' .fst .fst) (map-helper a)
    map-pres>0 a a>0 = map-helper-pres>0 a a>0


    module _ (a b : 𝕂)(a>0 : a >𝕂 𝟘)(b>0 : b >𝕂 𝟘) where

      private
        a≥0 = <𝕂→≤𝕂 {a = 𝟘} {b = a} a>0
        b≥0 = <𝕂→≤𝕂 {a = 𝟘} {b = b} b>0
        a₊ b₊ : 𝕂₊
        a₊ = a , a≥0
        b₊ = b , b≥0

      fa·fb≤ : (q : K) → q ∈ (a₊ ·𝕂₊ b₊) .fst .upper → map-helper a ·' map-helper b <' f-map q
      fa·fb≤ q q∈a·b =
        proof _ , isProp<' by do
        (s , t , s∈a , t∈b , q≡s·t) ← ∈→Inhab (·upper₊ a₊ b₊) q∈a·b
        return (
          subst (map-helper a ·' map-helper b <'_)
            (sym (pres· s t) ∙ (λ i → f-map (q≡s·t (~ i))))
            (·-PosPres≥0>0' (map-helper-pres≥0 a a≥0) (map-helper-pres≥0 b b≥0)
              (homPres>0 _ (≥𝕂0+q∈upper→q>0 a a≥0 s∈a)) (homPres>0 _ (≥𝕂0+q∈upper→q>0 b b≥0 t∈b))
              (map-helper< a s s∈a) (map-helper< b t t∈b)))

      fa·fb≤fa·b : map-helper a ·' map-helper b ≤' map-helper ((a₊ ·𝕂₊ b₊) .fst)
      fa·fb≤fa·b = map-sup ((a₊ ·𝕂₊ b₊) .fst) .bound _ (Inhab→∈ (map-prop ((a₊ ·𝕂₊ b₊) .fst)) fa·fb≤)

      ¬fa·fb<fa·b : ¬ map-helper a ·' map-helper b <' map-helper ((a₊ ·𝕂₊ b₊) .fst)
      ¬fa·fb<fa·b fa·fb<fa·b =
        proof _ , isProp⊥ by do
        let (s , t , fa<s , fb<t , fa·b≡s·t) =
              <-·-Decompose' (map-helper a) (map-helper b) _
              (map-helper-pres>0 a a>0) (map-helper-pres>0 b b>0) fa·fb<fa·b
        (p , p∈a , fp<s) ← >map-helper a s fa<s
        (q , q∈b , fq<t) ← >map-helper b t fb<t
        let fp·q<fa·b : f-map (p · q) <' map-helper ((a₊ ·𝕂₊ b₊) .fst)
            fp·q<fa·b =
              transport (λ i → pres· p q (~ i) <' fa·b≡s·t (~ i))
              (·-PosPres>' (homPres>0 _ (≥𝕂0+q∈upper→q>0 a a≥0 p∈a))
                (homPres>0 _ (≥𝕂0+q∈upper→q>0 b b≥0 q∈b)) fp<s fq<t)
            p·q∈a·b : (p · q) ∈ (a₊ ·𝕂₊ b₊) .fst .upper
            p·q∈a·b = Inhab→∈ (·upper₊ a₊ b₊) ∣ p , q , p∈a , q∈b , refl ∣₁
        return (<'-asym fp·q<fa·b (map-helper<  ((a₊ ·𝕂₊ b₊) .fst) _ p·q∈a·b))

      map-pres·PosPos' : map-helper ((a₊ ·𝕂₊ b₊) .fst) ≡ map-helper a ·' map-helper b
      map-pres·PosPos' = case-split (trichotomy' _ _)
        where
        case-split : Trichotomy (𝒦' .fst .fst .fst) _ _ → _
        case-split (lt fa·b<fa·fb) = Empty.rec (<≤-asym' fa·b<fa·fb fa·fb≤fa·b)
        case-split (eq fa·b≡fa·fb) = fa·b≡fa·fb
        case-split (gt fa·b>fa·fb) = Empty.rec (¬fa·fb<fa·b fa·b>fa·fb)

      map-pres·PosPos : map-helper (a ·𝕂 b) ≡ map-helper a ·' map-helper b
      map-pres·PosPos = (λ i → map-helper (·𝕂≡·𝕂₊ a₊ b₊ i)) ∙ map-pres·PosPos'


    open Helpers 𝕂CommRing renaming (helper1 to helper𝕂1 ; helper2 to helper𝕂2)
    open Helpers (LinearlyOrderedCommRing→CommRing (𝒦' .fst .fst))

    map-pres·Pos : (a b : 𝕂) → a >𝕂 𝟘 → map-helper (a ·𝕂 b) ≡ map-helper a ·' map-helper b
    map-pres·Pos a b a>0 = case-split (trichotomy𝕂 b 𝟘)
      where
      case-split : Trichotomy𝕂 b 𝟘 → _
      case-split (gt b>0) = map-pres·PosPos a b a>0 b>0
      case-split (eq b≡0) = (λ i → map-helper (a ·𝕂 b≡0 i))
        ∙ (λ i → map-helper (·𝕂ZeroR a i))
        ∙ map-pres0 ∙ sym (0RightAnnihilates' _)
        ∙ (λ i → map-helper a ·' map-pres0 (~ i))
        ∙ (λ i → map-helper a ·' map-helper (b≡0 (~ i)))
      case-split (lt b<0) = (λ i → map-helper (a ·𝕂 -𝕂Involutive b (~ i)))
        ∙ (λ i → map-helper (helper𝕂1 a (-𝕂 b) i))
        ∙ map-pres- (a ·𝕂 (-𝕂 b))
        ∙ (λ i → -' map-pres·PosPos a (-𝕂 b) a>0 (-reverse<0 b b<0) i)
        ∙ sym (helper1 _ _)
        ∙ (λ i → map-helper a ·' map-pres- (-𝕂 b) (~ i))
        ∙ (λ i → map-helper a ·' map-helper (-𝕂Involutive b i))

    map-pres· : (a b : 𝕂) → map-helper (a ·𝕂 b) ≡ map-helper a ·' map-helper b
    map-pres· a b = case-split (trichotomy𝕂 a 𝟘)
      where
      case-split : Trichotomy𝕂 a 𝟘 → _
      case-split (gt a>0) = map-pres·Pos a b a>0
      case-split (eq a≡0) = (λ i → map-helper (a≡0 i ·𝕂 b))
        ∙ (λ i → map-helper (·𝕂ZeroL b i))
        ∙ map-pres0 ∙ sym (0LeftAnnihilates' _)
        ∙ (λ i → map-pres0 (~ i) ·' map-helper b)
        ∙ (λ i → map-helper (a≡0 (~ i)) ·' map-helper b)
      case-split (lt a<0) = (λ i → map-helper (-𝕂Involutive a (~ i) ·𝕂 b))
        ∙ (λ i → map-helper (helper𝕂2 (-𝕂 a) b i))
        ∙ map-pres- ((-𝕂 a) ·𝕂 b)
        ∙ (λ i → -' map-pres·Pos (-𝕂 a) b (-reverse<0 a a<0) i)
        ∙ sym (helper2 _ _)
        ∙ (λ i → map-pres- (-𝕂 a) (~ i) ·' map-helper b)
        ∙ (λ i → map-helper (-𝕂Involutive a i) ·' map-helper b)


    {-

      The Ordered Field Homomorphism Given by Universal Property

    -}

    extendedRingHom : CommRingHom 𝕂CommRing (LinearlyOrderedCommRing→CommRing (𝒦' .fst .fst))
    extendedRingHom = map-helper , makeIsCommRingHom map-pres1 map-pres+ map-pres·

    open OrderedCommRingHom

    map-pres-- : (a b : 𝕂) → map-helper ((𝕂LO.Ord._-_) b a) ≡ map-helper b -' map-helper a
    map-pres-- a b =
      map-pres+ b (-𝕂 a)
      ∙ (λ i → map-helper b +' map-pres- a i)

    map-pres< : (a b : 𝕂) → 𝕂LO._<_ a b → map-helper a <' map-helper b
    map-pres< a b a<b =
      Diff>0→<' (subst (_>0'_) (map-pres-- a b)
        (map-pres>0 ((𝕂LO.Ord._-_) b a) (𝕂LO.<→Diff>0 a<b)))

    map-pres≤ : (a b : 𝕂) → 𝕂LO._≤_ a b → map-helper a ≤' map-helper b
    map-pres≤ a b a≤b =
      invEq (≤'≃¬> (map-helper a) (map-helper b)) (notGreater (𝕂LO.trichotomy a b))
      where
      notGreater : Trichotomy (𝕂LinearlyOrderedCommRing .fst) a b → ¬ map-helper b <' map-helper a
      notGreater (lt a<b) fb<fa = <'-asym (map-pres< a b a<b) fb<fa
      notGreater (eq a≡b) fb<fa = <'-arefl fb<fa (cong map-helper (sym a≡b))
      notGreater (gt b<a) _ = equivFun (𝕂LO.≤≃¬> a b) a≤b b<a

    extendedOrderedCommRingHom : OrderedCommRingHom (𝕂LinearlyOrderedCommRing .fst) (𝒦' .fst .fst .fst)
    extendedOrderedCommRingHom .ring-hom = extendedRingHom
    extendedOrderedCommRingHom .pres<    = map-pres<
    extendedOrderedCommRingHom .pres≤    = map-pres≤

    extendedLinearlyOrderedFieldHom : LinearlyOrderedFieldHom 𝕂LinearlyOrderedField (𝒦' .fst)
    extendedLinearlyOrderedFieldHom = extendedOrderedCommRingHom

    extendedOrderedFieldHom :
      OrderedFieldHom
        𝕂OrderedField
        (LinearlyOrderedField→OrderedField (𝒦' .fst))
    extendedOrderedFieldHom = extendedOrderedCommRingHom
