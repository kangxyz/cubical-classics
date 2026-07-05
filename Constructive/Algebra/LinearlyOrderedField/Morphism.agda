{-

Morphisms between linearly ordered fields

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Algebra.LinearlyOrderedField.Morphism where

open import Cubical.Foundations.Prelude hiding (lower)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SetQuot
open import Cubical.Relation.Nullary
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Algebra.OrderedCommRing.Morphism
import Constructive.Algebra.OrderedField.Morphism as OrderedFieldMorphism
open import Constructive.Algebra.OrderedField.Morphism public
  using (OrderedFieldHom)
open import Constructive.Algebra.LinearlyOrderedCommRing
import Constructive.Algebra.LinearlyOrderedCommRing.Morphism as LinearMorphism
open import Constructive.Algebra.LinearlyOrderedCommRing.Univalence
open import Constructive.Algebra.LinearlyOrderedCommRing.Archimedes
open import Constructive.Algebra.LinearlyOrderedField

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level
    𝒦  : LinearlyOrderedField ℓ   ℓ'
    𝒦' : LinearlyOrderedField ℓ'' ℓ'''

private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (p q : 𝓡 .fst) → p + (q - p) ≡ q
    helper1 _ _ = solve! 𝓡

    helper2 : (p ε x : 𝓡 .fst) → (p + (x + ε)) - (p + x) ≡ ε
    helper2 _ _ _ = solve! 𝓡

    helper3 : (x y a : 𝓡 .fst) → ((x - y) + a) - x ≡ a - y
    helper3 _ _ _ = solve! 𝓡

    helper4 : (x a b : 𝓡 .fst) → ((b - a) + a) - x ≡ b - x
    helper4 _ _ _ = solve! 𝓡


-- Linearly ordered-field homomorphisms are homomorphisms of the underlying Cubical
-- ordered commutative rings.

LinearlyOrderedFieldHom : (𝒦 : LinearlyOrderedField ℓ ℓ')(𝒦' : LinearlyOrderedField ℓ'' ℓ''') → Type _
LinearlyOrderedFieldHom 𝒦 𝒦' = OrderedCommRingHom (𝒦 .fst .fst) (𝒦' .fst .fst)


{-

  SIP for Linearly Ordered Fields

-}

-- Equivalence of linearly ordered fields

isLinearlyOrderedFieldEquiv : LinearlyOrderedFieldHom 𝒦 𝒦' → Type _
isLinearlyOrderedFieldEquiv {𝒦 = 𝒦} {𝒦' = 𝒦'} =
  isLinearlyOrderedCommRingEquiv {𝓡 = 𝒦 .fst} {𝓡' = 𝒦' .fst}


uaLinearlyOrderedField : {𝒦 𝒦' : LinearlyOrderedField ℓ ℓ'}
  {f : LinearlyOrderedFieldHom 𝒦 𝒦'} → isLinearlyOrderedFieldEquiv {𝒦 = 𝒦} {𝒦' = 𝒦'} f → 𝒦 ≡ 𝒦'
uaLinearlyOrderedField {𝒦 = 𝒦} {𝒦' = 𝒦'} {f = f} is-equiv i .fst =
  uaLinearlyOrderedCommRing {𝓡 = 𝒦 .fst} {𝓡' = 𝒦' .fst} {f = f} is-equiv i
uaLinearlyOrderedField {𝒦 = 𝒦} {𝒦' = 𝒦'} is-equiv i .snd =
  liftPathIsFieldOnLinearlyOrderedCommRing (λ i → uaLinearlyOrderedField is-equiv i .fst) (𝒦 .snd) (𝒦' .snd) i


{-

  Properties of linearly ordered field homomorphisms

-}

module LinearlyOrderedFieldHomStr (f : LinearlyOrderedFieldHom 𝒦' 𝒦) where

  open LinearlyOrderedFieldStr 𝒦
  open LinearlyOrderedFieldStr 𝒦' using ()
    renaming ( 0r to 0r' ; 1r to 1r'
             ; -_ to -'_ ; _+_ to _+'_
             ; 1>0 to 1>'0
             ; inv₊ to inv'₊ ; ·-lInv₊ to ·'-lInv₊
             ; _<_ to _<'_ ; _≤_ to _≤'_
             ; _>_ to _>'_ ; _≥_ to _≥'_
             ; _⋆_ to _⋆'_
             ; p>0→p⁻¹>0 to p>'0→p⁻¹>'0)
  open OrderedCommRingHom           f
  open LinearMorphism.OrderedCommRingHomProperties {𝓡 = 𝒦' .fst} {𝓡' = 𝒦 .fst} f
  open IsCommRingHom (ring-hom .snd)

  private
    K  = 𝒦  .fst .fst .fst
    K' = 𝒦' .fst .fst .fst
    f-map = ring-hom .fst


  {-

    Homomorphism preserves multiplicative inverse

  -}


  homPresInv : {x : K'} → (x>0 : x >' 0r') → f-map (inv'₊ x>0) ≡ inv₊ (homPres>0 _ x>0)
  homPresInv {x = x} x>0 = sym (·IdR _)
    ∙ (λ i → f-map (inv'₊ x>0) · ·-rInv₊ (homPres>0 _ x>0) (~ i))
    ∙ ·Assoc _ _ _
    ∙ (λ i → fx⁻¹fx≡1 i · inv₊ (homPres>0 _ x>0))
    ∙ ·IdL _
    where
    fx⁻¹fx≡1 : f-map (inv'₊ x>0) · f-map x ≡ 1r
    fx⁻¹fx≡1 = sym (pres· _ _) ∙ (λ i → f-map (·'-lInv₊ x>0 i)) ∙ pres1


  {-

    Image of an ordered field homomorphism

  -}

  isUnboundedΣ : Type _
  isUnboundedΣ = (x : K) → Σ[ r ∈ K' ] x < f-map r

  isDenseΣ : Type _
  isDenseΣ = {x y : K} → x < y → Σ[ r ∈ K' ] (x < f-map r) × (f-map r < y)


  isUnbounded : Type _
  isUnbounded = (x : K) → ∥ Σ[ r ∈ K' ] x < f-map r ∥₁

  isDense : Type _
  isDense = {x y : K} → x < y → ∥ Σ[ r ∈ K' ] (x < f-map r) × (f-map r < y) ∥₁


  isArchimedean→isUnboundedΣ : isArchimedean (𝒦 .fst) → isUnboundedΣ
  isArchimedean→isUnboundedΣ archimedes x =
    (helper .fst) ⋆' 1r' , subst (_> x) (sym (homPres⋆ _ _)) (helper .snd)
    where
    helper : _
    helper = archimedes x (f-map 1r') (homPres>0 _ 1>'0)


  isArchimedean→isUnbounded : isArchimedean (𝒦 .fst) → isUnbounded
  isArchimedean→isUnbounded archimedes x = ∣ isArchimedean→isUnboundedΣ archimedes x ∣₁


  -- Unboundedness in the other direction, equivalent by using additive inverses.

  isLowerUnbounded : Type _
  isLowerUnbounded = (x : K) → ∥ Σ[ r ∈ K' ] f-map r < x ∥₁

  isUnbounded→isLowerUnbounded : isUnbounded → isLowerUnbounded
  isUnbounded→isLowerUnbounded exceed x = do
    (r , fr>-x) ← exceed (- x)
    return (-' r ,
      transport (λ i → pres- r (~ i) < -Idempotent x i) (-Reverse< fr>-x))

  isLowerUnbounded→isUnbounded : isLowerUnbounded → isUnbounded
  isLowerUnbounded→isUnbounded -exceed x = do
    (r , fr<-x) ← -exceed (- x)
    return (-' r ,
      transport (λ i → pres- r (~ i) > -Idempotent x i) (-Reverse< fr<-x))


  isLowerUnboundedΣ : Type _
  isLowerUnboundedΣ = (x : K) → Σ[ r ∈ K' ] f-map r < x

  isUnboundedΣ→isLowerUnboundedΣ : isUnboundedΣ → isLowerUnboundedΣ
  isUnboundedΣ→isLowerUnboundedΣ exceed x =
    let (r , fr>-x) = exceed (- x) in
    -' r , transport (λ i → pres- r (~ i) < -Idempotent x i) (-Reverse< fr>-x)


  -- Another version using smallness.

  isArbitrarilySmall : Type _
  isArbitrarilySmall = (x : K) → x > 0r → ∥ Σ[ r ∈ K' ] (0r < f-map r) × (f-map r < x) ∥₁

  isUnbounded→isArbitrarilySmall : isUnbounded → isArbitrarilySmall
  isUnbounded→isArbitrarilySmall exceed x x>0 = do
    (r , fr>x⁻¹) ← exceed (inv₊ x>0)
    let x⁻¹>0 : inv₊ x>0 > 0r
        x⁻¹>0 = p>0→p⁻¹>0 x>0
        r>0 : r >' 0r'
        r>0 = homRefl>0 _ (<-trans x⁻¹>0 fr>x⁻¹)
        fr>0 : f-map r > 0r
        fr>0 = homPres>0 _ r>0
        fr⁻¹<x⁻¹⁻¹ = inv-Reverse< fr>0 x⁻¹>0 fr>x⁻¹
    return (_ , homPres>0 _ (p>'0→p⁻¹>'0 r>0) ,
      transport (λ i → homPresInv r>0 (~ i) < inv₊Idem x>0 i) fr⁻¹<x⁻¹⁻¹)


  isArbitrarilySmallΣ : Type _
  isArbitrarilySmallΣ = (x : K) → x > 0r → Σ[ r ∈ K' ] (0r < f-map r) × (f-map r < x)

  isUnboundedΣ→isArbitrarilySmallΣ : isUnboundedΣ → isArbitrarilySmallΣ
  isUnboundedΣ→isArbitrarilySmallΣ exceed x x>0 =
    let (r , fr>x⁻¹) = exceed (inv₊ x>0)
        x⁻¹>0 : inv₊ x>0 > 0r
        x⁻¹>0 = p>0→p⁻¹>0 x>0
        r>0 : r >' 0r'
        r>0 = homRefl>0 _ (<-trans x⁻¹>0 fr>x⁻¹)
        fr>0 : f-map r > 0r
        fr>0 = homPres>0 _ r>0
        fr⁻¹<x⁻¹⁻¹ = inv-Reverse< fr>0 x⁻¹>0 fr>x⁻¹
    in  _ , homPres>0 _ (p>'0→p⁻¹>'0 r>0) ,
        transport (λ i → homPresInv r>0 (~ i) < inv₊Idem x>0 i) fr⁻¹<x⁻¹⁻¹


  private

    module _
      (archimedes : isArchimedean (𝒦 .fst))
      (a b : K)(ε : K')
      (fε>0 : f-map ε > 0r)(fε<δ : f-map ε < b - a)
      (lower : K')(lower<a : f-map lower < a) where

      open import Constructive.Preliminary.Nat

      step : ℕ → K
      step n = f-map lower + n ⋆ f-map ε

      P : ℕ → Type _
      P n = step n > a

      isPropP : (n : ℕ) → isProp (P n)
      isPropP _ = isProp<

      decP : (n : ℕ) → Dec (P n)
      decP n = dec< _ _

      ¬P0 : ¬ P zero
      ¬P0 = <-asym lower+0·ε<a
        where
        lower+0·ε<a : step 0 < a
        lower+0·ε<a = subst (_< a) (sym (+IdR (f-map lower))
          ∙ (λ i → f-map lower + 0⋆q≡0 (f-map ε) (~ i))) lower<a

      open Helpers (LinearlyOrderedCommRing→CommRing (𝒦 .fst))

      ∃Pn : ∥ Σ[ n ∈ ℕ ] P n ∥₁
      ∃Pn =
        let (n , n·ε>a-lower) =
              archimedes (a - f-map lower) (f-map ε) fε>0
            lower+n·ε>a : step n > a
            lower+n·ε>a = subst (step n >_)
              (helper1 (f-map lower) a) (+-lPres< n·ε>a-lower)
        in  ∣ n , lower+n·ε>a ∣₁

      interval : Σ[ n ∈ ℕ ] (¬ P n) × P (suc n)
      interval = findInterval decP ¬P0 ∃Pn

      n₀ = interval .fst

      lower+sucn⋆ε>a : step (suc n₀) > a
      lower+sucn⋆ε>a = interval .snd .snd

      diff-path : (p ε : K)(n : ℕ) → (p + (suc n) ⋆ ε) - (p + n ⋆ ε) ≡ ε
      diff-path p ε n = (λ i → (p + sucn⋆q≡n⋆q+q n ε i) - (p + n ⋆ ε)) ∙ helper2 _ _ _

      b-sucn>a-n : b - step (suc n₀) > a - step n₀
      b-sucn>a-n = transport (λ i → helper3 (step (suc n₀)) (step n₀) a i < helper4 (step (suc n₀)) a b i) -<-
        where
        diff>b-a : step (suc n₀) - step n₀ < b - a
        diff>b-a = subst (_< b - a) (sym (diff-path _ _ _)) fε<δ
        -<- : ((step (suc n₀) - step n₀) + a) - step (suc n₀) < ((b - a) + a) - step (suc n₀)
        -<- = +-rPres< (+-rPres< diff>b-a)

      a-n≥0→b>sucn : a ≥ step n₀ → b > step (suc n₀)
      a-n≥0→b>sucn -≥- = Diff>0→> (≤<-trans (≥→Diff≥0 -≥-) b-sucn>a-n)

      b>sucn : b > step (suc n₀)
      b>sucn = case-split (trichotomy a (step n₀))
        where
        case-split : Trichotomy (𝒦 .fst .fst) a (step n₀) → b > step (suc n₀)
        case-split (lt a<n) = Empty.rec (interval .snd .fst a<n)
        case-split (eq a≡n) = a-n≥0→b>sucn (≤-refl (sym a≡n))
        case-split (gt a>n) = a-n≥0→b>sucn (<-≤-weaken a>n)

      in-the-image : (n : ℕ) → step n ≡ f-map (lower +' n ⋆' ε)
      in-the-image n = (λ i → f-map lower + homPres⋆ n ε (~ i)) ∙ sym (pres+ _ _)

      among-them : Σ[ r ∈ K' ] (a < f-map r) × (f-map r < b)
      among-them = lower +' (suc n₀) ⋆' ε ,
        subst (_> a) (in-the-image (suc n₀)) (interval .snd .snd) ,
        subst (_< b) (in-the-image (suc n₀)) b>sucn


  isArchimedean→isDenseΣ : isArchimedean (𝒦 .fst) → isDenseΣ
  isArchimedean→isDenseΣ archimedes {x = x} {y = y} x<y =
    let (lower , lower<a) =
          isUnboundedΣ→isLowerUnboundedΣ (isArchimedean→isUnboundedΣ archimedes) x
        (ε , fε>0 , fε<δ) =
          isUnboundedΣ→isArbitrarilySmallΣ (isArchimedean→isUnboundedΣ archimedes) (y - x) (>→Diff>0 x<y)
    in among-them archimedes x y ε fε>0 fε<δ lower lower<a

  isArchimedean→isDense : isArchimedean (𝒦 .fst) → isDense
  isArchimedean→isDense archimedes x<y = ∣ isArchimedean→isDenseΣ archimedes x<y ∣₁

{-

  The Canonical Map from ℚ

-}

module InclusionFromℚ (𝒦 : LinearlyOrderedField ℓ ℓ') where

  open import Cubical.Data.NatPlusOne
  open import Cubical.Data.Int
    using    (ℤ ; pos)
  import Cubical.Data.Int as Int
  open import Cubical.Data.Rationals
    using    (ℚ)

  open import Constructive.Algebra.LinearlyOrderedCommRing.Instances.Int
    using    (ℤLinearlyOrderedCommRing)

  open import Constructive.Algebra.LinearlyOrderedField.Instances.Rationals

  open LinearlyOrderedFieldStr 𝒦
  open LinearMorphism.InclusionFromℤ (𝒦 .fst)
  open LinearlyOrderedCommRingStr  ℤLinearlyOrderedCommRing using () renaming (_>_ to _>ℤ_)
  module ℚLO = LinearlyOrderedCommRingStr (ℚLinearlyOrderedField .fst)
  open OrderedFieldMorphism.InclusionFromℚ (LinearlyOrderedField→OrderedField 𝒦) public


  private

    module _ ((a , b) : ℤ × ℕ₊₁) where

      >0-helper' : a >ℤ 0 → ℤ→R a · inv (ℕ₊₁→R≢0 b) > 0r
      >0-helper' a>0 = ·-Pres>0 (ℤ→R-Pres>0 _ a>0) (p>0→p⁻¹>0 (ℕ₊₁→R>0 b))

      >0-helper : ℚLO._>0 [ a , b ] → ℚ→K [ a , b ] >0
      >0-helper a/b>0 =
        >0-helper' (subst (_>ℤ pos 0) (Int.·IdR a) a/b>0)

  ℚ→K-Pres>0 : (p : ℚ) → ℚLO._>0 p → ℚ→K p >0
  ℚ→K-Pres>0 = elimProp (λ _ → isPropΠ (λ _ → isProp>0 _)) >0-helper


  {-

    (Ordered) Ring Homomorphism Instance

  -}

  ℚ→K-Pres< : (p q : ℚ) → ℚLO._<_ p q → ℚ→K p < ℚ→K q
  ℚ→K-Pres< p q p<q =
    Diff>0→< (subst (_>0) (ℚ→K-Pres-- p q)
      (ℚ→K-Pres>0 ((ℚLO.Ord._-_) q p) (ℚLO.<→Diff>0 p<q)))

  ℚ→K-Pres≤ : (p q : ℚ) → ℚLO._≤_ p q → ℚ→K p ≤ ℚ→K q
  ℚ→K-Pres≤ p q p≤q =
    invEq (≤≃¬> (ℚ→K p) (ℚ→K q)) (notGreater (ℚLO.trichotomy p q))
    where
    notGreater : Trichotomy (ℚLinearlyOrderedField .fst .fst) p q → ¬ ℚ→K q < ℚ→K p
    notGreater (lt p<q) fq<fp = <-asym (ℚ→K-Pres< p q p<q) fq<fp
    notGreater (eq p≡q) fq<fp = <-arefl fq<fp (cong ℚ→K (sym p≡q))
    notGreater (gt q<p) _ = equivFun (ℚLO.≤≃¬> p q) p≤q q<p

  open OrderedCommRingHom

  ℚ→KOrderedCommRingHom : OrderedCommRingHom (ℚLinearlyOrderedField .fst .fst) (𝒦 .fst .fst)
  ℚ→KOrderedCommRingHom .ring-hom = ℚ→KCommRingHom
  ℚ→KOrderedCommRingHom .pres<    = ℚ→K-Pres<
  ℚ→KOrderedCommRingHom .pres≤    = ℚ→K-Pres≤

  ℚ→KLinearlyOrderedFieldHom : LinearlyOrderedFieldHom ℚLinearlyOrderedField 𝒦
  ℚ→KLinearlyOrderedFieldHom = ℚ→KOrderedCommRingHom

  ℚ→KOrderedFieldHom : OrderedFieldHom ℚOrderedField (LinearlyOrderedField→OrderedField 𝒦)
  ℚ→KOrderedFieldHom = ℚ→KOrderedCommRingHom
