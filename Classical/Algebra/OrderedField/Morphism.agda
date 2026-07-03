{-

Morphism between Ordered Field

-}
{-# OPTIONS --safe --lossy-unification #-}
module Classical.Algebra.OrderedField.Morphism where

open import Cubical.Foundations.Prelude hiding (lower)
open import Cubical.Foundations.HLevels

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

open import Classical.Algebra.StrictlyOrderedCommRing
open import Classical.Algebra.StrictlyOrderedCommRing.Morphism
open import Classical.Algebra.StrictlyOrderedCommRing.Univalence
open import Classical.Algebra.StrictlyOrderedCommRing.Archimedes
open import Classical.Algebra.OrderedField

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level
    𝒦  : OrderedField ℓ   ℓ'
    𝒦' : OrderedField ℓ'' ℓ'''

private
  module Helpers {ℓ : Level}(𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    helper1 : (a b c d b⁻¹ d⁻¹ : 𝓡 .fst)
      → (a · d + c · b) · (b⁻¹ · d⁻¹) ≡ (a · b⁻¹) · (d · d⁻¹) + (c · d⁻¹) · (b · b⁻¹)
    helper1 _ _ _ _ _ _ = solve! 𝓡

    helper2 : (a c b⁻¹ d⁻¹ : 𝓡 .fst) → (a · b⁻¹) · 1r + (c · d⁻¹) · 1r ≡ a · b⁻¹ + c · d⁻¹
    helper2 _ _ _ _ = solve! 𝓡

    helper3 : (a c b⁻¹ d⁻¹ : 𝓡 .fst) → (a · c) · (b⁻¹ · d⁻¹) ≡ (a · b⁻¹) · (c · d⁻¹)
    helper3 _ _ _ _ = solve! 𝓡

    helper4 : (a d b⁻¹ d⁻¹ : 𝓡 .fst) → (a · b⁻¹) · (d · d⁻¹) ≡ ((a · d) · b⁻¹) · d⁻¹
    helper4 _ _ _ _ = solve! 𝓡

    helper5 : (c b b⁻¹ d⁻¹ : 𝓡 .fst) → ((c · b) · b⁻¹) · d⁻¹ ≡ (c · d⁻¹) · (b · b⁻¹)
    helper5 _ _ _ _ = solve! 𝓡

    helper6 : (p q : 𝓡 .fst) → p + (q - p) ≡ q
    helper6 _ _ = solve! 𝓡

    helper7 : (p ε x : 𝓡 .fst) → (p + (x + ε)) - (p + x) ≡ ε
    helper7 _ _ _ = solve! 𝓡

    helper8 : (x y a : 𝓡 .fst) → ((x - y) + a) - x ≡ a - y
    helper8 _ _ _ = solve! 𝓡

    helper9 : (x a b : 𝓡 .fst) → ((b - a) + a) - x ≡ b - x
    helper9 _ _ _ = solve! 𝓡


-- The homomorphism between ordered fields is just the homomorphism between their underlying strictly ordered commutative rings.

OrderedFieldHom : (𝒦 : OrderedField ℓ ℓ')(𝒦' : OrderedField ℓ'' ℓ''') → Type _
OrderedFieldHom 𝒦 𝒦' = StrictlyOrderedCommRingHom (𝒦 .fst) (𝒦' .fst)


{-

  SIP for Ordered Field

-}

-- Equivalence of strictly ordered commutative rings

isOrderedFieldEquiv : OrderedFieldHom 𝒦 𝒦' → Type _
isOrderedFieldEquiv = isStrictlyOrderedCommRingEquiv


uaOrderedField : {𝒦 𝒦' : OrderedField ℓ ℓ'}
  {f : OrderedFieldHom 𝒦 𝒦'} → isOrderedFieldEquiv {𝒦 = 𝒦} {𝒦' = 𝒦'} f → 𝒦 ≡ 𝒦'
uaOrderedField {𝒦 = 𝒦} {𝒦' = 𝒦'} {f = f} is-equiv i .fst =
  uaStrictlyOrderedCommRing {𝓡 = 𝒦 .fst} {𝓡' = 𝒦' .fst} {f = f} is-equiv i
uaOrderedField {𝒦 = 𝒦} {𝒦' = 𝒦'} is-equiv i .snd =
  liftPathIsFieldOnStrictlyOrderedCommRing (λ i → uaOrderedField is-equiv i .fst) (𝒦 .snd) (𝒦' .snd) i


{-

  Properties of ordered field homomorphism

-}

module OrderedFieldHomStr (f : OrderedFieldHom 𝒦' 𝒦) where

  open OrderedFieldStr 𝒦
  open OrderedFieldStr 𝒦' using ()
    renaming ( 0r to 0r' ; 1r to 1r'
             ; -_ to -'_ ; _+_ to _+'_
             ; 1>0 to 1>'0
             ; inv₊ to inv'₊ ; ·-lInv₊ to ·'-lInv₊
             ; _<_ to _<'_ ; _≤_ to _≤'_
             ; _>_ to _>'_ ; _≥_ to _≥'_
             ; _⋆_ to _⋆'_
             ; p>0→p⁻¹>0 to p>'0→p⁻¹>'0)
  open StrictlyOrderedCommRingHom    f
  open StrictlyOrderedCommRingHomStr f
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


  -- Unbounded in the other direction but is equivalent by using additive inverse

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


  -- Another version but using smallness

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

      open import Classical.Preliminary.Nat

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

      open Helpers (StrictlyOrderedCommRing→CommRing (𝒦 .fst))

      ∃Pn : ∥ Σ[ n ∈ ℕ ] P n ∥₁
      ∃Pn =
        let (n , n·ε>a-lower) =
              archimedes (a - f-map lower) (f-map ε) fε>0
            lower+n·ε>a : step n > a
            lower+n·ε>a = subst (step n >_)
              (helper6 (f-map lower) a) (+-lPres< n·ε>a-lower)
        in  ∣ n , lower+n·ε>a ∣₁

      interval : Σ[ n ∈ ℕ ] (¬ P n) × P (suc n)
      interval = findInterval decP ¬P0 ∃Pn

      n₀ = interval .fst

      lower+sucn⋆ε>a : step (suc n₀) > a
      lower+sucn⋆ε>a = interval .snd .snd

      diff-path : (p ε : K)(n : ℕ) → (p + (suc n) ⋆ ε) - (p + n ⋆ ε) ≡ ε
      diff-path p ε n = (λ i → (p + sucn⋆q≡n⋆q+q n ε i) - (p + n ⋆ ε)) ∙ helper7 _ _ _

      b-sucn>a-n : b - step (suc n₀) > a - step n₀
      b-sucn>a-n = transport (λ i → helper8 (step (suc n₀)) (step n₀) a i < helper9 (step (suc n₀)) a b i) -<-
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
        case-split : Trichotomy a (step n₀) → b > step (suc n₀)
        case-split (lt a<n) = Empty.rec (interval .snd .fst a<n)
        case-split (eq a≡n) = a-n≥0→b>sucn (inr (sym a≡n))
        case-split (gt a>n) = a-n≥0→b>sucn (inl a>n)

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

module InclusionFromℚ (𝒦 : OrderedField ℓ ℓ') where

  open import Cubical.Data.NatPlusOne
  open import Cubical.Data.Int
    using    (ℤ ; pos ; pos·pos)
    renaming (_+_ to _+ℤ_ ; _·_ to _·ℤ_)
  import Cubical.Data.Int as Int
  open import Cubical.Data.Int.Order
    using    (zero-<sucPos)
  open import Cubical.Data.Rationals
    using    (ℚ ; ℕ₊₁→ℤ ; _∼_)
    renaming (_+_ to _+ℚ_ ; _·_ to _·ℚ_)

  open import Classical.Algebra.StrictlyOrderedCommRing.Instances.Int
    using    (ℤStrictlyOrderedCommRing)
  open import Classical.Algebra.StrictlyOrderedCommRing.Morphism

  open import Cubical.Algebra.CommRing.Instances.Rationals
  open import Classical.Algebra.OrderedField.Instances.Rationals

  open OrderedFieldStr 𝒦
  open InclusionFromℤ (𝒦 .fst)
  open StrictlyOrderedCommRingStr  ℤStrictlyOrderedCommRing using () renaming (_>_ to _>ℤ_ ; >0≡>0r to >0≡>0r-ℤ)
  module ℚSO = StrictlyOrderedCommRingStr (ℚOrderedField .fst)

  private
    K = 𝒦 .fst .fst .fst
    isSetK = is-set

  open Helpers (StrictlyOrderedCommRing→CommRing (𝒦 .fst))


  ℕ₊₁→ℤ>0 : (n : ℕ₊₁) → ℕ₊₁→ℤ n >ℤ pos 0
  ℕ₊₁→ℤ>0 (1+ n) = transport (>0≡>0r-ℤ (ℕ₊₁→ℤ (1+ n))) zero-<sucPos

  ℕ₊₁→R : ℕ₊₁ → K
  ℕ₊₁→R n = ℤ→R (ℕ₊₁→ℤ n)

  ℕ₊₁→R>0 : (n : ℕ₊₁) → ℕ₊₁→R n > 0r
  ℕ₊₁→R>0 n = ℤ→R-Pres>0'' (ℕ₊₁→ℤ n) (ℕ₊₁→ℤ>0 n)

  ℕ₊₁→R≢0 : (n : ℕ₊₁) → ¬ ℕ₊₁→R n ≡ 0r
  ℕ₊₁→R≢0 n = >-arefl (ℕ₊₁→R>0 n)

  ℕ₊₁→ℤ-·₊₁-comm : (m n : ℕ₊₁) → ℕ₊₁→ℤ (m ·₊₁ n) ≡ (ℕ₊₁→ℤ m) ·ℤ (ℕ₊₁→ℤ n)
  ℕ₊₁→ℤ-·₊₁-comm (1+ m) (1+ n) = pos·pos (suc m) (suc n)


  private

    module _ ((a , b) : ℤ × ℕ₊₁) where

      map-helper : K
      map-helper = ℤ→R a · inv (ℕ₊₁→R≢0 b)

      >0-helper' : a >ℤ 0 → map-helper > 0r
      >0-helper' a>0 = ·-Pres>0 (ℤ→R-Pres>0'' _ a>0) (p>0→p⁻¹>0 (ℕ₊₁→R>0 b))

      >0-helper : ℚSO._>0 [ a , b ] → map-helper >0
      >0-helper a/b>0 =
        transport (sym (>0≡>0r _))
          (>0-helper' (subst (_>ℤ pos 0) (Int.·IdR a) a/b>0))


    module _ ((a , b)(c , d) : ℤ × ℕ₊₁) where

      b≢0 = ℕ₊₁→R≢0 b
      d≢0 = ℕ₊₁→R≢0 d
      bd≢0 = ℕ₊₁→R≢0 (b ·₊₁ d)
      b⁻¹ = inv b≢0
      d⁻¹ = inv d≢0

      eq-helper : (r : (a , b) ∼ (c , d)) → map-helper (a , b) ≡ map-helper (c , d)
      eq-helper r = sym (·IdR _)
        ∙ (λ i → (ℤ→R a · b⁻¹) · ·-rInv d≢0 (~ i))
        ∙ helper4 _ _ _ _
        ∙ (λ i → (ℤ→R-Pres-· a (ℕ₊₁→ℤ d) (~ i) · b⁻¹) · d⁻¹)
        ∙ (λ i → (ℤ→R (r i) · b⁻¹) · d⁻¹)
        ∙ (λ i → (ℤ→R-Pres-· c (ℕ₊₁→ℤ b) i · b⁻¹) · d⁻¹)
        ∙ helper5 _ _ _ _
        ∙ (λ i → (ℤ→R c · d⁻¹) · ·-rInv b≢0 i)
        ∙ ·IdR _

      inv-path : inv (ℕ₊₁→R≢0 (b ·₊₁ d)) ≡ inv (·-≢0 b≢0 d≢0)
      inv-path i = invUniq {x≢0 = ℕ₊₁→R≢0 (b ·₊₁ d)} {y≢0 = ·-≢0 b≢0 d≢0}
        (cong ℤ→R (ℕ₊₁→ℤ-·₊₁-comm b d) ∙ ℤ→R-Pres-· _ _) i

      hom-helper : (a b c d : ℤ) → ℤ→R (a ·ℤ d +ℤ c ·ℤ b) ≡ ℤ→R a · ℤ→R d + ℤ→R c · ℤ→R b
      hom-helper a b c d = ℤ→R-Pres-+ _ _ ∙ (λ i → ℤ→R-Pres-· a d i + ℤ→R-Pres-· c b i)

      +-helper : map-helper (a ·ℤ ℕ₊₁→ℤ d +ℤ c ·ℤ ℕ₊₁→ℤ b , b ·₊₁ d) ≡ map-helper (a , b) + map-helper (c , d)
      +-helper = (λ i → hom-helper a (ℕ₊₁→ℤ b) c (ℕ₊₁→ℤ d) i · inv bd≢0)
        ∙ (λ i → (ℤ→R a · ℕ₊₁→R d + ℤ→R c · ℕ₊₁→R b) · inv-path i)
        ∙ (λ i → (ℤ→R a · ℕ₊₁→R d + ℤ→R c · ℕ₊₁→R b) · ·-Inv b≢0 d≢0 (~ i))
        ∙ helper1 _ _ _ _ _ _
        ∙ (λ i → (ℤ→R a · b⁻¹) · ·-rInv d≢0 i + (ℤ→R c · d⁻¹) · ·-rInv b≢0 i)
        ∙ helper2 _ _ _ _

      ·-helper : map-helper (a ·ℤ c , b ·₊₁ d) ≡ map-helper (a , b) · map-helper (c , d)
      ·-helper = (λ i → ℤ→R-Pres-· a c i · inv bd≢0)
        ∙ (λ i → (ℤ→R a · ℤ→R c) · inv-path i)
        ∙ (λ i → (ℤ→R a · ℤ→R c) · ·-Inv b≢0 d≢0 (~ i))
        ∙ helper3 _ _ _ _


  ℚ→K : ℚ → K
  ℚ→K =  SetQuot.elim (λ _ → isSetK) map-helper eq-helper

  ℚ→K-Pres-1 : ℚ→K 1 ≡ 1r
  ℚ→K-Pres-1 = ·-rInv _

  ℚ→K-Pres-+ : (p q : ℚ) → ℚ→K (p +ℚ q) ≡ ℚ→K p + ℚ→K q
  ℚ→K-Pres-+ = elimProp2 (λ _ _ → isSetK _ _) +-helper

  ℚ→K-Pres-· : (p q : ℚ) → ℚ→K (p ·ℚ q) ≡ ℚ→K p · ℚ→K q
  ℚ→K-Pres-· = elimProp2 (λ _ _ → isSetK _ _) ·-helper

  ℚ→K-Pres->0 : (p : ℚ) → ℚSO._>0 p → ℚ→K p >0
  ℚ→K-Pres->0 = elimProp (λ _ → isPropΠ (λ _ → isProp>0 _)) >0-helper


  {-

    (Ordered) Ring Homomorphism Instance

  -}

  isRingHomℚ→K : IsRingHom (CommRing→Ring ℚCommRing .snd) ℚ→K (CommRing→Ring (StrictlyOrderedCommRing→CommRing (𝒦 .fst)) .snd)
  isRingHomℚ→K = makeIsRingHom ℚ→K-Pres-1 ℚ→K-Pres-+ ℚ→K-Pres-·

  ℚ→KCommRingHom : CommRingHom ℚCommRing (StrictlyOrderedCommRing→CommRing (𝒦 .fst))
  ℚ→KCommRingHom = _ , IsRingHom→IsCommRingHom ℚCommRing (StrictlyOrderedCommRing→CommRing (𝒦 .fst)) ℚ→K isRingHomℚ→K

  open StrictlyOrderedCommRingHom

  ℚ→KStrictlyOrderedCommRingHom : StrictlyOrderedCommRingHom (ℚOrderedField .fst) (𝒦 .fst)
  ℚ→KStrictlyOrderedCommRingHom .ring-hom = ℚ→KCommRingHom
  ℚ→KStrictlyOrderedCommRingHom .pres->0  = ℚ→K-Pres->0

  ℚ→KOrderedFieldHom : OrderedFieldHom ℚOrderedField 𝒦
  ℚ→KOrderedFieldHom = ℚ→KStrictlyOrderedCommRingHom
