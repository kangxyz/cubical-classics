{-

Multiplicative Structure on Dedekind Cuts

-}
{-# OPTIONS --safe --lossy-unification #-}
module Classical.Algebra.OrderedField.DedekindCut.Multiplication where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
import Cubical.Functions.Logic as L
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Nullary
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Field using (IsField ; isfield)
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.StrictOrder
open import Cubical.Tactics.CommRingSolver.Reflection

open import Classical.Axioms
open import Classical.Foundations.Powerset

open import Classical.Algebra.StrictlyOrderedCommRing
import Classical.Algebra.StrictlyOrderedCommRing.Base as StrictBase
open import Classical.Algebra.StrictlyOrderedCommRing.Archimedes
open import Classical.Algebra.OrderedField
open import Classical.Algebra.OrderedField.DedekindCut.Base
open import Classical.Algebra.OrderedField.DedekindCut.Algebra
open import Classical.Algebra.OrderedField.DedekindCut.Signature
open import Classical.Algebra.OrderedField.DedekindCut.Order

private
  variable
    ℓ ℓ' : Level


module Multiplication ⦃ 🤖 : Oracle ⦄
  (𝒦 : OrderedField ℓ ℓ')(archimedes : isArchimedean (𝒦 . fst))
  where

  private
    K = 𝒦 .fst .fst .fst

  open OrderedFieldStr 𝒦
  open Basics   𝒦
  open Algebra  𝒦 archimedes
  open Order    𝒦 archimedes
  open DedekindCut


  {-

    Full Multiplication

  -}

  _·𝕂_ : 𝕂 → 𝕂 → 𝕂
  (a ·𝕂 b) = signed (sign a ·s sign b) (abs𝕂 a ·𝕂₊ abs𝕂 b)


  private
    lZeroSign : (a : 𝕂) → sign 𝟘 ≡ sign 𝟘 ·s sign a
    lZeroSign a = sign𝟘 ∙ (λ i → sign𝟘 (~ i) ·s sign a)

    rZeroSign : (a : 𝕂) → sign 𝟘 ≡ sign a ·s sign 𝟘
    rZeroSign a = lZeroSign a ∙ ·s-Comm (sign 𝟘) (sign a)

    lZero : (a : 𝕂) → abs𝕂 𝟘 ≡ abs𝕂 𝟘 ·𝕂₊ abs𝕂 a
    lZero a = abs𝟘 ∙ sym (·𝕂₊ZeroL (abs𝕂 a)) ∙ (λ i → abs𝟘 (~ i) ·𝕂₊ abs𝕂 a)

    rZero : (a : 𝕂) → abs𝕂 𝟘 ≡ abs𝕂 a ·𝕂₊ abs𝕂 𝟘
    rZero a = lZero a ∙ ·𝕂₊Comm (abs𝕂 𝟘) (abs𝕂 a)

  sign· : (a b : 𝕂) → sign (a ·𝕂 b) ≡ sign a ·s sign b
  sign· a b = case-split (trichotomy𝕂 a 𝟘) (trichotomy𝕂 b 𝟘)
    where
    case-split : Trichotomy𝕂 a 𝟘 → Trichotomy𝕂 b 𝟘 → sign (a ·𝕂 b) ≡ sign a ·s sign b
    case-split (gt a>0) (gt b>0) =
      sign-signed _ (abs𝕂 a ·𝕂₊ abs𝕂 b) (>𝕂-arefl (·𝕂-Pres>0 (abs𝕂 a) (abs𝕂 b) (abs>0 a a>0) (abs>0 b b>0)))
    case-split (lt a<0) (lt b<0) =
      sign-signed _ (abs𝕂 a ·𝕂₊ abs𝕂 b) (>𝕂-arefl (·𝕂-Pres>0 (abs𝕂 a) (abs𝕂 b) (abs<0 a a<0) (abs<0 b b<0)))
    case-split (gt a>0) (lt b<0) =
      sign-signed _ (abs𝕂 a ·𝕂₊ abs𝕂 b) (>𝕂-arefl (·𝕂-Pres>0 (abs𝕂 a) (abs𝕂 b) (abs>0 a a>0) (abs<0 b b<0)))
    case-split (lt a<0) (gt b>0) =
      sign-signed _ (abs𝕂 a ·𝕂₊ abs𝕂 b) (>𝕂-arefl (·𝕂-Pres>0 (abs𝕂 a) (abs𝕂 b) (abs<0 a a<0) (abs>0 b b>0)))
    case-split (eq a≡0) _ =
      (λ i → sign (signed (sign≡0 a a≡0 i ·s sign b) (abs𝕂 a ·𝕂₊ abs𝕂 b)))
      ∙ lZeroSign b ∙ (λ i → sign (a≡0 (~ i)) ·s sign b)
    case-split _ (eq b≡0) =
      (λ i → sign (signed (sign a ·s sign≡0 b b≡0 i) (abs𝕂 a ·𝕂₊ abs𝕂 b)))
      ∙ (λ i → sign (signed (·s-Comm (sign a) nul i) (abs𝕂 a ·𝕂₊ abs𝕂 b)))
      ∙ rZeroSign a ∙ (λ i → sign a ·s sign (b≡0 (~ i)))

  abs· : (a b : 𝕂) → abs𝕂 (a ·𝕂 b) ≡ (abs𝕂 a ·𝕂₊ abs𝕂 b)
  abs· a b = case-split (trichotomy𝕂 a 𝟘) (trichotomy𝕂 b 𝟘)
    where
    case-split : Trichotomy𝕂 a 𝟘 → Trichotomy𝕂 b 𝟘 → abs𝕂 (a ·𝕂 b) ≡ (abs𝕂 a ·𝕂₊ abs𝕂 b)
    case-split (gt a>0) (gt b>0) =
      (λ i → abs𝕂 (signed (sign>0 a a>0 i ·s sign>0 b b>0 i) (abs𝕂 a ·𝕂₊ abs𝕂 b)))
      ∙ abs-signed _ _ pos≢nul
    case-split (lt a<0) (lt b<0) =
      (λ i → abs𝕂 (signed (sign<0 a a<0 i ·s sign<0 b b<0 i) (abs𝕂 a ·𝕂₊ abs𝕂 b)))
      ∙ abs-signed _ _ pos≢nul
    case-split (gt a>0) (lt b<0) =
      (λ i → abs𝕂 (signed (sign>0 a a>0 i ·s sign<0 b b<0 i) (abs𝕂 a ·𝕂₊ abs𝕂 b)))
      ∙ abs-signed _ _ neg≢nul
    case-split (lt a<0) (gt b>0) =
      (λ i → abs𝕂 (signed (sign<0 a a<0 i ·s sign>0 b b>0 i) (abs𝕂 a ·𝕂₊ abs𝕂 b)))
      ∙ abs-signed _ _ neg≢nul
    case-split (eq a≡0) _ =
      (λ i → abs𝕂 (signed (sign≡0 a a≡0 i ·s sign b) (abs𝕂 a ·𝕂₊ abs𝕂 b)))
      ∙ lZero b ∙ (λ i → abs𝕂 (a≡0 (~ i)) ·𝕂₊ abs𝕂 b)
    case-split _ (eq b≡0) =
      (λ i → abs𝕂 (signed (sign a ·s sign≡0 b b≡0 i) (abs𝕂 a ·𝕂₊ abs𝕂 b)))
      ∙ (λ i → abs𝕂 (signed (·s-Comm (sign a) nul i) (abs𝕂 a ·𝕂₊ abs𝕂 b)))
      ∙ rZero a ∙ (λ i → abs𝕂 a ·𝕂₊ abs𝕂 (b≡0 (~ i)))


  ·𝕂Comm : (a b : 𝕂) → a ·𝕂 b ≡ b ·𝕂 a
  ·𝕂Comm a b i = signed (·s-Comm (sign a) (sign b) i) (·𝕂₊Comm (abs𝕂 a) (abs𝕂 b) i)

  ·𝕂Assoc : (a b c : 𝕂) → a ·𝕂 (b ·𝕂 c) ≡ (a ·𝕂 b) ·𝕂 c
  ·𝕂Assoc a b c =
    let p = λ i → signed (sign a ·s sign· b c i) (abs𝕂 a ·𝕂₊ abs· b c i)
        q = λ i → signed (sign· a b i ·s sign c) (abs· a b i ·𝕂₊ abs𝕂 c)
        r = λ i → signed (·s-Assoc (sign a) (sign b) (sign c) i) (·𝕂₊Assoc (abs𝕂 a) (abs𝕂 b) (abs𝕂 c) i)
    in  p ∙ r ∙ sym q


  ·𝕂IdR : (a : 𝕂) → a ·𝕂 𝟙 ≡ a
  ·𝕂IdR a = (λ i → signed (sign-path i) (abs𝕂 a ·𝕂₊ abs𝟙 i))
    ∙ (λ i → signed (sign a) (·𝕂₊IdR (abs𝕂 a) i))
    ∙ sign-abs-≡ a
    where
    sign-path : sign a ·s sign 𝟙 ≡ sign a
    sign-path = (λ i → sign a ·s sign𝟙 i) ∙ ·s-rUnit (sign a)

  ·𝕂ZeroR : (a : 𝕂) → a ·𝕂 𝟘 ≡ 𝟘
  ·𝕂ZeroR a = (λ i → signed (sign a ·s sign 𝟘) (abs𝕂 a ·𝕂₊ abs𝟘 i))
    ∙ (λ i → signed (sign a ·s sign 𝟘) (·𝕂₊ZeroR (abs𝕂 a) i))
    ∙ signed𝟘 (sign a ·s sign 𝟘)

  ·𝕂ZeroL : (a : 𝕂) → 𝟘 ·𝕂 a ≡ 𝟘
  ·𝕂ZeroL a = ·𝕂Comm 𝟘 a ∙ ·𝕂ZeroR a


  neg-·𝕂 : (a b : 𝕂) → ((-𝕂 a) ·𝕂 b) ≡ -𝕂 (a ·𝕂 b)
  neg-·𝕂  a b = (λ i → signed (-sign a i ·s sign b) (abs-𝕂 a i ·𝕂₊ abs𝕂 b))
    ∙ (λ i → signed (-s-· (sign a) (sign b) i) (abs𝕂 a ·𝕂₊ abs𝕂 b))
    ∙ signed- (sign a ·s sign b) (abs𝕂 a ·𝕂₊ abs𝕂 b)

  ·𝕂-neg : (a b : 𝕂) → (a ·𝕂 (-𝕂 b)) ≡ -𝕂 (a ·𝕂 b)
  ·𝕂-neg a b = ·𝕂Comm a (-𝕂 b) ∙ neg-·𝕂 b a ∙ cong (-𝕂_) (·𝕂Comm b a)

  neg-·𝕂-neg : (a b : 𝕂) → ((-𝕂 a) ·𝕂 (-𝕂 b)) ≡ a ·𝕂 b
  neg-·𝕂-neg a b = neg-·𝕂 a (-𝕂 b) ∙ cong (-𝕂_) (·𝕂-neg a b) ∙ -𝕂Involutive (a ·𝕂 b)


  private
    ·pos-helper : (a b : 𝕂) → a ≥𝕂 𝟘 → b ≥𝕂 𝟘 → a ·𝕂 b ≡ ((abs𝕂 a) ·𝕂₊ (abs𝕂 b)) .fst
    ·pos-helper a b a≥0 b≥0 = case-split (trichotomy𝕂 a 𝟘) (trichotomy𝕂 b 𝟘)
      where
      case-split : Trichotomy𝕂 a 𝟘 → Trichotomy𝕂 b 𝟘 → a ·𝕂 b ≡ ((abs𝕂 a) ·𝕂₊ (abs𝕂 b)) .fst
      case-split (lt a<0) _ = Empty.rec (<≤𝕂-asym a 𝟘 a<0 a≥0)
      case-split _ (lt b<0) = Empty.rec (<≤𝕂-asym b 𝟘 b<0 b≥0)
      case-split (eq a≡0) _ =
          (λ i → a≡0 i ·𝕂 b)
        ∙ ·𝕂ZeroL b
        ∙ (λ i → (·𝕂₊ZeroL (abs𝕂 b) (~ i)) .fst)
        ∙ (λ i → (abs𝟘 (~ i) ·𝕂₊ (abs𝕂 b)) .fst)
        ∙ (λ i → (abs𝕂 (a≡0 (~ i)) ·𝕂₊ (abs𝕂 b)) .fst)
      case-split _ (eq b≡0) =
        (λ i → a ·𝕂 b≡0 i)
        ∙ ·𝕂ZeroR a
        ∙ (λ i → (·𝕂₊ZeroR (abs𝕂 a) (~ i)) .fst)
        ∙ (λ i → ((abs𝕂 a) ·𝕂₊ abs𝟘 (~ i)) .fst)
        ∙ (λ i → ((abs𝕂 a) ·𝕂₊ abs𝕂 (b≡0 (~ i))) .fst)
      case-split (gt a>0) (gt b>0) i =
        signed ((sign>0 a a>0 i) ·s(sign>0 b b>0 i)) ((abs𝕂 a) ·𝕂₊ (abs𝕂 b))

    +pos-helper : (a b : 𝕂) → a ≥𝕂 𝟘 → b ≥𝕂 𝟘 → abs𝕂 (a +𝕂 b) ≡ ((abs𝕂 a) +𝕂₊ (abs𝕂 b))
    +pos-helper a b a≥0 b≥0 = path-𝕂₊ (abs𝕂 (a +𝕂 b)) _ path
      where a+b≥0 : (a +𝕂 b) ≥𝕂 𝟘
            a+b≥0 = +𝕂-Pres≥0 a b a≥0 b≥0
            path : abs𝕂 (a +𝕂 b) .fst ≡ ((abs𝕂 a) +𝕂₊ (abs𝕂 b)) .fst
            path = abs≥0 (a +𝕂 b) a+b≥0 ∙ (λ i → abs≥0 a a≥0 (~ i) +𝕂 abs≥0 b b≥0 (~ i))

  ·𝕂DistR-PosPosPos : (a b c : 𝕂)
    → a ≥𝕂 𝟘 → b ≥𝕂 𝟘 → c ≥𝕂 𝟘
    → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
  ·𝕂DistR-PosPosPos a b c a≥0 b≥0 c≥0 =
      (λ i → ·pos-helper a b a≥0 b≥0 i +𝕂 ·pos-helper a c a≥0 c≥0 i)
    ∙ (λ i → ·𝕂₊DistR (abs𝕂 a) (abs𝕂 b) (abs𝕂 c) i .fst)
    ∙ (λ i → ((abs𝕂 a) ·𝕂₊ +pos-helper b c b≥0 c≥0 (~ i)) .fst)
    ∙ sym (·pos-helper a (b +𝕂 c) a≥0 b+c≥0)
    where
    b+c≥0 : (b +𝕂 c) ≥𝕂 𝟘
    b+c≥0 = +𝕂-Pres≥0 b c b≥0 c≥0

  ·𝕂DistR-PosPosNeg : (a b c : 𝕂)
    → a ≥𝕂 𝟘 → b ≥𝕂 𝟘 → c <𝕂 𝟘 → (b +𝕂 c) ≥𝕂 𝟘
    → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
  ·𝕂DistR-PosPosNeg a b c a≥0 b≥0 c<0 b+c≥0 = (λ i → path1 (~ i) +𝕂 (a ·𝕂 c)) ∙ path2
    where
    path1 : (a ·𝕂 (b +𝕂 c)) +𝕂 (-𝕂 (a ·𝕂 c)) ≡ a ·𝕂 b
    path1 = (λ i → (a ·𝕂 (b +𝕂 c)) +𝕂 ·𝕂-neg a c (~ i))
      ∙ ·𝕂DistR-PosPosPos a (b +𝕂 c) (-𝕂 c) a≥0 b+c≥0 (<0-reverse c c<0)
      ∙ (λ i → a ·𝕂 +𝕂Assoc b c (-𝕂 c) (~ i))
      ∙ (λ i → a ·𝕂 (b +𝕂 +𝕂InvR c i)) ∙ (λ i → a ·𝕂 (+𝕂IdR b i))
    path2 : ((a ·𝕂 (b +𝕂 c)) +𝕂 (-𝕂 (a ·𝕂 c))) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
    path2 = sym (+𝕂Assoc _ _ _) ∙ (λ i → (a ·𝕂 (b +𝕂 c)) +𝕂 +𝕂InvL (a ·𝕂 c) i) ∙ +𝕂IdR _

  ·𝕂DistR-PosPos : (a b c : 𝕂)
    → a ≥𝕂 𝟘 → (b +𝕂 c) ≥𝕂 𝟘
    → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
  ·𝕂DistR-PosPos a b c a≥0 b+c≥0 = case-split (dichotomy𝕂 b 𝟘) (dichotomy𝕂 c 𝟘)
    where
    case-split : Dichotomy𝕂 b 𝟘 → Dichotomy𝕂 c 𝟘 → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
    case-split (ge b≥0) (ge c≥0) = ·𝕂DistR-PosPosPos a b c a≥0 b≥0 c≥0
    case-split (lt b<0) (ge c≥0) = +𝕂Comm _ _
      ∙ (λ i → ·𝕂DistR-PosPosNeg a c b a≥0 c≥0 b<0 c+b≥0 i)
      ∙ (λ i → a ·𝕂 +𝕂Comm c b i)
      where c+b≥0 : (c +𝕂 b) ≥𝕂 𝟘
            c+b≥0 = subst (_≥𝕂 𝟘) (+𝕂Comm b c) b+c≥0
    case-split (ge b≥0) (lt c<0) = ·𝕂DistR-PosPosNeg a b c a≥0 b≥0 c<0 b+c≥0
    case-split (lt b<0) (lt c<0) = Empty.rec (<≤𝕂-asym (b +𝕂 c) 𝟘 (+𝕂-Pres<0 b c b<0 c<0) b+c≥0)

  private
    alg-helper' : (a b c d : 𝕂) → (a +𝕂 b) +𝕂 (c +𝕂 d) ≡ (a +𝕂 c) +𝕂 (b +𝕂 d)
    alg-helper' a b c d = +𝕂Assoc (a +𝕂 b) c d
      ∙ (λ i → +𝕂Assoc a b c (~ i) +𝕂 d)
      ∙ (λ i → (a +𝕂 +𝕂Comm b c i) +𝕂 d)
      ∙ (λ i → +𝕂Assoc a c b i +𝕂 d)
      ∙ sym (+𝕂Assoc (a +𝕂 c) b d)

    alg-helper : (a b : 𝕂) → -𝕂 (a +𝕂 b) ≡ (-𝕂 a) +𝕂 (-𝕂 b)
    alg-helper a b = sym (+𝕂IdR (-𝕂 (a +𝕂 b)))
      ∙ (λ i → (-𝕂 (a +𝕂 b)) +𝕂 path (~ i))
      ∙ +𝕂Assoc _ _ _
      ∙ (λ i → +𝕂InvL (a +𝕂 b) i +𝕂 ((-𝕂 a) +𝕂 (-𝕂 b)))
      ∙ +𝕂IdL ((-𝕂 a) +𝕂 (-𝕂 b))
      where
      path : (a +𝕂 b) +𝕂 ((-𝕂 a) +𝕂 (-𝕂 b)) ≡ 𝟘
      path = alg-helper' _ _ _ _ ∙ (λ i → +𝕂InvR a i +𝕂 +𝕂InvR b i) ∙ +𝕂IdR 𝟘

  ·𝕂DistR-NegPos : (a b c : 𝕂)
    → a <𝕂 𝟘 → (b +𝕂 c) ≥𝕂 𝟘
    → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
  ·𝕂DistR-NegPos a b c a<0 b+c≥0 =
    sym (-𝕂Involutive _) ∙ (λ i → -𝕂 path i) ∙ -𝕂Involutive _
    where
    path : -𝕂 ((a ·𝕂 b) +𝕂 (a ·𝕂 c)) ≡ -𝕂 (a ·𝕂 (b +𝕂 c))
    path = alg-helper (a ·𝕂 b) (a ·𝕂 c)
      ∙ (λ i → neg-·𝕂 a b (~ i) +𝕂 neg-·𝕂 a c (~ i))
      ∙ ·𝕂DistR-PosPos (-𝕂 a) b c (<0-reverse a a<0) b+c≥0
      ∙ neg-·𝕂 a (b +𝕂 c)

  ·𝕂DistR-Pos : (a b c : 𝕂)
    → (b +𝕂 c) ≥𝕂 𝟘
    → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
  ·𝕂DistR-Pos a b c b+c≥0 = case-split (dichotomy𝕂 a 𝟘)
    where
    case-split : Dichotomy𝕂 a 𝟘 → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
    case-split (ge a≥0) = ·𝕂DistR-PosPos a b c a≥0 b+c≥0
    case-split (lt a<0) = ·𝕂DistR-NegPos a b c a<0 b+c≥0

  ·𝕂DistR-Neg : (a b c : 𝕂)
    → (b +𝕂 c) <𝕂 𝟘
    → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
  ·𝕂DistR-Neg a b c b+c<0 =
    sym (-𝕂Involutive _) ∙ (λ i → -𝕂 path i) ∙ -𝕂Involutive _
    where
    -b+-k≥0 : ((-𝕂 b) +𝕂 (-𝕂 c)) ≥𝕂 𝟘
    -b+-k≥0 = subst (_≥𝕂 𝟘) (alg-helper b c) (<0-reverse (b +𝕂 c) b+c<0)
    path : -𝕂 ((a ·𝕂 b) +𝕂 (a ·𝕂 c)) ≡ -𝕂 (a ·𝕂 (b +𝕂 c))
    path = alg-helper (a ·𝕂 b) (a ·𝕂 c)
      ∙ (λ i → ·𝕂-neg a b (~ i) +𝕂 ·𝕂-neg a c (~ i))
      ∙ ·𝕂DistR-Pos a (-𝕂 b) (-𝕂 c) -b+-k≥0
      ∙ (λ i → a ·𝕂 alg-helper b c (~ i))
      ∙ ·𝕂-neg a (b +𝕂 c)

  ·𝕂DistR : (a b c : 𝕂) → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
  ·𝕂DistR a b c = case-split (dichotomy𝕂 (b +𝕂 c) 𝟘)
    where
    case-split : Dichotomy𝕂 (b +𝕂 c) 𝟘 → (a ·𝕂 b) +𝕂 (a ·𝕂 c) ≡ a ·𝕂 (b +𝕂 c)
    case-split (ge b+c≥0) = ·𝕂DistR-Pos a b c b+c≥0
    case-split (lt b+c<0) = ·𝕂DistR-Neg a b c b+c<0


  -- The previously defined _·𝕂₊_ is equal to _·𝕂_ when both variables are non-negative.

  ·𝕂≡·𝕂₊ : (a b : 𝕂₊) → a .fst ·𝕂 b .fst ≡ (a ·𝕂₊ b) .fst
  ·𝕂≡·𝕂₊ (a , a≥0) (b , b≥0) = ·pos-helper a b a≥0 b≥0
    ∙ (λ i → (path-𝕂₊ (abs𝕂 a) (a , a≥0) (abs≥0 a a≥0) i
          ·𝕂₊ path-𝕂₊ (abs𝕂 b) (b , b≥0) (abs≥0 b b≥0) i) .fst)


  {-

    Commutative Ring Instance

  -}

  𝕂CommRing : CommRing (ℓ-max ℓ ℓ')
  𝕂CommRing = makeCommRing {R = 𝕂}
      𝟘 𝟙 _+𝕂_ _·𝕂_ -𝕂_ isSet𝕂
    +𝕂Assoc +𝕂IdR +𝕂InvR +𝕂Comm
    ·𝕂Assoc ·𝕂IdR (λ x y z → sym (·𝕂DistR x y z)) ·𝕂Comm


  {-

    Strictly ordered commutative ring instance

  -}

  private
    ·𝕂-Pos-helper : (a b : 𝕂) → a >𝕂 𝟘 → b >𝕂 𝟘 → ((abs𝕂 a) ·𝕂₊ (abs𝕂 b)) .fst ≡ a ·𝕂 b
    ·𝕂-Pos-helper a b a>0 b>0 = sym (·pos-helper a b (<𝕂→≤𝕂 {a = 𝟘} {b = a} a>0) (<𝕂→≤𝕂 {a = 𝟘} {b = b} b>0))

  ·𝕂'-Pres>0 : (a b : 𝕂) → a >𝕂 𝟘 → b >𝕂 𝟘 → (a ·𝕂 b) >𝕂 𝟘
  ·𝕂'-Pres>0 a b a>0 b>0 =
    subst (_>𝕂 𝟘) (·𝕂-Pos-helper a b a>0 b>0) (·𝕂-Pres>0 (abs𝕂 a) (abs𝕂 b) (abs>0 a a>0) (abs>0 b b>0))

  private
    open BinaryRelation

    ≤𝕂-trans : (a b c : 𝕂) → a ≤𝕂 b → b ≤𝕂 c → a ≤𝕂 c
    ≤𝕂-trans a b c a≤b b≤c = lift (λ x∈c → lower a≤b (lower b≤c x∈c))

    𝕂≤Poset : Poset (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
    𝕂≤Poset = poset 𝕂 _≤𝕂_
      (isposet isSet𝕂 (λ a b → isProp≤𝕂 {a = a} {b = b})
        (λ a → ≤𝕂-refl {a = a} refl)
        ≤𝕂-trans
        (λ a b a≤b b≤a → ≤𝕂-asym a≤b b≤a))

    min𝕂 : 𝕂 → 𝕂 → 𝕂
    min𝕂 a b with dichotomy𝕂 a b
    ... | lt a<b = a
    ... | ge a≥b = b

    max𝕂 : 𝕂 → 𝕂 → 𝕂
    max𝕂 a b with dichotomy𝕂 a b
    ... | lt a<b = b
    ... | ge a≥b = a

    min𝕂≤left : {a b : 𝕂} → min𝕂 a b ≤𝕂 a
    min𝕂≤left {a = a} {b = b} with dichotomy𝕂 a b
    ... | lt a<b = ≤𝕂-refl {a = a} refl
    ... | ge a≥b = a≥b

    min𝕂≤right : {a b : 𝕂} → min𝕂 a b ≤𝕂 b
    min𝕂≤right {a = a} {b = b} with dichotomy𝕂 a b
    ... | lt a<b = <𝕂→≤𝕂 {a = a} {b = b} a<b
    ... | ge a≥b = ≤𝕂-refl {a = b} refl

    ≤min𝕂 : {a b x : 𝕂} → x ≤𝕂 a → x ≤𝕂 b → x ≤𝕂 min𝕂 a b
    ≤min𝕂 {a = a} {b = b} x≤a x≤b with dichotomy𝕂 a b
    ... | lt a<b = x≤a
    ... | ge a≥b = x≤b

    left≤max𝕂 : {a b : 𝕂} → a ≤𝕂 max𝕂 a b
    left≤max𝕂 {a = a} {b = b} with dichotomy𝕂 a b
    ... | lt a<b = <𝕂→≤𝕂 {a = a} {b = b} a<b
    ... | ge a≥b = ≤𝕂-refl {a = a} refl

    right≤max𝕂 : {a b : 𝕂} → b ≤𝕂 max𝕂 a b
    right≤max𝕂 {a = a} {b = b} with dichotomy𝕂 a b
    ... | lt a<b = ≤𝕂-refl {a = b} refl
    ... | ge a≥b = a≥b

    max𝕂≤ : {a b x : 𝕂} → a ≤𝕂 x → b ≤𝕂 x → max𝕂 a b ≤𝕂 x
    max𝕂≤ {a = a} {b = b} a≤x b≤x with dichotomy𝕂 a b
    ... | lt a<b = b≤x
    ... | ge a≥b = a≤x

    𝕂≤Pseudolattice : Pseudolattice (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
    𝕂≤Pseudolattice =
      makePseudolatticeFromPoset 𝕂≤Poset min𝕂 max𝕂
        min𝕂≤left min𝕂≤right ≤min𝕂
        left≤max𝕂 right≤max𝕂 max𝕂≤

    <𝕂-trans : (a b c : 𝕂) → a <𝕂 b → b <𝕂 c → a <𝕂 c
    <𝕂-trans a b c a<b b<c = do
      (q , q<r∈c , q∈b) ← b<c
      return (q , q<r∈c , lower (<𝕂→≤𝕂 {a = a} {b = b} a<b) q∈b)

    <𝕂-weaklyLinear : (a b c : 𝕂) → a <𝕂 b → (a <𝕂 c) L.⊔′ (c <𝕂 b)
    <𝕂-weaklyLinear a b c a<b with trichotomy𝕂 c b
    ... | lt c<b = ∣ inr c<b ∣₁
    ... | eq c≡b = ∣ inl (subst (a <𝕂_) (sym c≡b) a<b) ∣₁
    ... | gt c>b = ∣ inl (<𝕂-trans a b c a<b c>b) ∣₁

    <𝕂≤𝕂-trans : (a b c : 𝕂) → a <𝕂 b → b ≤𝕂 c → a <𝕂 c
    <𝕂≤𝕂-trans a b c a<b b≤c with split≤𝕂 b c b≤c
    ... | lt b<c = <𝕂-trans a b c a<b b<c
    ... | eq b≡c = subst (a <𝕂_) b≡c a<b

    ≤𝕂<𝕂-trans : (a b c : 𝕂) → a ≤𝕂 b → b <𝕂 c → a <𝕂 c
    ≤𝕂<𝕂-trans a b c a≤b b<c with split≤𝕂 a b a≤b
    ... | lt a<b = <𝕂-trans a b c a<b b<c
    ... | eq a≡b = subst (_<𝕂 c) (sym a≡b) b<c

    ≤𝕂≃¬>𝕂 : (a b : 𝕂) → (a ≤𝕂 b) ≃ (¬ (b <𝕂 a))
    ≤𝕂≃¬>𝕂 a b =
      propBiimpl→Equiv (isProp≤𝕂 {a = a} {b = b}) (isProp¬ (b <𝕂 a))
        (λ a≤b b<a → <≤𝕂-asym b a b<a a≤b)
        (λ ¬b<a → ¬a>b→a≤b a b ¬b<a)

    +𝕂-posSum : (x y : 𝕂) → 𝟘 <𝕂 (x +𝕂 y) → (𝟘 <𝕂 x) L.⊔′ (𝟘 <𝕂 y)
    +𝕂-posSum x y 0<x+y with trichotomy𝕂 x 𝟘
    ... | gt x>0 = ∣ inl x>0 ∣₁
    ... | eq x≡0 = ∣ inr (subst (𝟘 <𝕂_) x+y≡y 0<x+y) ∣₁
      where
      x+y≡y : x +𝕂 y ≡ y
      x+y≡y = (λ i → x≡0 i +𝕂 y) ∙ +𝕂IdL y
    ... | lt x<0 = ∣ inr (<𝕂-trans 𝟘 (-𝕂 x) y (-reverse<0 x x<0) -x<y) ∣₁
      where
      -x<y : (-𝕂 x) <𝕂 y
      -x<y = transport (λ i → +𝕂IdL (-𝕂 x) i <𝕂 x+y-x≡y i)
        (+𝕂-rPres< 𝟘 (x +𝕂 y) (-𝕂 x) 0<x+y)
        where
        x+y-x≡y : (x +𝕂 y) +𝕂 (-𝕂 x) ≡ y
        x+y-x≡y =
          sym (+𝕂Assoc x y (-𝕂 x))
          ∙ (λ i → x +𝕂 +𝕂Comm y (-𝕂 x) i)
          ∙ +𝕂Assoc x (-𝕂 x) y
          ∙ (λ i → +𝕂InvR x i +𝕂 y)
          ∙ +𝕂IdL y

    <𝕂→Diff>0 : (a b : 𝕂) → a <𝕂 b → (b +𝕂 (-𝕂 a)) >𝕂 𝟘
    <𝕂→Diff>0 a b a<b =
      subst ((b +𝕂 (-𝕂 a)) >𝕂_) (+𝕂InvR a)
        (+𝕂-rPres< a b (-𝕂 a) a<b)

    Diff>0→<𝕂 : (a b : 𝕂) → (b +𝕂 (-𝕂 a)) >𝕂 𝟘 → a <𝕂 b
    Diff>0→<𝕂 a b 0<b-a =
      transport (λ i → +𝕂IdL a i <𝕂 b-a+a≡b i)
        (+𝕂-rPres< 𝟘 (b +𝕂 (-𝕂 a)) a 0<b-a)
      where
      b-a+a≡b : (b +𝕂 (-𝕂 a)) +𝕂 a ≡ b
      b-a+a≡b = sym (+𝕂Assoc _ _ _) ∙ (λ i → b +𝕂 +𝕂InvL a i) ∙ +𝕂IdR b

    ·𝕂-diffR : (x y z : 𝕂) → (y +𝕂 (-𝕂 x)) ·𝕂 z ≡ (y ·𝕂 z) +𝕂 (-𝕂 (x ·𝕂 z))
    ·𝕂-diffR x y z =
      ·𝕂Comm (y +𝕂 (-𝕂 x)) z
      ∙ sym (·𝕂DistR z y (-𝕂 x))
      ∙ (λ i → ·𝕂Comm z y i +𝕂 ·𝕂Comm z (-𝕂 x) i)
      ∙ (λ i → (y ·𝕂 z) +𝕂 neg-·𝕂 x z i)

    ·𝕂-rMono< : (x y z : 𝕂) → 𝟘 <𝕂 z → x <𝕂 y → (x ·𝕂 z) <𝕂 (y ·𝕂 z)
    ·𝕂-rMono< x y z 0<z x<y =
      Diff>0→<𝕂 (x ·𝕂 z) (y ·𝕂 z)
        (subst (_>𝕂 𝟘) (·𝕂-diffR x y z)
          (·𝕂'-Pres>0 (y +𝕂 (-𝕂 x)) z (<𝕂→Diff>0 x y x<y) 0<z))

    ·𝕂-rMono≤ : (x y z : 𝕂) → 𝟘 ≤𝕂 z → x ≤𝕂 y → (x ·𝕂 z) ≤𝕂 (y ·𝕂 z)
    ·𝕂-rMono≤ x y z 0≤z x≤y with split≤𝕂 𝟘 z 0≤z | split≤𝕂 x y x≤y
    ... | lt 0<z | lt x<y = <𝕂→≤𝕂 {a = x ·𝕂 z} {b = y ·𝕂 z} (·𝕂-rMono< x y z 0<z x<y)
    ... | lt 0<z | eq x≡y = ≤𝕂-refl {a = x ·𝕂 z} (λ i → x≡y i ·𝕂 z)
    ... | eq 0≡z | _ = ≤𝕂-refl {a = x ·𝕂 z} xz≡yz
      where
      xz≡yz : x ·𝕂 z ≡ y ·𝕂 z
      xz≡yz =
        (λ i → x ·𝕂 0≡z (~ i))
        ∙ ·𝕂ZeroR x
        ∙ sym (·𝕂ZeroR y)
        ∙ (λ i → y ·𝕂 0≡z i)

  𝕂IsOrderedCommRing : IsOrderedCommRing 𝟘 𝟙 _+𝕂_ _·𝕂_ -𝕂_ _<𝕂_ _≤𝕂_
  𝕂IsOrderedCommRing .IsOrderedCommRing.isCommRing = 𝕂CommRing .snd .CommRingStr.isCommRing
  𝕂IsOrderedCommRing .IsOrderedCommRing.isPseudolattice = 𝕂≤Pseudolattice .snd .PseudolatticeStr.is-pseudolattice
  𝕂IsOrderedCommRing .IsOrderedCommRing.isStrictOrder =
    isstrictorder isSet𝕂
      (λ a b → isProp<𝕂 {a = a} {b = b})
      (λ a a<a → <𝕂-arefl {a = a} {b = a} a<a refl)
      <𝕂-trans
      <𝕂-asym
      <𝕂-weaklyLinear
  𝕂IsOrderedCommRing .IsOrderedCommRing.<-≤-weaken = λ a b a<b → <𝕂→≤𝕂 {a = a} {b = b} a<b
  𝕂IsOrderedCommRing .IsOrderedCommRing.≤≃¬> = ≤𝕂≃¬>𝕂
  𝕂IsOrderedCommRing .IsOrderedCommRing.+MonoR≤ = +𝕂-rPres≤
  𝕂IsOrderedCommRing .IsOrderedCommRing.+MonoR< = +𝕂-rPres<
  𝕂IsOrderedCommRing .IsOrderedCommRing.posSum→pos∨pos = +𝕂-posSum
  𝕂IsOrderedCommRing .IsOrderedCommRing.<-≤-trans = <𝕂≤𝕂-trans
  𝕂IsOrderedCommRing .IsOrderedCommRing.≤-<-trans = ≤𝕂<𝕂-trans
  𝕂IsOrderedCommRing .IsOrderedCommRing.·MonoR≤ = ·𝕂-rMono≤
  𝕂IsOrderedCommRing .IsOrderedCommRing.·MonoR< = ·𝕂-rMono<
  𝕂IsOrderedCommRing .IsOrderedCommRing.0<1 = 1>𝕂0

  𝕂OrderedCommRing : OrderedCommRing (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  𝕂OrderedCommRing .fst = 𝕂
  𝕂OrderedCommRing .snd =
    orderedcommringstr 𝟘 𝟙 _+𝕂_ _·𝕂_ -𝕂_ _<𝕂_ _≤𝕂_ 𝕂IsOrderedCommRing

  trichotomy𝕂ᶜ : (a b : 𝕂) → StrictBase.Trichotomy 𝕂OrderedCommRing a b
  trichotomy𝕂ᶜ a b with trichotomy𝕂 a b
  ... | lt a<b = StrictBase.lt a<b
  ... | eq a≡b = StrictBase.eq a≡b
  ... | gt a>b = StrictBase.gt a>b

  𝕂StrictlyOrderedCommRing : StrictlyOrderedCommRing (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  𝕂StrictlyOrderedCommRing = 𝕂OrderedCommRing , strictorderstr trichotomy𝕂ᶜ


  {-

    Multiplicative Inverse

  -}

  isInv𝕂₊ : (a : 𝕂₊) → Type (ℓ-max ℓ ℓ')
  isInv𝕂₊ a =  Σ[ a' ∈ 𝕂₊ ] (a ·𝕂₊ a') .fst ≡ 𝟙

  isPropIsInv : (a : 𝕂₊) → isProp (isInv𝕂₊ a)
  isPropIsInv a (x , p) (y , q) i .fst = x≡y i
    where
    x≡y : x ≡ y
    x≡y = sym (·𝕂₊IdR x)
      ∙ (λ i → x ·𝕂₊ path-𝕂₊ (a ·𝕂₊ y) 𝟙₊ q (~ i))
      ∙ ·𝕂₊Assoc x a y
      ∙ (λ i → ·𝕂₊Comm x a i ·𝕂₊ y)
      ∙ (λ i → path-𝕂₊ (a ·𝕂₊ x) 𝟙₊ p i ·𝕂₊ y)
      ∙ ·𝕂₊IdL y
  isPropIsInv a u@(x , p) v@(y , q) i .snd j =
    isSet→SquareP (λ _ _ → isSet𝕂) p q
      (λ i → (a ·𝕂₊ isPropIsInv a u v i .fst) .fst) refl i j

  ·𝕂₊InvR : (a : 𝕂₊) → a .fst >𝕂 𝟘 → isInv𝕂₊ a
  ·𝕂₊InvR a = Prop.rec (isPropIsInv a)
    (λ (q , q<r∈a , q∈𝟘) →
      let q>0 = q∈𝕂₊→q>0 𝟘₊ q q∈𝟘 in
      inv𝕂₊ (a .fst) q q>0 q<r∈a , ·𝕂₊InvR' a q q>0 q<r∈a)

  inv𝕂₊>0 : (a : 𝕂₊)(a⁻¹ : isInv𝕂₊ a) → a⁻¹ .fst .fst >𝕂 𝟘
  inv𝕂₊>0 a ((a' , a'≥0) , p) with split≤𝕂 𝟘 a' a'≥0
  ... | lt 0<a' = 0<a'
  ... | eq 0≡a' = Empty.rec (<𝕂-arefl 1>𝕂0 𝟘≡𝟙)
    where 𝟘≡𝟙 : 𝟘 ≡ 𝟙
          𝟘≡𝟙 = (λ i → ·𝕂₊ZeroR a (~ i) .fst)
            ∙ (λ i → (a ·𝕂₊ path-𝕂₊ 𝟘₊ (a' , a'≥0) 0≡a' i) .fst) ∙ p


  isInv𝕂 : (a : 𝕂) → Type (ℓ-max ℓ ℓ')
  isInv𝕂 a = Σ[ a' ∈ 𝕂 ] a ·𝕂 a' ≡ 𝟙

  module _ (a : 𝕂)(a>0 : a >𝕂 𝟘) where

    private
      a₊ : 𝕂₊
      a₊ = a , <𝕂→≤𝕂 {a = 𝟘} {b = a} a>0
      Σa⁻¹ = ·𝕂₊InvR a₊ a>0
      a₊⁻¹ = Σa⁻¹ .fst
      a⁻¹ = Σa⁻¹ .fst .fst
      a⁻¹>0 = inv𝕂₊>0 _ Σa⁻¹

    ·𝕂InvR-Pos : isInv𝕂 a
    ·𝕂InvR-Pos .fst = a⁻¹
    ·𝕂InvR-Pos .snd =
        sym (·𝕂-Pos-helper a a⁻¹ a>0 a⁻¹>0)
      ∙ (λ i → (path-𝕂₊ (abs𝕂 a) a₊ (abs≥0 a (a₊ .snd)) i
          ·𝕂₊ path-𝕂₊ (abs𝕂 a⁻¹) a₊⁻¹ (abs≥0 a⁻¹ (a₊⁻¹ .snd)) i) .fst)
      ∙ Σa⁻¹ .snd


  ·𝕂InvR-Neg : (a : 𝕂)(a<0 : a <𝕂 𝟘) → isInv𝕂 a
  ·𝕂InvR-Neg a a<0 = -𝕂 -a⁻¹ , ·𝕂-neg a -a⁻¹ ∙ sym (neg-·𝕂 a -a⁻¹) ∙  Σ-a⁻¹ .snd
    where Σ-a⁻¹ : isInv𝕂 (-𝕂 a)
          Σ-a⁻¹ = ·𝕂InvR-Pos (-𝕂 a) (-reverse<0 a a<0)
          -a⁻¹ : 𝕂
          -a⁻¹ = Σ-a⁻¹ .fst


  ·𝕂InvR : (a : 𝕂) → ¬ a ≡ 𝟘 → isInv𝕂 a
  ·𝕂InvR a ¬a≡0 = case-split (trichotomy𝕂 a 𝟘)
    where
    case-split : Trichotomy𝕂 a 𝟘 → isInv𝕂 a
    case-split (gt a>0) = ·𝕂InvR-Pos a a>0
    case-split (lt a<0) = ·𝕂InvR-Neg a a<0
    case-split (eq a≡0) = Empty.rec (¬a≡0 a≡0)


  {-

    Ordered Field Instance

  -}

  𝟘≢𝟙 : ¬ 𝟘 ≡ 𝟙
  𝟘≢𝟙 = <𝕂-arefl 1>𝕂0

  IsField𝕂 : IsField 𝟘 𝟙 _+𝕂_ _·𝕂_ (-𝕂_)
  IsField𝕂 = isfield (CommRingStr.isCommRing (𝕂CommRing .snd)) ·𝕂InvR 𝟘≢𝟙

  𝕂OrderedField : OrderedField (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
  𝕂OrderedField = 𝕂StrictlyOrderedCommRing , IsField𝕂
