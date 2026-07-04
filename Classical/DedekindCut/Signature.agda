{-

Datatype to describe the sign of an element in a strictly ordered commutative ring

-}
{-# OPTIONS --safe #-}
module Classical.DedekindCut.Signature where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty
open import Cubical.Relation.Nullary


-- Being positive, zero or negative

data Sign : Type where
  pos : Sign
  nul : Sign
  neg : Sign

-- Reverse the signature

-s_ : Sign → Sign
-s pos = neg
-s nul = nul
-s neg = pos

-- Signature of multiplication

_·s_ : Sign → Sign → Sign
pos ·s x = x
nul ·s x = nul
neg ·s x = -s x

_≥0s : Sign → Type
pos ≥0s = Unit
nul ≥0s = Unit
neg ≥0s = ⊥


·s-Comm : (x y : Sign) → x ·s y ≡ y ·s x
·s-Comm pos pos = refl
·s-Comm nul pos = refl
·s-Comm neg pos = refl
·s-Comm pos nul = refl
·s-Comm nul nul = refl
·s-Comm neg nul = refl
·s-Comm pos neg = refl
·s-Comm nul neg = refl
·s-Comm neg neg = refl

·s-Assoc : (x y z : Sign) → x ·s (y ·s z) ≡  (x ·s y) ·s z
·s-Assoc nul _ _ = refl
·s-Assoc pos _ _ = refl
·s-Assoc neg pos pos = refl
·s-Assoc neg nul pos = refl
·s-Assoc neg neg pos = refl
·s-Assoc neg pos nul = refl
·s-Assoc neg nul nul = refl
·s-Assoc neg neg nul = refl
·s-Assoc neg pos neg = refl
·s-Assoc neg nul neg = refl
·s-Assoc neg neg neg = refl

·s-rUnit : (x : Sign) → x ·s pos ≡ x
·s-rUnit x = ·s-Comm x pos

-s-· : (x y : Sign) → (-s x) ·s y ≡ -s (x ·s y)
-s-· pos _ = refl
-s-· nul _ = refl
-s-· neg pos = refl
-s-· neg nul = refl
-s-· neg neg = refl


pos≢nul : ¬ pos ≡ nul
pos≢nul p = subst (λ { nul → ⊥ ; pos → Unit ; neg → Unit }) p _

neg≢nul : ¬ neg ≡ nul
neg≢nul p = subst (λ { nul → ⊥ ; pos → Unit ; neg → Unit }) p _


data TrichotomySign (x : Sign) : Type where
  ≡pos : x ≡ pos → TrichotomySign x
  ≡nul : x ≡ nul → TrichotomySign x
  ≡neg : x ≡ neg → TrichotomySign x

trichotomySign : (x : Sign) → TrichotomySign x
trichotomySign pos = ≡pos refl
trichotomySign nul = ≡nul refl
trichotomySign neg = ≡neg refl


data DichotomySign (x : Sign) : Type where
  ≡nul :   x ≡ nul → DichotomySign x
  ≢nul : ¬ x ≡ nul → DichotomySign x

dichotomySign : (x : Sign) → DichotomySign x
dichotomySign nul = ≡nul refl
dichotomySign pos = ≢nul pos≢nul
dichotomySign neg = ≢nul neg≢nul


integralSign : (x y : Sign) → ¬ x ≡ nul → ¬ y ≡ nul → ¬ (x ·s y) ≡ nul
integralSign pos pos ¬x≡nul ¬y≡nul = pos≢nul
integralSign pos nul ¬x≡nul ¬y≡nul = Empty.rec (¬y≡nul refl)
integralSign pos neg ¬x≡nul ¬y≡nul = neg≢nul
integralSign nul pos ¬x≡nul ¬y≡nul = Empty.rec (¬x≡nul refl)
integralSign nul nul ¬x≡nul ¬y≡nul = Empty.rec (¬x≡nul refl)
integralSign nul neg ¬x≡nul ¬y≡nul = Empty.rec (¬x≡nul refl)
integralSign neg pos ¬x≡nul ¬y≡nul = neg≢nul
integralSign neg nul ¬x≡nul ¬y≡nul = Empty.rec (¬y≡nul refl)
integralSign neg neg ¬x≡nul ¬y≡nul = pos≢nul
