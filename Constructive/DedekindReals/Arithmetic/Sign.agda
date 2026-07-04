{-

Constructive signs used by Dedekind-real arithmetic

This sign algebra has no dependency on LEM, Oracle, or powersets.

-}
{-# OPTIONS --safe #-}
module Constructive.DedekindReals.Arithmetic.Sign where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary


data Sign : Type where
  pos : Sign
  nul : Sign
  neg : Sign


-s_ : Sign → Sign
-s pos = neg
-s nul = nul
-s neg = pos

infixr 8 -s_


_·s_ : Sign → Sign → Sign
pos ·s y = y
nul ·s _ = nul
neg ·s y = -s y

infixl 7 _·s_


_≥0s : Sign → Type
pos ≥0s = Unit
nul ≥0s = Unit
neg ≥0s = ⊥

infix 4 _≥0s


·s-comm : (x y : Sign) → x ·s y ≡ y ·s x
·s-comm pos pos = refl
·s-comm pos nul = refl
·s-comm pos neg = refl
·s-comm nul pos = refl
·s-comm nul nul = refl
·s-comm nul neg = refl
·s-comm neg pos = refl
·s-comm neg nul = refl
·s-comm neg neg = refl


·s-assoc : (x y z : Sign) → x ·s (y ·s z) ≡ (x ·s y) ·s z
·s-assoc pos _ _ = refl
·s-assoc nul _ _ = refl
·s-assoc neg pos pos = refl
·s-assoc neg pos nul = refl
·s-assoc neg pos neg = refl
·s-assoc neg nul pos = refl
·s-assoc neg nul nul = refl
·s-assoc neg nul neg = refl
·s-assoc neg neg pos = refl
·s-assoc neg neg nul = refl
·s-assoc neg neg neg = refl


·s-rUnit : (x : Sign) → x ·s pos ≡ x
·s-rUnit x = ·s-comm x pos


-s-·s : (x y : Sign) → (-s x) ·s y ≡ -s (x ·s y)
-s-·s pos _ = refl
-s-·s nul _ = refl
-s-·s neg pos = refl
-s-·s neg nul = refl
-s-·s neg neg = refl


pos≢nul : ¬ pos ≡ nul
pos≢nul p = subst (λ { pos → Unit ; nul → ⊥ ; neg → Unit }) p tt


neg≢nul : ¬ neg ≡ nul
neg≢nul p = subst (λ { pos → Unit ; nul → ⊥ ; neg → Unit }) p tt


data TrichotomySign (x : Sign) : Type where
  ≡pos : x ≡ pos → TrichotomySign x
  ≡nul : x ≡ nul → TrichotomySign x
  ≡neg : x ≡ neg → TrichotomySign x


trichotomySign : (x : Sign) → TrichotomySign x
trichotomySign pos = ≡pos refl
trichotomySign nul = ≡nul refl
trichotomySign neg = ≡neg refl


data DichotomySign (x : Sign) : Type where
  ≡nul : x ≡ nul → DichotomySign x
  ≢nul : ¬ x ≡ nul → DichotomySign x


dichotomySign : (x : Sign) → DichotomySign x
dichotomySign pos = ≢nul pos≢nul
dichotomySign nul = ≡nul refl
dichotomySign neg = ≢nul neg≢nul


integralSign : (x y : Sign) → ¬ x ≡ nul → ¬ y ≡ nul → ¬ (x ·s y) ≡ nul
integralSign pos pos _ _ = pos≢nul
integralSign pos nul _ ¬y≡nul = Empty.rec (¬y≡nul refl)
integralSign pos neg _ _ = neg≢nul
integralSign nul pos ¬x≡nul _ = Empty.rec (¬x≡nul refl)
integralSign nul nul ¬x≡nul _ = Empty.rec (¬x≡nul refl)
integralSign nul neg ¬x≡nul _ = Empty.rec (¬x≡nul refl)
integralSign neg pos _ _ = neg≢nul
integralSign neg nul _ ¬y≡nul = Empty.rec (¬y≡nul refl)
integralSign neg neg _ _ = pos≢nul
