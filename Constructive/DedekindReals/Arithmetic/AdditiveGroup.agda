{-

Additive group lemmas for constructive Dedekind reals

The later multiplication laws reuse these ordinary abelian-group calculations.

-}
{-# OPTIONS --safe #-}
module Constructive.DedekindReals.Arithmetic.AdditiveGroup where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Constructive.DedekindReals
open import Constructive.DedekindReals.Arithmetic.Base


module AdditiveGroup {ℓ : Level} where
  open Algebra {ℓ}
  open Addition {ℓ}

  DedekindAbGroup : AbGroup (ℓ-suc ℓ)
  DedekindAbGroup =
    makeAbGroup 0𝔻 _+_ (-_) isSetDedekindReal
      +-assoc +-idR +-invR +-comm

  module DedekindAbGroupTheory = AbGroupTheory DedekindAbGroup
  module DedekindGroupTheory = GroupTheory (AbGroup→Group DedekindAbGroup)

  +-interchange :
    (a b c d : DedekindReal ℓ) →
    (a + b) + (c + d) ≡ (a + c) + (b + d)
  +-interchange =
    DedekindAbGroupTheory.comm-4

  +-cancelR :
    (x y z : DedekindReal ℓ) →
    x + z ≡ y + z →
    x ≡ y
  +-cancelR x y z =
    DedekindGroupTheory.·CancelR z

  +-cancelL :
    (x y z : DedekindReal ℓ) →
    z + x ≡ z + y →
    x ≡ y
  +-cancelL x y z =
    DedekindGroupTheory.·CancelL z

  inverse-uniqueR :
    (x y : DedekindReal ℓ) →
    x + y ≡ 0𝔻 →
    - x ≡ y
  inverse-uniqueR x y x+y≡0 =
    sym (DedekindGroupTheory.invUniqueR x+y≡0)

  inverse-uniqueL :
    (x y : DedekindReal ℓ) →
    y + x ≡ 0𝔻 →
    - x ≡ y
  inverse-uniqueL x y y+x≡0 =
    sym (DedekindGroupTheory.invUniqueL y+x≡0)

  neg-add :
    (a b : DedekindReal ℓ) →
    - (a + b) ≡ (- a) + (- b)
  neg-add a b =
    DedekindGroupTheory.invDistr a b ∙
    +-comm (- b) (- a)

  neg-difference-swap :
    (a b : DedekindReal ℓ) →
    - (a + (- b)) ≡ b + (- a)
  neg-difference-swap a b =
    neg-add a (- b) ∙
    cong₂ _+_ refl (neg-involutive b) ∙
    +-comm (- a) b

  difference-neg-swap :
    (a b : DedekindReal ℓ) →
    a + (- b) ≡ - (b + (- a))
  difference-neg-swap a b =
    sym (neg-difference-swap b a)

  plus-minus-cancelR :
    (x n : DedekindReal ℓ) →
    (x + n) + (- n) ≡ x
  plus-minus-cancelR x n =
    sym (+-assoc x n (- n)) ∙
    cong (x +_) (+-invR n) ∙
    +-idR x

  minus-plus-cancelR :
    (x n : DedekindReal ℓ) →
    (x + (- n)) + n ≡ x
  minus-plus-cancelR x n =
    sym (+-assoc x (- n) n) ∙
    cong (x +_) (+-invL n) ∙
    +-idR x

  sum-differences :
    (a b c d : DedekindReal ℓ) →
    (a + (- b)) + (c + (- d)) ≡ (a + c) + (- (b + d))
  sum-differences a b c d =
    +-interchange a (- b) c (- d) ∙
    cong ((a + c) +_) (sym (neg-add b d))

  difference-eq→cross-sum :
    (a b c d : DedekindReal ℓ) →
    a + (- b) ≡ c + (- d) →
    a + d ≡ c + b
  difference-eq→cross-sum a b c d diff-path =
    sym left-normal ∙
    cong (_+ (b + d)) diff-path ∙
    right-normal
    where
    left-normal :
      (a + (- b)) + (b + d) ≡ a + d
    left-normal =
      +-assoc (a + (- b)) b d ∙
      cong (_+ d) (minus-plus-cancelR a b)

    right-normal :
      (c + (- d)) + (b + d) ≡ c + b
    right-normal =
      +-interchange c (- d) b d ∙
      cong ((c + b) +_) (+-invL d) ∙
      +-idR (c + b)

  cross-sum→difference-eq :
    (a b c d : DedekindReal ℓ) →
    a + d ≡ c + b →
    a + (- b) ≡ c + (- d)
  cross-sum→difference-eq a b c d cross-path =
    sym left-normal ∙
    cong (_+ ((- b) + (- d))) cross-path ∙
    right-normal
    where
    left-normal :
      (a + d) + ((- b) + (- d)) ≡ a + (- b)
    left-normal =
      +-interchange a d (- b) (- d) ∙
      cong ((a + (- b)) +_) (+-invR d) ∙
      +-idR (a + (- b))

    right-normal :
      (c + b) + ((- b) + (- d)) ≡ c + (- d)
    right-normal =
      +-assoc (c + b) (- b) (- d) ∙
      cong (_+ (- d)) (plus-minus-cancelR c b)
