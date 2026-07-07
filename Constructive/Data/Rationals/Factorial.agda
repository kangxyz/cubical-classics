{-

Rational reciprocal factorial coefficients

-}
{-# OPTIONS --safe #-}
module Constructive.Data.Rationals.Factorial where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder

open import Constructive.Data.Nat.Factorial
  using (factorial)
import Constructive.Data.Rationals.Base as RationalBase
import Constructive.Data.Rationals.Archimedean as RationalArch
import Constructive.Data.Rationals.Inverse as RationalInverse
import Constructive.Data.Rationals.Multiplication as RationalMul


naturalOne≤ :
  (n : ℕ) →
  RationalBase.1ℚ ℚOrder.≤
  RationalArch.natMul (suc n) RationalBase.1ℚ
naturalOne≤ zero =
  subst
    (λ q → RationalBase.1ℚ ℚOrder.≤ q)
    (sym (RationalArch.natMul-one RationalBase.1ℚ))
    (RationalBase.≤-refl RationalBase.1ℚ)
naturalOne≤ (suc n) =
  RationalBase.≤-trans
    {p = RationalBase.1ℚ}
    {q = RationalArch.natMul (suc n) RationalBase.1ℚ}
    {r = RationalArch.natMul (suc (suc n)) RationalBase.1ℚ}
    (naturalOne≤ n)
    (RationalArch.natMul-step≤
      (suc n)
      {ε = RationalBase.1ℚ}
      RationalBase.0<1)


unitFraction≤1 :
  (n : ℕ) →
  RationalArch.unitFraction n ℚOrder.≤ RationalBase.1ℚ
unitFraction≤1 n =
  RationalInverse.mul-right-cancel-positive-≤
    {p = unit}
    {q = RationalBase.1ℚ}
    {c = natural}
    natural-positive
    unit-natural≤one-natural
  where
  unit : ℚ
  unit =
    RationalArch.unitFraction n

  natural : ℚ
  natural =
    RationalArch.natMul (suc n) RationalBase.1ℚ

  natural-positive : RationalBase.0ℚ ℚOrder.< natural
  natural-positive =
    RationalArch.natMul-suc-positive n RationalBase.0<1

  divideBySuc≡unit :
    RationalArch.divideBySuc RationalBase.1ℚ n ≡ unit
  divideBySuc≡unit =
    RationalArch.divideBySuc-as-unitFraction RationalBase.1ℚ n ∙
    ℚ.·IdL unit

  natMul-unit≡one :
    RationalArch.natMul (suc n) unit ≡ RationalBase.1ℚ
  natMul-unit≡one =
    cong (RationalArch.natMul (suc n)) (sym divideBySuc≡unit) ∙
    RationalArch.natMul-divideBySuc RationalBase.1ℚ n

  unit-times-natural≡one :
    unit ℚ.· natural ≡ RationalBase.1ℚ
  unit-times-natural≡one =
    sym (RationalArch.natMul-mul-left (suc n) unit RationalBase.1ℚ) ∙
    cong (RationalArch.natMul (suc n)) (ℚ.·IdR unit) ∙
    natMul-unit≡one

  one-times-natural≡natural :
    RationalBase.1ℚ ℚ.· natural ≡ natural
  one-times-natural≡natural =
    ℚ.·IdL natural

  unit-natural≤one-natural :
    unit ℚ.· natural ℚOrder.≤ RationalBase.1ℚ ℚ.· natural
  unit-natural≤one-natural =
    subst2
      ℚOrder._≤_
      (sym unit-times-natural≡one)
      (sym one-times-natural≡natural)
      (naturalOne≤ n)


factorialRational :
  ℕ →
  ℚ
factorialRational n =
  RationalArch.natMul (factorial n) RationalBase.1ℚ


reciprocalFactorial :
  ℕ →
  ℚ
reciprocalFactorial zero =
  RationalBase.1ℚ
reciprocalFactorial (suc n) =
  RationalArch.divideBySuc (reciprocalFactorial n) n


reciprocalFactorial-zero :
  reciprocalFactorial zero ≡ RationalBase.1ℚ
reciprocalFactorial-zero =
  refl


reciprocalFactorial-suc :
  (n : ℕ) →
  reciprocalFactorial (suc n) ≡
  RationalArch.divideBySuc (reciprocalFactorial n) n
reciprocalFactorial-suc n =
  refl


reciprocalFactorial-positive :
  (n : ℕ) →
  RationalBase.0ℚ ℚOrder.< reciprocalFactorial n
reciprocalFactorial-positive zero =
  RationalBase.0<1
reciprocalFactorial-positive (suc n) =
  RationalArch.divideBySuc-positive
    {q = reciprocalFactorial n}
    (reciprocalFactorial-positive n)
    n


reciprocalFactorial≤1 :
  (n : ℕ) →
  reciprocalFactorial n ℚOrder.≤ RationalBase.1ℚ
reciprocalFactorial≤1 zero =
  RationalBase.≤-refl RationalBase.1ℚ
reciprocalFactorial≤1 (suc n) =
  RationalBase.≤-trans
    {p = reciprocalFactorial (suc n)}
    {q = RationalArch.unitFraction n}
    {r = RationalBase.1ℚ}
    reciprocal-step≤unit
    (unitFraction≤1 n)
  where
  reciprocal : ℚ
  reciprocal =
    reciprocalFactorial n

  unit : ℚ
  unit =
    RationalArch.unitFraction n

  reciprocal-nonnegative :
    RationalBase.0ℚ ℚOrder.≤ reciprocal
  reciprocal-nonnegative =
    RationalBase.<→≤
      {p = RationalBase.0ℚ}
      {q = reciprocal}
      (reciprocalFactorial-positive n)

  divideBySuc≡mul-unit :
    reciprocalFactorial (suc n) ≡ reciprocal ℚ.· unit
  divideBySuc≡mul-unit =
    RationalArch.divideBySuc-as-unitFraction reciprocal n

  reciprocal-unit≤unit :
    reciprocal ℚ.· unit ℚOrder.≤ RationalBase.1ℚ ℚ.· unit
  reciprocal-unit≤unit =
    ℚOrder.≤-·o
      reciprocal
      RationalBase.1ℚ
      unit
      (RationalBase.<→≤
        {p = RationalBase.0ℚ}
        {q = unit}
        (RationalArch.unitFraction-positive n))
      (reciprocalFactorial≤1 n)

  reciprocal-step≤unit :
    reciprocalFactorial (suc n) ℚOrder.≤ unit
  reciprocal-step≤unit =
    subst2
      ℚOrder._≤_
      (sym divideBySuc≡mul-unit)
      (ℚ.·IdL unit)
      reciprocal-unit≤unit


reciprocalFactorial-cancel-suc :
  (n : ℕ) →
  RationalArch.natMul (suc n) RationalBase.1ℚ
    ℚ.· reciprocalFactorial (suc n)
  ≡ reciprocalFactorial n
reciprocalFactorial-cancel-suc n =
  ℚ.·Comm natural reciprocal ∙
  sym (RationalArch.natMul-mul-left (suc n) reciprocal RationalBase.1ℚ) ∙
  cong (RationalArch.natMul (suc n)) (ℚ.·IdR reciprocal) ∙
  RationalArch.natMul-divideBySuc (reciprocalFactorial n) n
  where
  natural : ℚ
  natural =
    RationalArch.natMul (suc n) RationalBase.1ℚ

  reciprocal : ℚ
  reciprocal =
    reciprocalFactorial (suc n)


divideByFactorial :
  ℚ →
  ℕ →
  ℚ
divideByFactorial q n =
  q ℚ.· reciprocalFactorial n


divideByFactorial-one :
  (n : ℕ) →
  divideByFactorial RationalBase.1ℚ n ≡ reciprocalFactorial n
divideByFactorial-one n =
  ℚ.·IdL (reciprocalFactorial n)


divideByFactorial-zero :
  (q : ℚ) →
  divideByFactorial q zero ≡ q
divideByFactorial-zero q =
  ℚ.·IdR q
