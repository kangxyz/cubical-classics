{-

Formal derivatives and primitives of power-series coefficients

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Differentiation where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Base
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Magnitude
  using (neg-zeroᶜ)
open import Constructive.Analysis.Reals.Series.Instances.Geometric.Real
  using (realPower)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( addPowerSeries
    ; constantPowerSeries
    ; negPowerSeries
    ; rationalScalePowerSeries
    ; subPowerSeries
    ; zeroPowerSeries
    )
import Constructive.Data.Rationals as Rational


naturalReal :
  ℕ →
  ℝᶜ
naturalReal n =
  rational (Rational.natMul n Rational.1ℚ)


inverseSucReal :
  ℕ →
  ℝᶜ
inverseSucReal n =
  rational (Rational.divideBySuc Rational.1ℚ n)


derivativePowerSeries :
  PowerSeries →
  PowerSeries
derivativePowerSeries a n =
  naturalReal (suc n) ·ᶜ a (suc n)


primitivePowerSeries :
  PowerSeries →
  PowerSeries
primitivePowerSeries a zero =
  0ᶜ
primitivePowerSeries a (suc n) =
  inverseSucReal n ·ᶜ a n


derivativePowerSeriesCoefficient :
  (a : PowerSeries) →
  (n : ℕ) →
  derivativePowerSeries a n ≡ naturalReal (suc n) ·ᶜ a (suc n)
derivativePowerSeriesCoefficient a n =
  refl


primitivePowerSeriesCoefficient-zero :
  (a : PowerSeries) →
  primitivePowerSeries a zero ≡ 0ᶜ
primitivePowerSeriesCoefficient-zero a =
  refl


primitivePowerSeriesCoefficient-suc :
  (a : PowerSeries) →
  (n : ℕ) →
  primitivePowerSeries a (suc n) ≡ inverseSucReal n ·ᶜ a n
primitivePowerSeriesCoefficient-suc a n =
  refl


derivativePowerSeriesTerm :
  (a : PowerSeries) →
  (h : ℝᶜ) →
  (n : ℕ) →
  powerSeriesTerm (derivativePowerSeries a) h n ≡
  naturalReal (suc n) ·ᶜ powerSeriesTerm (λ k → a (suc k)) h n
derivativePowerSeriesTerm a h n =
  sym (mulᶜ-assoc
    (naturalReal (suc n))
    (a (suc n))
    (realPower h n))


derivativePowerSeries-zero :
  (n : ℕ) →
  derivativePowerSeries zeroPowerSeries n ≡ zeroPowerSeries n
derivativePowerSeries-zero n =
  mulᶜ-zero-right (naturalReal (suc n))


derivativePowerSeries-constant :
  (c : ℝᶜ) →
  (n : ℕ) →
  derivativePowerSeries (constantPowerSeries c) n ≡ zeroPowerSeries n
derivativePowerSeries-constant c n =
  mulᶜ-zero-right (naturalReal (suc n))


derivativePowerSeries-add :
  (a b : PowerSeries) →
  (n : ℕ) →
  derivativePowerSeries (addPowerSeries a b) n ≡
  addPowerSeries (derivativePowerSeries a) (derivativePowerSeries b) n
derivativePowerSeries-add a b n =
  mulᶜ-distrib-right
    (naturalReal (suc n))
    (a (suc n))
    (b (suc n))


derivativePowerSeries-neg :
  (a : PowerSeries) →
  (n : ℕ) →
  derivativePowerSeries (negPowerSeries a) n ≡
  negPowerSeries (derivativePowerSeries a) n
derivativePowerSeries-neg a n =
  mulᶜ-neg-right (naturalReal (suc n)) (a (suc n))


derivativePowerSeries-sub :
  (a b : PowerSeries) →
  (n : ℕ) →
  derivativePowerSeries (subPowerSeries a b) n ≡
  subPowerSeries (derivativePowerSeries a) (derivativePowerSeries b) n
derivativePowerSeries-sub a b n =
  derivativePowerSeries-add a (negPowerSeries b) n ∙
  cong
    (λ f → addPowerSeries (derivativePowerSeries a) f n)
    (funExt (derivativePowerSeries-neg b))


derivativePowerSeries-rationalScale :
  (q : ℚ) →
  (a : PowerSeries) →
  (n : ℕ) →
  derivativePowerSeries (rationalScalePowerSeries q a) n ≡
  rationalScalePowerSeries q (derivativePowerSeries a) n
derivativePowerSeries-rationalScale q a n =
  mulᶜ-assoc
    (naturalReal (suc n))
    (rational q)
    (a (suc n)) ∙
  cong
    (_·ᶜ a (suc n))
    (mulᶜ-comm (naturalReal (suc n)) (rational q)) ∙
  sym
    (mulᶜ-assoc
      (rational q)
      (naturalReal (suc n))
      (a (suc n)))


naturalTimesInverseSuc≡one :
  (n : ℕ) →
  Rational.natMul (suc n) Rational.1ℚ
    ℚ.· Rational.divideBySuc Rational.1ℚ n
  ≡ Rational.1ℚ
naturalTimesInverseSuc≡one n =
  ℚ.·Comm natural inverse ∙
  sym (Rational.natMul-mul-left (suc n) inverse Rational.1ℚ) ∙
  cong (Rational.natMul (suc n)) (ℚ.·IdR inverse) ∙
  Rational.natMul-divideBySuc Rational.1ℚ n
  where
  natural : ℚ
  natural =
    Rational.natMul (suc n) Rational.1ℚ

  inverse : ℚ
  inverse =
    Rational.divideBySuc Rational.1ℚ n


naturalTimesInverseSucReal-cancel :
  (n : ℕ) →
  (x : ℝᶜ) →
  naturalReal (suc n) ·ᶜ (inverseSucReal n ·ᶜ x) ≡ x
naturalTimesInverseSucReal-cancel n x =
  mulᶜ-assoc-rational-left natural inverseReal x ∙
  cong
    (_·ᶜ x)
    (mulᶜ-rational-rational natural inverse ∙
     cong rational (naturalTimesInverseSuc≡one n)) ∙
  mulᶜ-one-left x
  where
  natural : ℚ
  natural =
    Rational.natMul (suc n) Rational.1ℚ

  inverse : ℚ
  inverse =
    Rational.divideBySuc Rational.1ℚ n

  inverseReal : ℝᶜ
  inverseReal =
    inverseSucReal n


derivativePrimitivePowerSeries :
  (a : PowerSeries) →
  (n : ℕ) →
  derivativePowerSeries (primitivePowerSeries a) n ≡ a n
derivativePrimitivePowerSeries a n =
  naturalTimesInverseSucReal-cancel n (a n)


inverseSucTimesNatural≡one :
  (n : ℕ) →
  Rational.divideBySuc Rational.1ℚ n
    ℚ.· Rational.natMul (suc n) Rational.1ℚ
  ≡ Rational.1ℚ
inverseSucTimesNatural≡one n =
  ℚ.·Comm inverse natural ∙
  naturalTimesInverseSuc≡one n
  where
  natural : ℚ
  natural =
    Rational.natMul (suc n) Rational.1ℚ

  inverse : ℚ
  inverse =
    Rational.divideBySuc Rational.1ℚ n


primitiveDerivativePowerSeries-suc :
  (a : PowerSeries) →
  (n : ℕ) →
  primitivePowerSeries (derivativePowerSeries a) (suc n) ≡ a (suc n)
primitiveDerivativePowerSeries-suc a n =
  mulᶜ-assoc-rational-left inverse naturalRealₙ (a (suc n)) ∙
  cong
    (_·ᶜ a (suc n))
    (mulᶜ-rational-rational inverse natural ∙
     cong rational (inverseSucTimesNatural≡one n)) ∙
  mulᶜ-one-left (a (suc n))
  where
  natural : ℚ
  natural =
    Rational.natMul (suc n) Rational.1ℚ

  inverse : ℚ
  inverse =
    Rational.divideBySuc Rational.1ℚ n

  naturalRealₙ : ℝᶜ
  naturalRealₙ =
    naturalReal (suc n)


primitiveDerivativePowerSeries :
  (a : PowerSeries) →
  (n : ℕ) →
  primitivePowerSeries (derivativePowerSeries a) n ≡
  subPowerSeries a (constantPowerSeries (a zero)) n
primitiveDerivativePowerSeries a zero =
  sym (add-inverse-right (a zero))
primitiveDerivativePowerSeries a (suc n) =
  primitiveDerivativePowerSeries-suc a n ∙
  sym
    (cong
      (a (suc n) +ᶜ_)
      neg-zeroᶜ ∙
    add-zero-right (a (suc n)))


primitivePowerSeries-zero :
  (n : ℕ) →
  primitivePowerSeries zeroPowerSeries n ≡ zeroPowerSeries n
primitivePowerSeries-zero zero =
  refl
primitivePowerSeries-zero (suc n) =
  mulᶜ-zero-right (inverseSucReal n)


primitivePowerSeries-add :
  (a b : PowerSeries) →
  (n : ℕ) →
  primitivePowerSeries (addPowerSeries a b) n ≡
  addPowerSeries (primitivePowerSeries a) (primitivePowerSeries b) n
primitivePowerSeries-add a b zero =
  sym (add-zero-left 0ᶜ)
primitivePowerSeries-add a b (suc n) =
  mulᶜ-distrib-right
    (inverseSucReal n)
    (a n)
    (b n)


primitivePowerSeries-neg :
  (a : PowerSeries) →
  (n : ℕ) →
  primitivePowerSeries (negPowerSeries a) n ≡
  negPowerSeries (primitivePowerSeries a) n
primitivePowerSeries-neg a zero =
  sym neg-zeroᶜ
primitivePowerSeries-neg a (suc n) =
  mulᶜ-neg-right (inverseSucReal n) (a n)


primitivePowerSeries-sub :
  (a b : PowerSeries) →
  (n : ℕ) →
  primitivePowerSeries (subPowerSeries a b) n ≡
  subPowerSeries (primitivePowerSeries a) (primitivePowerSeries b) n
primitivePowerSeries-sub a b n =
  primitivePowerSeries-add a (negPowerSeries b) n ∙
  cong
    (λ f → addPowerSeries (primitivePowerSeries a) f n)
    (funExt (primitivePowerSeries-neg b))


primitivePowerSeries-rationalScale :
  (q : ℚ) →
  (a : PowerSeries) →
  (n : ℕ) →
  primitivePowerSeries (rationalScalePowerSeries q a) n ≡
  rationalScalePowerSeries q (primitivePowerSeries a) n
primitivePowerSeries-rationalScale q a zero =
  sym (mulᶜ-zero-right (rational q))
primitivePowerSeries-rationalScale q a (suc n) =
  mulᶜ-assoc
    (inverseSucReal n)
    (rational q)
    (a n) ∙
  cong
    (_·ᶜ a n)
    (mulᶜ-comm (inverseSucReal n) (rational q)) ∙
  sym
    (mulᶜ-assoc
      (rational q)
      (inverseSucReal n)
      (a n))
