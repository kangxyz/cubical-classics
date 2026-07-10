{-

Coefficient estimates for strict-subball re-centering.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Recenter.CoefficientBounds where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Tactics.CommRingSolver.Reflection

open import Constructive.Analysis.GeometricDecay
  using (positivePower ; positivePower-radius)
open import Constructive.Analysis.GeometricDecay.Rational
  using (rationalPower)
open import Constructive.Analysis.Reals.PowerSeries.DerivativeConvergence.Estimates
  using
    ( derivativeStrictSubballRatio
    ; derivativeStrictSubballRatio<1
    ; ratioPowerTimesScalePower
    )
open import Constructive.Analysis.Reals.PowerSeries.Recenter.Binomial
  using (binomialℕ)
open import Constructive.Analysis.Reals.PowerSeries.Recenter.BinomialGeometric
  using
    ( binomialGeometricBoundScale
    ; binomialGeometricWeight-path
    ; binomialGeometricWeight≤scale
    )
open import Constructive.Data.PositiveRationals
  using (ℚ⁺ ; radius ; _*⁺_ ; posInv⁺)
import Constructive.Data.Rationals as Rational


private
  module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
    open CommRingStr (𝓡 .snd)

    coefficient-cancel-form :
      (B i d s : 𝓡 .fst) →
      ((B · i) · d) · s ≡ B · ((i · s) · d)
    coefficient-cancel-form _ _ _ _ = solve! 𝓡

    scale-cancel-form :
      (i C sn sk : 𝓡 .fst) →
      (i · C) · (sn · sk) ≡ (i · sn) · (C · sk)
    scale-cancel-form _ _ _ _ = solve! 𝓡


rationalPower-add :
  (r : ℚ) →
  (m n : ℕ) →
  rationalPower r (m Nat.+ n) ≡
  rationalPower r m ℚ.· rationalPower r n
rationalPower-add r zero n =
  sym (ℚ.·IdL (rationalPower r n))
rationalPower-add r (suc m) n =
  cong (r ℚ.·_) (rationalPower-add r m n) ∙
  ℚ.·Assoc
    r
    (rationalPower r m)
    (rationalPower r n)


positivePower-add-radius :
  (ρ : ℚ⁺) →
  (m n : ℕ) →
  radius (positivePower ρ (m Nat.+ n)) ≡
  radius (positivePower ρ m) ℚ.· radius (positivePower ρ n)
positivePower-add-radius ρ m n =
  positivePower-radius ρ (m Nat.+ n) ∙
  rationalPower-add (radius ρ) m n ∙
  cong₂
    (λ x y → x ℚ.· y)
    (sym (positivePower-radius ρ m))
    (sym (positivePower-radius ρ n))


recenterCoefficientScale :
  (δ σ : ℚ⁺) →
  radius δ ℚOrder.< radius σ →
  ℕ →
  ℚ⁺
recenterCoefficientScale δ σ δ<σ n =
  posInv⁺ (positivePower σ n) *⁺
  binomialGeometricBoundScale
    (derivativeStrictSubballRatio δ σ)
    (derivativeStrictSubballRatio<1 {ρ = δ} {σ = σ} δ<σ)
    n


recenterCoefficientWeight≤Scale :
  (δ σ : ℚ⁺) →
  (δ<σ : radius δ ℚOrder.< radius σ) →
  (n k : ℕ) →
  ((Rational.natMul (binomialℕ (n Nat.+ k) n) Rational.1ℚ ℚ.·
    radius (posInv⁺ (positivePower σ (n Nat.+ k)))) ℚ.·
    radius (positivePower δ k))
    ℚOrder.≤
  radius (recenterCoefficientScale δ σ δ<σ n)
recenterCoefficientWeight≤Scale δ σ δ<σ n k =
  Rational.mul-right-cancel-positive-≤
    {p = coeff}
    {q = scale}
    {c = σpowNK}
    (positivePower σ (n Nat.+ k) .snd)
    coeffσ≤scaleσ
  where
  q : ℚ⁺
  q =
    derivativeStrictSubballRatio δ σ

  q<1 : radius q ℚOrder.< Rational.1ℚ
  q<1 =
    derivativeStrictSubballRatio<1 {ρ = δ} {σ = σ} δ<σ

  B : ℚ
  B =
    Rational.natMul (binomialℕ (n Nat.+ k) n) Rational.1ℚ

  invσNK : ℚ
  invσNK =
    radius (posInv⁺ (positivePower σ (n Nat.+ k)))

  δpow : ℚ
  δpow =
    radius (positivePower δ k)

  σpowN : ℚ
  σpowN =
    radius (positivePower σ n)

  σpowK : ℚ
  σpowK =
    radius (positivePower σ k)

  σpowNK : ℚ
  σpowNK =
    radius (positivePower σ (n Nat.+ k))

  invσN : ℚ
  invσN =
    radius (posInv⁺ (positivePower σ n))

  C : ℚ
  C =
    radius (binomialGeometricBoundScale q q<1 n)

  coeff : ℚ
  coeff =
    (B ℚ.· invσNK) ℚ.· δpow

  scale : ℚ
  scale =
    radius (recenterCoefficientScale δ σ δ<σ n)

  qpow : ℚ
  qpow =
    rationalPower (radius q) k

  left-path :
    coeff ℚ.· σpowNK ≡ B ℚ.· δpow
  left-path =
    SolverHelpers.coefficient-cancel-form
      ℚCommRing
      B
      invσNK
      δpow
      σpowNK ∙
    cong
      (λ x → B ℚ.· (x ℚ.· δpow))
      (Rational.posInv-left
        σpowNK
        (positivePower σ (n Nat.+ k) .snd)) ∙
    cong (B ℚ.·_) (ℚ.·IdL δpow)

  right-path :
    scale ℚ.· σpowNK ≡ C ℚ.· σpowK
  right-path =
    cong (scale ℚ.·_) (positivePower-add-radius σ n k) ∙
    SolverHelpers.scale-cancel-form
      ℚCommRing
      invσN
      C
      σpowN
      σpowK ∙
    cong
      (λ x → x ℚ.· (C ℚ.· σpowK))
      (Rational.posInv-left σpowN (positivePower σ n .snd)) ∙
    ℚ.·IdL (C ℚ.· σpowK)

  weight≤C :
    B ℚ.· qpow ℚOrder.≤ C
  weight≤C =
    subst
      (λ x → x ℚOrder.≤ C)
      (binomialGeometricWeight-path q n k)
      (binomialGeometricWeight≤scale q q<1 n k)

  σpowK-nonnegative : Rational.0ℚ ℚOrder.≤ σpowK
  σpowK-nonnegative =
    Rational.<→≤
      {p = Rational.0ℚ}
      {q = σpowK}
      (positivePower σ k .snd)

  scaled-weight≤ :
    (B ℚ.· qpow) ℚ.· σpowK ℚOrder.≤ C ℚ.· σpowK
  scaled-weight≤ =
    ℚOrder.≤-·o
      (B ℚ.· qpow)
      C
      σpowK
      σpowK-nonnegative
      weight≤C

  ratio-path :
    (B ℚ.· qpow) ℚ.· σpowK ≡ B ℚ.· δpow
  ratio-path =
    sym (ℚ.·Assoc B qpow σpowK) ∙
    cong
      (B ℚ.·_)
      (ratioPowerTimesScalePower δ σ k)

  scaled≤ :
    B ℚ.· δpow ℚOrder.≤ C ℚ.· σpowK
  scaled≤ =
    subst
      (λ x → x ℚOrder.≤ C ℚ.· σpowK)
      ratio-path
      scaled-weight≤

  coeffσ≤scaleσ :
    coeff ℚ.· σpowNK ℚOrder.≤ scale ℚ.· σpowNK
  coeffσ≤scaleσ =
    subst2
      ℚOrder._≤_
      (sym left-path)
      (sym right-path)
      scaled≤
