{-

Part of Constructive.Analysis.Reals.PowerSeries.Analytic

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Analytic.Algebra where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Rationals using (ℚ)
open import Cubical.Data.Sigma using (_,_)

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Addition
  using (_+ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
  using (_·ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Negation
  using (-ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.Series
  using (TailBound)
open import Constructive.Analysis.Modulus
  using (AntitoneNatModulus ; maxModulus ; splitModulus)
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Algebra
  using
    ( addPowerSeries
    ; addPowerSeriesOnBallWithMax
    ; negPowerSeries
    ; negPowerSeriesOnBallWith
    ; powerSeriesSumOnBall-addWithMax
    ; powerSeriesSumOnBall-neg
    ; powerSeriesSumOnBall-rationalScale
    ; powerSeriesSumOnBall-realScale
    ; powerSeriesSumOnBall-subWithMax
    ; rationalScaleModulus
    ; rationalScalePowerSeries
    ; rationalScalePowerSeriesOnBallWith
    ; realScaleModulus
    ; realScalePowerSeries
    ; realScalePowerSeriesOnBallWith
    ; subPowerSeries
    ; subPowerSeriesOnBallWithMax
    )
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct
  using
    ( cauchyProductPowerSeries
    ; cauchyProductPowerSeriesOnBallWithFromMajorants
    ; cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTail
    )
open import Constructive.Analysis.Reals.Series.CauchyProduct
  using (sequenceCauchyProduct)
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using
    ( PowerSeriesMajorizedOnBall
    ; majorizedOnBall→hasPowerSeriesOnBallWith
    )
open import Constructive.Analysis.Reals.PowerSeries.Radius
open import Constructive.Data.PositiveRationals

open import Constructive.Analysis.Reals.PowerSeries.Analytic.Base

hasPowerSeriesAtWith-congFunction :
  {f g : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  ((x : ℝᶜ) → f x ≡ g x) →
  HasPowerSeriesAtWith f c a ρ μ →
  HasPowerSeriesAtWith g c a ρ μ
hasPowerSeriesAtWith-congFunction f≡g (convergence , sumPath) =
  convergence ,
  λ x inBall →
    sym (f≡g x) ∙
    sumPath x inBall


hasPowerSeriesAtWith-neg :
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesAtWith f c a ρ μ →
  HasPowerSeriesAtWith
    (λ x → -ᶜ f x)
    c
    (negPowerSeries a)
    ρ
    μ
hasPowerSeriesAtWith-neg {c = c} {a = a} (convergence , sumPath) =
  negPowerSeriesOnBallWith convergence ,
  λ x inBall →
    cong -ᶜ_ (sumPath x inBall) ∙
    sym
      (powerSeriesSumOnBall-neg
        convergence
        (centeredDisplacement c x)
        (InPowerSeriesBall.displacementBound inBall))


hasPowerSeriesAtWith-add :
  {f g : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν : ℚ⁺ → ℕ} →
  HasPowerSeriesAtWith f c a ρ μ →
  HasPowerSeriesAtWith g c b ρ ν →
  HasPowerSeriesAtWith
    (λ x → f x +ᶜ g x)
    c
    (addPowerSeries a b)
    ρ
    (splitModulus (maxModulus μ ν))
hasPowerSeriesAtWith-add
  {c = c}
  {a = a}
  {b = b}
  (leftConvergence , leftPath)
  (rightConvergence , rightPath) =
  addPowerSeriesOnBallWithMax leftConvergence rightConvergence ,
  λ x inBall →
    cong₂ _+ᶜ_ (leftPath x inBall) (rightPath x inBall) ∙
    sym
      (powerSeriesSumOnBall-addWithMax
        leftConvergence
        rightConvergence
        (centeredDisplacement c x)
        (InPowerSeriesBall.displacementBound inBall))


hasPowerSeriesAtWith-sub :
  {f g : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a b : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν : ℚ⁺ → ℕ} →
  HasPowerSeriesAtWith f c a ρ μ →
  HasPowerSeriesAtWith g c b ρ ν →
  HasPowerSeriesAtWith
    (λ x → f x +ᶜ (-ᶜ g x))
    c
    (subPowerSeries a b)
    ρ
    (splitModulus (maxModulus μ ν))
hasPowerSeriesAtWith-sub
  {c = c}
  {a = a}
  {b = b}
  (leftConvergence , leftPath)
  (rightConvergence , rightPath) =
  subPowerSeriesOnBallWithMax leftConvergence rightConvergence ,
  λ x inBall →
    cong₂ _+ᶜ_
      (leftPath x inBall)
      (cong -ᶜ_ (rightPath x inBall)) ∙
    sym
      (powerSeriesSumOnBall-subWithMax
        leftConvergence
        rightConvergence
        (centeredDisplacement c x)
        (InPowerSeriesBall.displacementBound inBall))


hasPowerSeriesAtWith-rationalScale :
  (q : ℚ) →
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesAtWith f c a ρ μ →
  HasPowerSeriesAtWith
    (λ x → rational q ·ᶜ f x)
    c
    (rationalScalePowerSeries q a)
    ρ
    (rationalScaleModulus q μ)
hasPowerSeriesAtWith-rationalScale q {c = c} (convergence , sumPath) =
  rationalScalePowerSeriesOnBallWith q convergence ,
  λ x inBall →
    cong (rational q ·ᶜ_) (sumPath x inBall) ∙
    sym
      (powerSeriesSumOnBall-rationalScale
        q
        convergence
        (centeredDisplacement c x)
        (InPowerSeriesBall.displacementBound inBall))


hasPowerSeriesAtWith-realScale :
  (s : ℝᶜ) →
  (κ : ℚ⁺) →
  BoundedByᶜ κ s →
  {f : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ : ℚ⁺ → ℕ} →
  HasPowerSeriesAtWith f c a ρ μ →
  HasPowerSeriesAtWith
    (λ x → s ·ᶜ f x)
    c
    (realScalePowerSeries s a)
    ρ
    (realScaleModulus κ μ)
hasPowerSeriesAtWith-realScale s κ s-bound {c = c} (convergence , sumPath) =
  realScalePowerSeriesOnBallWith s κ s-bound convergence ,
  λ x inBall →
    cong (s ·ᶜ_) (sumPath x inBall) ∙
    sym
      (powerSeriesSumOnBall-realScale
        s
        κ
        s-bound
        convergence
        (centeredDisplacement c x)
        (InPowerSeriesBall.displacementBound inBall))


hasPowerSeriesAtWith-cauchyProductFromMajorants :
  {f g : ℝᶜ → ℝᶜ} →
  {c : ℝᶜ} →
  {a b A B : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν τ : ℚ⁺ → ℕ} →
  HasPowerSeriesAtWith f c a ρ ν →
  HasPowerSeriesAtWith g c b ρ τ →
  PowerSeriesMajorizedOnBall a ρ A ν →
  PowerSeriesMajorizedOnBall b ρ B τ →
  TailBound (sequenceCauchyProduct A B) μ →
  AntitoneNatModulus μ →
  HasPowerSeriesAtWith
    (λ x → f x ·ᶜ g x)
    c
    (cauchyProductPowerSeries a b)
    ρ
    μ
hasPowerSeriesAtWith-cauchyProductFromMajorants
  {c = c}
  {a = a}
  {b = b}
  {ρ = ρ}
  {μ = μ}
  {ν = ν}
  {τ = τ}
  (leftConvergence , leftPath)
  (rightConvergence , rightPath)
  leftMajorized
  rightMajorized
  productTail
  productAntitone =
  productConvergence ,
  λ x inBall →
    cong₂ _·ᶜ_ (leftPath x inBall) (rightPath x inBall) ∙
    cong₂ _·ᶜ_ (leftDataPath x inBall) (rightDataPath x inBall) ∙
    sym (productPath x inBall)
  where
  leftMajorConvergence :
    HasPowerSeriesOnBallWith a ρ ν
  leftMajorConvergence =
    majorizedOnBall→hasPowerSeriesOnBallWith leftMajorized

  rightMajorConvergence :
    HasPowerSeriesOnBallWith b ρ τ
  rightMajorConvergence =
    majorizedOnBall→hasPowerSeriesOnBallWith rightMajorized

  productConvergence :
    HasPowerSeriesOnBallWith (cauchyProductPowerSeries a b) ρ μ
  productConvergence =
    cauchyProductPowerSeriesOnBallWithFromMajorants
      leftMajorized
      rightMajorized
      productTail
      productAntitone

  leftDataPath :
    (x : ℝᶜ) →
    (inBall : InPowerSeriesBall c ρ x) →
    centeredPowerSeriesSumOnBall a c ρ ν leftConvergence x inBall ≡
    powerSeriesSumOnBall
      a
      ρ
      ν
      leftMajorConvergence
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
  leftDataPath x inBall =
    powerSeriesSumOnBall-data-independent
      leftConvergence
      leftMajorConvergence
      (centeredDisplacement c x)
      h-bound
      h-bound
    where
    h-bound : BoundedByᶜ ρ (centeredDisplacement c x)
    h-bound =
      InPowerSeriesBall.displacementBound inBall

  rightDataPath :
    (x : ℝᶜ) →
    (inBall : InPowerSeriesBall c ρ x) →
    centeredPowerSeriesSumOnBall b c ρ τ rightConvergence x inBall ≡
    powerSeriesSumOnBall
      b
      ρ
      τ
      rightMajorConvergence
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
  rightDataPath x inBall =
    powerSeriesSumOnBall-data-independent
      rightConvergence
      rightMajorConvergence
      (centeredDisplacement c x)
      h-bound
      h-bound
    where
    h-bound : BoundedByᶜ ρ (centeredDisplacement c x)
    h-bound =
      InPowerSeriesBall.displacementBound inBall

  productPath :
    (x : ℝᶜ) →
    (inBall : InPowerSeriesBall c ρ x) →
    powerSeriesSumOnBall
      (cauchyProductPowerSeries a b)
      ρ
      μ
      productConvergence
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
    ≡
    powerSeriesSumOnBall
      a
      ρ
      ν
      leftMajorConvergence
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
    ·ᶜ
    powerSeriesSumOnBall
      b
      ρ
      τ
      rightMajorConvergence
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
  productPath x inBall =
    cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTail
      leftMajorized
      rightMajorized
      productTail
      productAntitone
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)


hasPowerSeriesWithinAtWith-cauchyProductFromMajorants :
  {ℓ : Level} →
  {D : ℝᶜ → Type ℓ} →
  {f g : (x : ℝᶜ) → D x → ℝᶜ} →
  {c : ℝᶜ} →
  {a b A B : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν τ : ℚ⁺ → ℕ} →
  HasPowerSeriesWithinAtWith {D = D} f c a ρ ν →
  HasPowerSeriesWithinAtWith {D = D} g c b ρ τ →
  PowerSeriesMajorizedOnBall a ρ A ν →
  PowerSeriesMajorizedOnBall b ρ B τ →
  TailBound (sequenceCauchyProduct A B) μ →
  AntitoneNatModulus μ →
  HasPowerSeriesWithinAtWith
    {D = D}
    (λ x domain → f x domain ·ᶜ g x domain)
    c
    (cauchyProductPowerSeries a b)
    ρ
    μ
hasPowerSeriesWithinAtWith-cauchyProductFromMajorants
  {D = D}
  {c = c}
  {a = a}
  {b = b}
  {ρ = ρ}
  {μ = μ}
  {ν = ν}
  {τ = τ}
  (leftConvergence , leftPath)
  (rightConvergence , rightPath)
  leftMajorized
  rightMajorized
  productTail
  productAntitone =
  productConvergence ,
  λ x domain inBall →
    cong₂ _·ᶜ_ (leftPath x domain inBall) (rightPath x domain inBall) ∙
    cong₂ _·ᶜ_ (leftDataPath x inBall) (rightDataPath x inBall) ∙
    sym (productPath x inBall)
  where
  leftMajorConvergence :
    HasPowerSeriesOnBallWith a ρ ν
  leftMajorConvergence =
    majorizedOnBall→hasPowerSeriesOnBallWith leftMajorized

  rightMajorConvergence :
    HasPowerSeriesOnBallWith b ρ τ
  rightMajorConvergence =
    majorizedOnBall→hasPowerSeriesOnBallWith rightMajorized

  productConvergence :
    HasPowerSeriesOnBallWith (cauchyProductPowerSeries a b) ρ μ
  productConvergence =
    cauchyProductPowerSeriesOnBallWithFromMajorants
      leftMajorized
      rightMajorized
      productTail
      productAntitone

  leftDataPath :
    (x : ℝᶜ) →
    (inBall : InPowerSeriesBall c ρ x) →
    centeredPowerSeriesSumOnBall a c ρ ν leftConvergence x inBall ≡
    powerSeriesSumOnBall
      a
      ρ
      ν
      leftMajorConvergence
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
  leftDataPath x inBall =
    powerSeriesSumOnBall-data-independent
      leftConvergence
      leftMajorConvergence
      (centeredDisplacement c x)
      h-bound
      h-bound
    where
    h-bound : BoundedByᶜ ρ (centeredDisplacement c x)
    h-bound =
      InPowerSeriesBall.displacementBound inBall

  rightDataPath :
    (x : ℝᶜ) →
    (inBall : InPowerSeriesBall c ρ x) →
    centeredPowerSeriesSumOnBall b c ρ τ rightConvergence x inBall ≡
    powerSeriesSumOnBall
      b
      ρ
      τ
      rightMajorConvergence
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
  rightDataPath x inBall =
    powerSeriesSumOnBall-data-independent
      rightConvergence
      rightMajorConvergence
      (centeredDisplacement c x)
      h-bound
      h-bound
    where
    h-bound : BoundedByᶜ ρ (centeredDisplacement c x)
    h-bound =
      InPowerSeriesBall.displacementBound inBall

  productPath :
    (x : ℝᶜ) →
    (inBall : InPowerSeriesBall c ρ x) →
    powerSeriesSumOnBall
      (cauchyProductPowerSeries a b)
      ρ
      μ
      productConvergence
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
    ≡
    powerSeriesSumOnBall
      a
      ρ
      ν
      leftMajorConvergence
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
    ·ᶜ
    powerSeriesSumOnBall
      b
      ρ
      τ
      rightMajorConvergence
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
  productPath x inBall =
    cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTail
      leftMajorized
      rightMajorized
      productTail
      productAntitone
      (centeredDisplacement c x)
      (InPowerSeriesBall.displacementBound inBall)
