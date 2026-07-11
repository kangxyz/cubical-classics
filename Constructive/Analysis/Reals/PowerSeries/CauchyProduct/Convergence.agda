{-

Cauchy-product convergence from power-series majorants

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Convergence where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)

open import Constructive.Analysis.Modulus using (AntitoneNatModulus)
open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.Multiplication
  using (_·ᶜ_)
open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  using (BoundedByᶜ)
open import Constructive.Analysis.Reals.Series
  using
    ( SeriesMajorizedBy
    ; TailBound
    ; seriesSumFromFiniteTailBound
    ; seriesSumFromFiniteTailBoundConvergesTo
    )
open import Constructive.Analysis.Reals.PowerSeries.Base
open import Constructive.Analysis.Reals.PowerSeries.Radius
  using
    ( HasPowerSeriesOnBallWith
    ; hasPowerSeriesOnBallWith
    ; powerSeriesSumOnBall
    )
open import Constructive.Analysis.Reals.PowerSeries.Majorant
  using
    ( PowerSeriesMajorizedOnBall
    ; majorizedOnBall→hasPowerSeriesOnBallWith
    )
open import Constructive.Data.PositiveRationals

import Constructive.Analysis.Reals.Sequences.Convergence as SeqConv

open import Constructive.Analysis.Reals.Series.CauchyProduct.Finite
  using (sequenceCauchyProduct)
open import Constructive.Analysis.Reals.Series.CauchyProduct.Convergence
  using (seriesSumFromFiniteTailBound-cong)
open import Constructive.Analysis.Reals.Series.CauchyProduct.Majorant
  using
    ( sequenceCauchyProductMajorizedBy
    ; sequenceCauchyProductTailBoundFromMajorant
    )
open import Constructive.Analysis.Reals.Series.CauchyProduct.ProductOfSums
  using (sequenceCauchyProductSumProductFromMajorantProductTail)
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.TermBridge
  using (cauchyProductPowerSeriesTerm-sequenceCauchyProduct)
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Coefficients
  using (cauchyProductPowerSeries)


private
  seriesSumFromFiniteTailBound-data-independent :
    {u : ℕ → ℝᶜ} →
    {μ : ℚ⁺ → ℕ} →
    (leftTail rightTail : TailBound u μ) →
    (leftAntitone rightAntitone : AntitoneNatModulus μ) →
    seriesSumFromFiniteTailBound u μ leftTail leftAntitone ≡
    seriesSumFromFiniteTailBound u μ rightTail rightAntitone
  seriesSumFromFiniteTailBound-data-independent
    {u = u}
    {μ = μ}
    leftTail
    rightTail
    leftAntitone
    rightAntitone =
    SeqConv.convergesToPath
      (seriesSumFromFiniteTailBoundConvergesTo
        u
        μ
        leftTail
        leftAntitone)
      (seriesSumFromFiniteTailBoundConvergesTo
        u
        μ
        rightTail
        rightAntitone)


cauchyProductPowerSeriesOnBallWithFromMajorants :
  {a b A B : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν τ : ℚ⁺ → ℕ} →
  PowerSeriesMajorizedOnBall a ρ A ν →
  PowerSeriesMajorizedOnBall b ρ B τ →
  TailBound (sequenceCauchyProduct A B) μ →
  AntitoneNatModulus μ →
  HasPowerSeriesOnBallWith (cauchyProductPowerSeries a b) ρ μ
cauchyProductPowerSeriesOnBallWithFromMajorants
  {a = a}
  {b = b}
  {ρ = ρ}
  {μ = μ}
  left
  right
  productTail
  productAntitone =
  hasPowerSeriesOnBallWith productAntitone productTailAt
  where
  productTailAt :
    (h : ℝᶜ) →
    BoundedByᶜ ρ h →
    TailBound (powerSeriesTerm (cauchyProductPowerSeries a b) h) μ
  productTailAt h h-bound =
    subst
      (λ w → TailBound w μ)
      (sym termPath)
      (sequenceCauchyProductTailBoundFromMajorant
        (PowerSeriesMajorizedOnBall.termMajorized left h h-bound)
        (PowerSeriesMajorizedOnBall.termMajorized right h h-bound)
        productTail)
    where
    termPath :
      powerSeriesTerm (cauchyProductPowerSeries a b) h ≡
      sequenceCauchyProduct (powerSeriesTerm a h) (powerSeriesTerm b h)
    termPath =
      funExt (cauchyProductPowerSeriesTerm-sequenceCauchyProduct a b h)


cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTail :
  {a b A B : PowerSeries} →
  {ρ : ℚ⁺} →
  {μ ν τ : ℚ⁺ → ℕ} →
  (left : PowerSeriesMajorizedOnBall a ρ A ν) →
  (right : PowerSeriesMajorizedOnBall b ρ B τ) →
  (productTail : TailBound (sequenceCauchyProduct A B) μ) →
  (productAntitone : AntitoneNatModulus μ) →
  (h : ℝᶜ) →
  (h-bound : BoundedByᶜ ρ h) →
  powerSeriesSumOnBall
    (cauchyProductPowerSeries a b)
    ρ
    μ
    (cauchyProductPowerSeriesOnBallWithFromMajorants
      left
      right
      productTail
      productAntitone)
    h
    h-bound
  ≡
  powerSeriesSumOnBall
    a
    ρ
    ν
    (majorizedOnBall→hasPowerSeriesOnBallWith left)
    h
    h-bound
  ·ᶜ
  powerSeriesSumOnBall
    b
    ρ
    τ
    (majorizedOnBall→hasPowerSeriesOnBallWith right)
    h
    h-bound
cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTail
  {a = a}
  {b = b}
  {A = A}
  {B = B}
  {ρ = ρ}
  {μ = μ}
  {ν = ν}
  {τ = τ}
  left
  right
  productTail
  productAntitone
  h
  h-bound =
  seriesSumFromFiniteTailBound-cong
    termPath
    productSeriesTail
    productAntitone
  ∙ seriesSumFromFiniteTailBound-data-independent
      transportedProductTail
      sequenceProductTail
      productAntitone
      productAntitone
  ∙ sequenceCauchyProductSumProductFromMajorantProductTail
      ν
      τ
      μ
      leftSeriesTail
      leftAntitone
      rightSeriesTail
      rightAntitone
      leftTermsMajorized
      rightTermsMajorized
      productTail
      productAntitone
  where
  leftConvergence : HasPowerSeriesOnBallWith a ρ ν
  leftConvergence =
    majorizedOnBall→hasPowerSeriesOnBallWith left

  rightConvergence : HasPowerSeriesOnBallWith b ρ τ
  rightConvergence =
    majorizedOnBall→hasPowerSeriesOnBallWith right

  productConvergence :
    HasPowerSeriesOnBallWith (cauchyProductPowerSeries a b) ρ μ
  productConvergence =
    cauchyProductPowerSeriesOnBallWithFromMajorants
      left
      right
      productTail
      productAntitone

  leftSeriesTail : TailBound (powerSeriesTerm a h) ν
  leftSeriesTail =
    HasPowerSeriesOnBallWith.tailBound leftConvergence h h-bound

  rightSeriesTail : TailBound (powerSeriesTerm b h) τ
  rightSeriesTail =
    HasPowerSeriesOnBallWith.tailBound rightConvergence h h-bound

  productSeriesTail :
    TailBound (powerSeriesTerm (cauchyProductPowerSeries a b) h) μ
  productSeriesTail =
    HasPowerSeriesOnBallWith.tailBound productConvergence h h-bound

  leftAntitone : AntitoneNatModulus ν
  leftAntitone =
    HasPowerSeriesOnBallWith.antitoneModulus leftConvergence

  rightAntitone : AntitoneNatModulus τ
  rightAntitone =
    HasPowerSeriesOnBallWith.antitoneModulus rightConvergence

  leftTermsMajorized :
    SeriesMajorizedBy (powerSeriesTerm a h) A
  leftTermsMajorized =
    PowerSeriesMajorizedOnBall.termMajorized left h h-bound

  rightTermsMajorized :
    SeriesMajorizedBy (powerSeriesTerm b h) B
  rightTermsMajorized =
    PowerSeriesMajorizedOnBall.termMajorized right h h-bound

  termPath :
    powerSeriesTerm (cauchyProductPowerSeries a b) h ≡
    sequenceCauchyProduct (powerSeriesTerm a h) (powerSeriesTerm b h)
  termPath =
    funExt (cauchyProductPowerSeriesTerm-sequenceCauchyProduct a b h)

  transportedProductTail :
    TailBound
      (sequenceCauchyProduct (powerSeriesTerm a h) (powerSeriesTerm b h))
      μ
  transportedProductTail =
    subst (λ w → TailBound w μ) termPath productSeriesTail

  sequenceProductTail :
    TailBound
      (sequenceCauchyProduct (powerSeriesTerm a h) (powerSeriesTerm b h))
      μ
  sequenceProductTail =
    sequenceCauchyProductTailBoundFromMajorant
      leftTermsMajorized
      rightTermsMajorized
      productTail
