{-

Cauchy-product coefficients for power series

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.CauchyProduct where

open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Core
  public
  using
    ( cauchyProductPowerSeries
    ; sequenceCauchyProduct
    ; sequenceCauchyProduct-zero
    ; sequenceCauchyProduct-suc
    ; sequenceCauchyProduct-cong
    )
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Algebra public
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Theorem public
