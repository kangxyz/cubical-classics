{-

Cauchy-product coefficients for power series

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.PowerSeries.CauchyProduct where

open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Coefficients
  public
  using
    ( cauchyProductPowerSeries
    ; cauchyProductPowerSeries-zero
    ; cauchyProductPowerSeries-suc
    ; cauchyProductPowerSeries-suc-right
    ; cauchyProductPowerSeries-cong
    ; cauchyProductPowerSeries-cong-left
    ; cauchyProductPowerSeries-zero-left
    ; cauchyProductPowerSeries-zero-right
    ; cauchyProductPowerSeries-constant-left
    ; cauchyProductPowerSeries-one-left
    ; cauchyProductPowerSeries-comm
    ; cauchyProductPowerSeries-add-left
    ; cauchyProductPowerSeries-neg-left
    ; cauchyProductPowerSeries-sub-left
    ; cauchyProductPowerSeries-rationalScale-left
    )
open import Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Convergence
  public
  using
    ( cauchyProductPowerSeriesOnBallWithFromMajorants
    ; cauchyProductPowerSeriesSumOnBallProductFromMajorantsAndProductTail
    )
