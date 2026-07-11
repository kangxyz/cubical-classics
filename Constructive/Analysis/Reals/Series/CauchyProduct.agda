{-

Cauchy products of Cauchy-real series

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Series.CauchyProduct where

open import Constructive.Analysis.Reals.Series.CauchyProduct.Finite
  public
  using
    ( sequenceCauchyProduct
    ; sequenceCauchyProduct-antiDiagonal
    ; sequenceCauchyProduct-cong
    ; sequenceCauchyProduct-cong-left
    ; sequenceCauchyProduct-scale-left
    ; partialProduct-sequenceCauchyProductRemainder
    )
open import Constructive.Analysis.Reals.Series.CauchyProduct.Majorant
  public
  using
    ( sequenceCauchyProductMajorizedBy
    ; sequenceCauchyProductMajorizedByTerms
    ; sequenceCauchyProductTailBoundFromMajorant
    )
open import Constructive.Analysis.Reals.Series.CauchyProduct.ProductOfSums
  public
  using (sequenceCauchyProductSumProductFromMajorantProductTail)
