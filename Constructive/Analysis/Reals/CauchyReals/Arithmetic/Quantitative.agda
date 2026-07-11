{-

Quantitative estimates for bounded Cauchy-real arithmetic

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.CauchyReals.Arithmetic.Quantitative where

open import Constructive.Analysis.Reals.CauchyReals.Arithmetic.ProductBounds
  public
  using
    ( absᶜ-mul≤product
    ; absᶜ-rational-nonnegative
    ; absᶜ-scalarMul≤
    ; bounded-byᶜ-abs≤rational
    ; mulᶜ-nonnegative
    ; tripleScalarProductPath
    )
open import
  Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedMultiplication
  public
  using
    ( RationalRightMultiplierᶜ
    ; bounded-real-right-multiplierᶜ
    ; boundedMulᶜ
    ; boundedMulᶜ-close
    ; boundedMulᶜ-lipschitz
    ; boundedMulᶜ-continuous
    ; boundedMulᶜ-bound-independent
    )
open import
  Constructive.Analysis.Reals.CauchyReals.Arithmetic.BoundedReciprocal
  public
  using
    ( boundedReciprocalᶜ
    ; boundedReciprocalᶜ-lipschitz
    ; boundedReciprocalᶜ-continuous
    ; boundedReciprocalᶜ-bound
    )
open import Constructive.Analysis.Reals.CauchyReals.Order.Bounds
  public
  using (bounded-byᶜ-scale-rational-closed-bound)
