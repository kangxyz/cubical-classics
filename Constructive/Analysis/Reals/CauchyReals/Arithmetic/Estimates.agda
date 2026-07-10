{-

Quantitative estimates for bounded Cauchy-real arithmetic

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.CauchyReals.Arithmetic.Estimates where

open import
  Constructive.Analysis.Reals.CauchyReals.Arithmetic.Internal.BoundedMultiplication
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
  Constructive.Analysis.Reals.CauchyReals.Arithmetic.Internal.BoundedReciprocal
  public
  using
    ( boundedReciprocalᶜ
    ; boundedReciprocalᶜ-lipschitz
    ; boundedReciprocalᶜ-continuous
    ; boundedReciprocalᶜ-bound
    )
