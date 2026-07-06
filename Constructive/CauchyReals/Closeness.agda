{-

Closeness properties for HoTT Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.CauchyReals.Closeness where

open import Constructive.CauchyReals.Closeness.ReflexiveSymmetric public
open import Constructive.CauchyReals.Closeness.Internal.Computed public
  using
    ( ComputedClose
    ; close→computed
    ; computed→close
    ; close-triangle
    ; rationalConstructorTriangle
    )
open import Constructive.CauchyReals.Closeness.Rounded public
