{-# OPTIONS --safe #-}
module Constructive.Algebra.LinearlyOrderedCommRing where

open import Constructive.Algebra.OrderedCommRing public
  using (OrderedCommRing ; OrderedCommRingStr ; IsOrderedCommRing ; OrderedCommRing→CommRing)

open import Constructive.Algebra.LinearlyOrderedCommRing.Base public
open import Constructive.Algebra.LinearlyOrderedCommRing.Properties public
