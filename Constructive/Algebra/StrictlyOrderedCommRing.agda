{-# OPTIONS --safe #-}
module Constructive.Algebra.StrictlyOrderedCommRing where

open import Constructive.Algebra.OrderedCommRing public
  using (OrderedCommRing ; OrderedCommRingStr ; IsOrderedCommRing ; OrderedCommRing→CommRing)

open import Constructive.Algebra.StrictlyOrderedCommRing.Base public
open import Constructive.Algebra.StrictlyOrderedCommRing.Properties public
