{-# OPTIONS --safe #-}
module Classical.Algebra.StrictlyOrderedCommRing where

open import Classical.Algebra.OrderedCommRing public
  using (OrderedCommRing ; OrderedCommRingStr ; IsOrderedCommRing ; OrderedCommRing→CommRing)

open import Classical.Algebra.StrictlyOrderedCommRing.Base public
open import Classical.Algebra.StrictlyOrderedCommRing.Properties public
