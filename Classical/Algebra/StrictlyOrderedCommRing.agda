{-# OPTIONS --safe #-}
module Classical.Algebra.StrictlyOrderedCommRing where

open import Cubical.Algebra.OrderedCommRing public
  using (OrderedCommRing ; OrderedCommRingStr ; IsOrderedCommRing ; OrderedCommRing→CommRing)

open import Classical.Algebra.StrictlyOrderedCommRing.Base public
  hiding (Trichotomy ; lt ; eq ; gt)
open import Classical.Algebra.StrictlyOrderedCommRing.Properties public
