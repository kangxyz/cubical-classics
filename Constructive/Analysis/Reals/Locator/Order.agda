{-

Order observations for located Cauchy reals

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.Locator.Order where

open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sum using (_⊎_)

open import Constructive.Analysis.Reals.CauchyReals.Base
open import Constructive.Analysis.Reals.CauchyReals.Order.StrictPositive
open import Constructive.Analysis.Reals.Locator.Base


compareLocated :
  (x : ℝᶜ) →
  Locator x →
  (q r : ℚ) →
  q ℚOrder.< r →
  (rational q <ᶜ x) ⊎ (x <ᶜ rational r)
compareLocated x loc =
  Locator.compare loc
