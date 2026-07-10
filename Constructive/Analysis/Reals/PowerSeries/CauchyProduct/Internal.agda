{-

Commutative-ring identities used by Cauchy-product proofs

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.CauchyProduct.Internal where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection


module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
  open CommRingStr (𝓡 .snd)

  rectangular-triangular-remainder-step :
    (u Qq Qm R T : 𝓡 .fst) →
    ((u · Qq + R) + (- (u · Qm + T))) ≡
    (u · (Qq + (- Qm)) + (R + (- T)))
  rectangular-triangular-remainder-step _ _ _ _ _ =
    solve! 𝓡

  tail-cauchy-product-decomposition-step :
    (u v tv cp tcp : 𝓡 .fst) →
    ((u · v + cp) + (u · tv + tcp)) ≡
    (u · (v + tv) + (cp + tcp))
  tail-cauchy-product-decomposition-step _ _ _ _ _ =
    solve! 𝓡
