{-

Commutative-ring identities used by exponential majorant proofs

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.PowerSeries.Instances.Exponential.Internal where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection


module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
  open CommRingStr (𝓡 .snd)

  exp-majorant-step :
    (ρ p r u : 𝓡 .fst) →
    (ρ · p) · (r · u) ≡ (ρ · u) · (p · r)
  exp-majorant-step _ _ _ _ =
    solve! 𝓡

  exp-geometric-scale-step :
    (h s p : 𝓡 .fst) →
    h · (s · p) ≡ s · (h · p)
  exp-geometric-scale-step _ _ _ =
    solve! 𝓡
