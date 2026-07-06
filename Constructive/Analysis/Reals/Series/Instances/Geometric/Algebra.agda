{-

Algebra helpers for geometric-series identities

-}
{-# OPTIONS --safe --lossy-unification #-}
module Constructive.Analysis.Reals.Series.Instances.Geometric.Algebra where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver.Reflection

module SolverHelpers {ℓ : Level} (𝓡 : CommRing ℓ) where
  open CommRingStr (𝓡 .snd)

  geometric-zero :
    (r : 𝓡 .fst) →
    (1r - r) · 0r ≡ 1r - 1r
  geometric-zero _ =
    solve! 𝓡

  geometric-distrib :
    (r s p : 𝓡 .fst) →
    (1r - r) · (s + p) ≡ ((1r - r) · s) + ((1r - r) · p)
  geometric-distrib _ _ _ =
    solve! 𝓡

  geometric-step :
    (r p : 𝓡 .fst) →
    (1r - p) + ((1r - r) · p) ≡ 1r - (r · p)
  geometric-step _ _ =
    solve! 𝓡

  segment-zero :
    (r p : 𝓡 .fst) →
    (1r - r) · 0r ≡ p - p
  segment-zero _ _ =
    solve! 𝓡

  segment-distrib :
    (r p s : 𝓡 .fst) →
    (1r - r) · (p + s) ≡ ((1r - r) · p) + ((1r - r) · s)
  segment-distrib _ _ _ =
    solve! 𝓡

  segment-step :
    (r p t : 𝓡 .fst) →
    ((1r - r) · p) + ((r · p) - t) ≡ p - t
  segment-step _ _ _ =
    solve! 𝓡

  linear-zero :
    1r · (1r + 0r) ≡ 1r
  linear-zero =
    solve! 𝓡

  linear-factor-step :
    (q N : 𝓡 .fst) →
    q · ((1r + N) + (1r - q)) ≡
    (1r + N) - ((1r - q) · (N + (1r - q)))
  linear-factor-step _ _ =
    solve! 𝓡

  power-linear-step :
    (q p N d : 𝓡 .fst) →
    (q · p) · (1r + (N + d)) ≡
    p · (q · ((1r + N) + d))
  power-linear-step _ _ _ _ =
    solve! 𝓡
