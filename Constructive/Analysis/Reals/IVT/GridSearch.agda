{-

Finite rational grid search for approximate IVT arguments

-}
{-# OPTIONS --safe #-}
module Constructive.Analysis.Reals.IVT.GridSearch where

open import Cubical.Foundations.Prelude

import Cubical.Data.FinData.Base as Fin
open import Cubical.Data.FinData.Base using (Fin)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; _×_)
open import Cubical.Data.Sum using (inl ; inr)

open import Constructive.Data.PositiveRationals
open import Constructive.Data.Rationals.Closeness
import Constructive.Data.Rationals as Rational


SignChange :
  {n : ℕ} →
  (Fin (suc (suc n)) → ℚ) →
  Fin (suc n) →
  Type₀
SignChange values i =
  (values (Fin.weakenFin i) ℚOrder.< Rational.0ℚ) ×
  (Rational.0ℚ ℚOrder.≤ values (Fin.suc i))


AdjacentValuesClose :
  {n : ℕ} →
  (Fin (suc (suc n)) → ℚ) →
  ℚ⁺ →
  Fin (suc n) →
  Type₀
AdjacentValuesClose values ε i =
  Closeℚ (values (Fin.weakenFin i)) ε (values (Fin.suc i))


NearZeroCandidate :
  {n : ℕ} →
  (Fin (suc (suc n)) → ℚ) →
  ℚ⁺ →
  Fin (suc n) →
  Type₀
NearZeroCandidate values ε i =
  SignChange values i × AdjacentValuesClose values ε i


NonnegativeSmall :
  {n : ℕ} →
  (Fin n → ℚ) →
  ℚ⁺ →
  Fin n →
  Type₀
NonnegativeSmall values ε i =
  (Rational.0ℚ ℚOrder.≤ values i) ×
  (values i ℚOrder.< radius ε)


rightSmallFromCandidate :
  {n : ℕ} →
  {values : Fin (suc (suc n)) → ℚ} →
  {ε : ℚ⁺} →
  (i : Fin (suc n)) →
  NearZeroCandidate values ε i →
  NonnegativeSmall values ε (Fin.suc i)
rightSmallFromCandidate {values = values} {ε = ε} i ((left<0 , 0≤right) , close) =
  0≤right ,
  Rational.<≤-trans
    {p = values (Fin.suc i)}
    {q = values (Fin.weakenFin i) ℚ.+ radius ε}
    {r = radius ε}
    (Rational.diff<→shift<
      (values (Fin.weakenFin i))
      (values (Fin.suc i))
      (radius ε)
      (close .snd))
    (Rational.add-nonpositive≤right
      {p = values (Fin.weakenFin i)}
      {r = radius ε}
      (Rational.<→≤
        {p = values (Fin.weakenFin i)}
        {q = Rational.0ℚ}
        left<0))


gridSignChange :
  (n : ℕ) →
  (values : Fin (suc (suc n)) → ℚ) →
  values Fin.zero ℚOrder.< Rational.0ℚ →
  Rational.0ℚ ℚOrder.≤ values (Fin.fromℕ (suc n)) →
  Σ[ i ∈ Fin (suc n) ] SignChange values i
gridSignChange zero values v₀<0 0≤v₁ =
  Fin.zero , v₀<0 , 0≤v₁
gridSignChange (suc n) values v₀<0 0≤last
  with Rational.negative-or-nonnegative (values (Fin.suc Fin.zero))
... | inr 0≤v₁ =
  Fin.zero , v₀<0 , 0≤v₁
... | inl v₁<0 =
  Fin.suc (step .fst) , step .snd
  where
  tailValues : Fin (suc (suc n)) → ℚ
  tailValues i =
    values (Fin.suc i)

  step : Σ[ i ∈ Fin (suc n) ] SignChange tailValues i
  step =
    gridSignChange n tailValues v₁<0 0≤last


gridNearZeroCandidate :
  (n : ℕ) →
  (values : Fin (suc (suc n)) → ℚ) →
  (ε : ℚ⁺) →
  ((i : Fin (suc n)) → AdjacentValuesClose values ε i) →
  values Fin.zero ℚOrder.< Rational.0ℚ →
  Rational.0ℚ ℚOrder.≤ values (Fin.fromℕ (suc n)) →
  Σ[ i ∈ Fin (suc n) ] NearZeroCandidate values ε i
gridNearZeroCandidate n values ε adjacentClose v₀<0 0≤last =
  i , signChange , adjacentClose i
  where
  signChangeAt : Σ[ i ∈ Fin (suc n) ] SignChange values i
  signChangeAt =
    gridSignChange n values v₀<0 0≤last

  i : Fin (suc n)
  i =
    signChangeAt .fst

  signChange : SignChange values i
  signChange =
    signChangeAt .snd


gridNearZeroRight :
  (n : ℕ) →
  (values : Fin (suc (suc n)) → ℚ) →
  (ε : ℚ⁺) →
  ((i : Fin (suc n)) → AdjacentValuesClose values ε i) →
  values Fin.zero ℚOrder.< Rational.0ℚ →
  Rational.0ℚ ℚOrder.≤ values (Fin.fromℕ (suc n)) →
  Σ[ i ∈ Fin (suc (suc n)) ] NonnegativeSmall values ε i
gridNearZeroRight n values ε adjacentClose v₀<0 0≤last =
  Fin.suc (candidate .fst) ,
  rightSmallFromCandidate
    {values = values}
    {ε = ε}
    (candidate .fst)
    (candidate .snd)
  where
  candidate : Σ[ i ∈ Fin (suc n) ] NearZeroCandidate values ε i
  candidate =
    gridNearZeroCandidate n values ε adjacentClose v₀<0 0≤last
