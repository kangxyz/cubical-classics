{-# OPTIONS --safe #-}
module Classical.Axioms.Choice where

open import Cubical.Foundations.Prelude
open import Cubical.Axiom.Choice public
  using ( choiceMap
        ; satAC
        ; satAC∃
        ; satAC→satAC∃
        ; satAC₀
        ; FinSatAC
        ; satAC∃Fin
        ; InductiveFinSatAC
        ; InductiveFinSatAC∃
        )


AC : Typeω
AC = {ℓ ℓ' ℓ'' : Level} → (X : Type ℓ) → satAC∃ ℓ' ℓ'' X
