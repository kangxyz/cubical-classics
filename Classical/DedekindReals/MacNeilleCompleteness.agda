{-

MacNeille completeness of constructive Dedekind reals under Oracle

-}
{-# OPTIONS --safe #-}
module Classical.DedekindReals.MacNeilleCompleteness where

open import Cubical.Foundations.Prelude

open import Classical.Axioms
import Classical.DedekindCompletion.MacNeilleCompleteness as Completion
open import Constructive.Algebra.LinearlyOrderedField.Instances.Rationals
  using (ℚArchimedeanLinearlyOrderedField)

private
  variable
    ℓ : Level


module LinearlyOrderedFieldStructure ⦃ 🤖 : Oracle ⦄ {ℓ : Level} where
  open Completion.LinearlyOrderedFieldStructure
    ⦃ 🤖 ⦄ ℚArchimedeanLinearlyOrderedField {ℓᴾ = ℓ}
    public
    renaming
      ( DedekindCompletionLinearlyOrderedCommRing to
        DedekindLinearlyOrderedCommRing
      ; DedekindCompletionIsFieldOnLinearlyOrderedCommRing to
        DedekindIsFieldOnLinearlyOrderedCommRing
      ; DedekindCompletionLinearlyOrderedField to
        DedekindLinearlyOrderedField
      )


module MacNeilleCompleteness ⦃ 🤖 : Oracle ⦄ {ℓ : Level} where
  open Completion.MacNeilleCompleteness
    ⦃ 🤖 ⦄ ℚArchimedeanLinearlyOrderedField {ℓᴾ = ℓ}
    public
    renaming
      ( isMacNeilleCompleteDedekindCompletion to
        isMacNeilleCompleteDedekindReal
      )


open LinearlyOrderedFieldStructure public
  using (DedekindLinearlyOrderedField ; DedekindLinearlyOrderedCommRing)

open MacNeilleCompleteness public
  using (isMacNeilleCompleteDedekindReal ; supremum)
