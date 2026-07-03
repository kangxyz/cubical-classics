{-# OPTIONS --safe #-}
module Classical.Algebra.Field.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Field as CubicalField

open CubicalField public
  using ( Field ; IsField ; isfield ; fieldstr
        ; makeIsField ; makeField ; makeFieldFromCommRing
        ; Field→CommRing ; FieldHom ; FieldEquiv ; FieldPath ; uaField
        ; isPropIsField
        ; FieldEquiv→FieldHom ; _$f_ )
  renaming (FieldStr to CubicalFieldStr)
