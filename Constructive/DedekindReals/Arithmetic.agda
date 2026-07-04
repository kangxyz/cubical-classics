{-

Constructive arithmetic structure on Dedekind reals.

This module is the public arithmetic entry point.  It re-exports the LEM-free
Dedekind-real arithmetic fragments, including the ordered-field structure.  The
cut-level definitions of addition, non-negative multiplication, and signed
multiplication live in Constructive.DedekindReals.Arithmetic.Base.

-}
{-# OPTIONS --safe #-}
module Constructive.DedekindReals.Arithmetic where

open import Constructive.DedekindReals.Arithmetic.Sign public
open import Constructive.DedekindReals.Arithmetic.Base public
open import Constructive.DedekindReals.Arithmetic.AdditiveGroup public
open import Constructive.DedekindReals.Arithmetic.Negation public
open import Constructive.DedekindReals.Arithmetic.NonNegative public
open import Constructive.DedekindReals.Arithmetic.Unit public
open import Constructive.DedekindReals.Arithmetic.Difference public
open import Constructive.DedekindReals.Arithmetic.Distributivity public
open import Constructive.DedekindReals.Arithmetic.Associativity public
open import Constructive.DedekindReals.Arithmetic.CommRing public
open import Constructive.DedekindReals.Arithmetic.Order public
open import Constructive.DedekindReals.Arithmetic.OrderedCommRing public
open import Constructive.DedekindReals.Arithmetic.Inverse public
open import Constructive.DedekindReals.Arithmetic.OrderedField public
