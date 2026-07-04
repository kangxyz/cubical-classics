{-

Constructive Dedekind reals over the rationals.

This is the LEM-free rational-cut presentation.  The Oracle-based classical
Dedekind-real completion by cuts remains in Classical.DedekindCut.

This module is the public entry point.  The record definition itself lives in
Constructive.DedekindReals.Base, and its basic properties and constructions
live in Constructive.DedekindReals.Properties.

-}
{-# OPTIONS --safe #-}
module Constructive.DedekindReals where

open import Constructive.DedekindReals.Base public
open import Constructive.DedekindReals.Properties public
