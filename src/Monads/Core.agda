module Monads.Core where

open import Level

open import Categories.Core
open import Functors.Core
open import Functors.Adjunction
open import Transformations.Core

open Functors.Core.Syntax


private
  variable
    o m e : Level

record Monad (πΆ : Category o m e) (π : Endβ¨ πΆ β©) : Set (o β m β e) where
  field
    Ξ· : [ πΆ , πΆ ]β¨ Id πΆ , π β©
    ΞΌ : [ πΆ , πΆ ]β¨ π Β² , π β©
