module Yoneda.YonedaLemma where

open import Level

open import Categories.Core
open import Categories.Sets
open import Categories.2-Category using ([_,_])
open import Functors.Core
open import Functors.Homfunctor
open import NaturalTransformations.Core
open import Morphisms.Isomorphism

private
  variable
    o m o' m' : Level

open Category
