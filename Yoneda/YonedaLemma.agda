module Yoneda.YonedaLemma where

open import Level

open import Categories.Core
open import Categories.Sets
open import Functors.Core
open import Functors.Homfunctor
open import NaturalTransformations.Core
open import Morphisms.Isomorphism

private
  variable
    o m : Level

open Category
open Functor
open NaturalTransformation using (η)

toYoneda : (C : Category o m) {X : Obj C} {F : Functor C (𝒮ℯ𝓉 m)}
           → [ C , 𝒮ℯ𝓉 m ]⟨ Hom C [ X ,─] , F ⟩
           → Fₒ F X
toYoneda
  record { id = id }
  record { η = η }
  = η id

fromYoneda : {C : Category o m} {X : Obj C} (F : Functor C (𝒮ℯ𝓉 m))
             → Fₒ F X
             → [ C , 𝒮ℯ𝓉 m ]⟨ Hom C [ X ,─] , F ⟩
fromYoneda
  record { Fₘ = Fₘ }
  u
  = record { η = λ f → (Fₘ f) u }
