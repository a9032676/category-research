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
open Functor
open NaturalTransformation using (η)

toYoneda : (C : Category o m) {X : Obj C} {F : Functor C (𝒮ℯ𝓉 m)}
           → [ C , (𝒮ℯ𝓉 m) ]⟨ Hom C [ X ,─] , F ⟩
           → Fₒ F X
toYoneda
  record { id = id }
  record { η = η }
  = η id

{-
  to :: ∀ x. (∀ a. (x → a) → f a) → f x
  to :: ((x → x) → f x) → f x
  η : ((x → x) → f x)
  η id : f x
-}

fromYoneda : {C : Category o m} {X : Obj C} (F : Functor C (𝒮ℯ𝓉 m))
             → Fₒ F X
             → [ C , 𝒮ℯ𝓉 m ]⟨ Hom C [ X ,─] , F ⟩
fromYoneda
  record { Fₘ = Fₘ }
  fx
  = record { η = λ f → Fₘ f fx }
