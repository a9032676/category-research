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
    o m e : Level
    
open Category
open Functor
open NaturalTransformation

toYoneda : (C : Category o m e) {X : Obj C} {F : Functor C (𝑆𝑒𝑡 m)}
           → [ C , 𝑆𝑒𝑡 m ]⟨ Hom C [ X ,─] , F ⟩
           → Fₒ F X
toYoneda
  record { id = id }
  (η α)
  = α id 

fromYoneda : {C : Category o m e} {X : Obj C} (F : Functor C (𝑆𝑒𝑡 m))
             → Fₒ F X
             → [ C , 𝑆𝑒𝑡 m ]⟨ Hom C [ X ,─] , F ⟩
fromYoneda
  record { Fₘ = Fₘ }
  u
  = η (λ f → (Fₘ f) u)
