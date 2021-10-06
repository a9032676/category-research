open import Level

module Yoneda.YonedaLemma {o m e : Level} where

open import Categories.Core
open import Categories.Sets
open import Functors.Core
open import Functors.Homfunctor
open import NaturalTransformations.Core
open import Morphisms.Isomorphism

module Yoneda (C : Category o m e) {X : Obj C} {F : Functor C (𝑆𝑒𝑡 m)} where
  open Functor F

  toYoneda : [ C , 𝑆𝑒𝑡 m ]⟨ Hom C [ X ,─] , F ⟩ → Fₒ X
  toYoneda (η α) = α (id C)

  fromYoneda : Fₒ X → [ C , 𝑆𝑒𝑡 m ]⟨ Hom C [ X ,─] , F ⟩
  fromYoneda u = η (λ f → (Fₘ f) u)
