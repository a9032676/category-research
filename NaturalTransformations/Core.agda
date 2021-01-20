module NaturalTransformations.Core where

open import Level

open import Categories.Core
open import Functors.Core

private
  variable
    o m o' m' : Level

record NaturalTransformation
  (C : Category o m) (D : Category o' m')
  (F G : Functor C D) : Set (o ⊔ m ⊔ o' ⊔ m') where
  open Functor F using (Fₒ)
  open Category D using (_⇒_)
  private module G = Functor G
  field
    η : ∀ X → Fₒ X ⇒ G.Fₒ X

-- Vertical composition of natural transformation
_∘ᵛ_ : {C : Category o m} {D : Category o' m'} {F G H : Functor C D}
       → NaturalTransformation C D G H
       → NaturalTransformation C D F G
       → NaturalTransformation C D F H
_∘ᵛ_ {_} {_} {_} {_} {C} {D} {F} {G} {H} G→H F→G = record { η = β∘α }
  where
    private module C = Category C
    private module D = Category D
    
    private module F = Functor F using (Fₒ)
    private module G = Functor G using (Fₒ)
    private module H = Functor H using (Fₒ)
    
    open NaturalTransformation using (η)
    
    α : ∀ X → F.Fₒ X D.⇒ G.Fₒ X
    α = η F→G

    β : ∀ X → G.Fₒ X D.⇒ H.Fₒ X
    β = η G→H

    β∘α : (X : C.Obj) → F.Fₒ X D.⇒ H.Fₒ X
    β∘α x = β x D.∘ α x
