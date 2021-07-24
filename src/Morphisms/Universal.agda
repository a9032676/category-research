module Morphisms.Universal where

open import Level
open import Categories.Core
open import Functors.Core hiding (_∘_)
open import Data.Product using (Σ; _,_)

private
  variable
    o₁ m₁ e₁ o₂ m₂ e₂ : Level

infix 4 UM⟨_,_⟩
infix 4 UM!⟨_,_⟩

syntax UniversalMorphism X F = X 𝒰-⇒ F

record UniversalMorphism
  {𝐶 : Category o₁ m₁ e₁} {𝐷 : Category o₂ m₂ e₂}
  (X : Obj 𝐷) (F : Functor 𝐶 𝐷) : Set (o₁ ⊔ m₂) where
  constructor UM⟨_,_⟩
  open Functor F using (Fₒ)
  field
    A : Obj 𝐶
    𝑢 : 𝐷 [ X , Fₒ A ]

syntax DualUniversalMorphism X F = X 𝒰-⇒! F

record DualUniversalMorphism
  {𝐶 : Category o₁ m₁ e₁} {𝐷 : Category o₂ m₂ e₂}
  (X : Obj 𝐷) (F : Functor 𝐶 𝐷) : Set (o₁ ⊔ m₂) where
  constructor UM!⟨_,_⟩
  open Functor F using (Fₒ)
  field
    A : Obj 𝐶
    𝑢 : 𝐷 [ Fₒ A , X ]
