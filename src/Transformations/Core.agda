module NaturalTransformations.Core where

open import Level

open import Categories.Core
open import Functors.Core

private
  variable
    o₁ m₁ e₁ o₂ m₂ e₂ : Level

record NaturalTransformation
  (𝐶 : Category o₁ m₁ e₁) (𝐷 : Category o₂ m₂ e₂)
  (F G : Functor 𝐶 𝐷) : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
  constructor η_
  open Functor F using (Fₒ)
  open Functor G renaming (Fₒ to Gₒ)
  field
    η-mor : ∀ {X : Obj 𝐶} → 𝐷 [ Fₒ X , Gₒ X ]

syntax NaturalTransformation 𝐶 𝐷 F G = [ 𝐶 , 𝐷 ]⟨ F , G ⟩

open NaturalTransformation public

-- Vertical composition of natural transformation
_∘ᵛ_ : {𝐶 : Category o₁ m₁ e₁} {𝐷 : Category o₂ m₂ e₂} {F G H : Functor 𝐶 𝐷}
       → [ 𝐶 , 𝐷 ]⟨ G , H ⟩ → [ 𝐶 , 𝐷 ]⟨ F , G ⟩ → [ 𝐶 , 𝐷 ]⟨ F , H ⟩
_∘ᵛ_ {𝐶 = 𝐶} {𝐷 = 𝐷} (η β) (η α) = η (𝐷 [ β ∘ α ])
