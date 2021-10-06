open import Level
open import Categories.Core using (Category)

module Transformations.Dinatural
  {o₁ m₁ e₁ o₂ m₂ e₂ : Level}
  {𝐶 : Category o₁ m₁ e₁}
  {𝐷 : Category o₂ m₂ e₂}
  where

open import Categories.Product public
open import Functors.Core using (Functor) public

record DinaturalTransformation
  (F G : Functor (𝐶 ᵒᵖ × 𝐶) 𝐷)
  {c : Obj 𝐶}
  : Set (o₁ ⊔ m₁ ⊔ m₂ ⊔ e₂) where
  open Category 𝐷 using (_⇒_)
  open Functor F using (Fₒ; Fₘ)
  open Functor G renaming (Fₒ to Gₒ; Fₘ to Gₘ)
  field
    α⟨c⟩ : Fₒ (c , c) ⇒ Gₒ (c , c)
    -- Hexagon identity
    𝟙 :
      ∀ {c′ : Obj 𝐶} {f : 𝐶 [ c , c′ ]}
      → 𝐷 [ Gₘ (id 𝐶 , f) ∘ α⟨c⟩ ∘ Fₘ (f , id 𝐶) ≈ Gₘ (id 𝐶 , f) ∘ α⟨c⟩ ∘ Fₘ (f , id 𝐶) ]
