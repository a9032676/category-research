open import Level
open import Categories.Core using (Category)

module Transformations.Extranatural
  {o₁ m₁ e₁ o₂ m₂ e₂ o₃ m₃ e₃ o₄ m₄ e₄ : Level}
  {𝐴 : Category o₁ m₁ e₁}
  {𝐵 : Category o₂ m₂ e₂}
  {𝐶 : Category o₃ m₃ e₃}
  {𝐷 : Category o₄ m₄ e₄}
  where

open import Categories.Product public
open import Functors.Core using (Functor) public

record ExtranaturalTransformation
  (F : Functor (𝐴 × 𝐵 × 𝐵 ᵒᵖ) 𝐷)
  (G : Functor (𝐴 × 𝐶 × 𝐶 ᵒᵖ) 𝐷)
  {a : Obj 𝐴} {b : Obj 𝐵} {c : Obj 𝐶}
  : Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂ ⊔ o₃ ⊔ m₃ ⊔ m₄ ⊔ e₄) where
  open Category 𝐷 using (_⇒_)
  open Functor F using (Fₒ; Fₘ)
  open Functor G renaming (Fₒ to Gₒ; Fₘ to Gₘ)
  field
    α⟨a,b,c⟩ : Fₒ (a , b , b) ⇒ Gₒ (a , c , c)
    nat-a :
      {a′ : Obj 𝐴} {f : 𝐴 [ a , a′ ]} {α⟨a′,b,c⟩ : Fₒ (a′ , b , b) ⇒ Gₒ (a′ , c , c)}
      → 𝐷 [ α⟨a′,b,c⟩ ∘ Fₘ (f , id 𝐵 , id (𝐵 ᵒᵖ)) ≈ Gₘ (f , id 𝐶 , id (𝐶 ᵒᵖ)) ∘ α⟨a,b,c⟩ ]
    extra-b :
      {b′ : Obj 𝐵} {g : 𝐵 [ b , b′ ]} {α⟨a,b′,c⟩ : Fₒ (a , b′ , b′) ⇒ Gₒ (a , c , c)}
      → 𝐷 [ α⟨a,b,c⟩ ∘ Fₘ (id 𝐴 , id 𝐵 , g) ≈ α⟨a,b′,c⟩ ∘ Fₘ (id 𝐴 , g , id (𝐵 ᵒᵖ)) ]
    extra-c :
      {c′ : Obj 𝐶} {h : 𝐶 [ c , c′ ]} {α⟨a,b,c′⟩ : Fₒ (a , b , b) ⇒ Gₒ (a , c′ , c′)}
      → 𝐷 [ Gₘ (id 𝐴 , h , id (𝐶 ᵒᵖ) ) ∘ α⟨a,b,c⟩ ≈ Gₘ (id 𝐴 , id 𝐶 , h) ∘ α⟨a,b,c′⟩ ]

syntax ExtranaturalTransformation F G = F Ex⇒ G
