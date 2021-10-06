open import Level
open import Categories.Core

module NaturalTransformations.Extranatural
  (o₁ m₁ e₁ o₂ m₂ e₂ o₃ m₃ e₃ o₄ m₄ e₄ : Level)
  {A : Category o₁ m₁ e₁}
  {B : Category o₂ m₂ e₂}
  {C : Category o₃ m₃ e₃}
  {D : Category o₄ m₄ e₄}
  where

open import Categories.Product
open import Functors.Core using (Functor)
open import Data.Product renaming (_×_ to _×ᵖ_)

record ExtranaturalTransformation
  (F : Functor (A × B × (B ᵒᵖ)) D)
  (G : Functor (A × C × (C ᵒᵖ)) D)
  {a : Obj A} {b : Obj B} {c : Obj C}
  : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂ ⊔ o₃ ⊔ m₃ ⊔ e₃ ⊔ o₄ ⊔ m₄ ⊔ e₄) where
  open Category D using (_⇒_)
  open Functor F using (Fₒ; Fₘ)
  open Functor G renaming (Fₒ to Gₒ; Fₘ to Gₘ)
  field
    α⟨a,b,c⟩ : Fₒ (a , b , b) ⇒ Gₒ (a , c , c)
    nat-a :
      {a′ : Obj A} {f : A [ a , a′ ]} {α⟨a′,b,c⟩ : Fₒ (a′ , b , b) ⇒ Gₒ (a′ , c , c)}
      → D [ α⟨a′,b,c⟩ ∘ Fₘ (f , id B , id (B ᵒᵖ)) ≈ Gₘ (f , id C , id (C ᵒᵖ)) ∘ α⟨a,b,c⟩ ]
    extra-b :
      {b′ : Obj B} {g : B [ b , b′ ]} {α⟨a,b′,c⟩ : Fₒ (a , b′ , b′) ⇒ Gₒ (a , c , c)}
      → D [ α⟨a,b,c⟩ ∘ Fₘ (id A , id B , g) ≈ α⟨a,b′,c⟩ ∘ Fₘ (id A , g , id (B ᵒᵖ)) ]
    extra-c :
      {c′ : Obj C} {h : C [ c , c′ ]} {α⟨a,b,c′⟩ : Fₒ (a , b , b) ⇒ Gₒ (a , c′ , c′)}
      → D [ Gₘ (id A , h , id (C ᵒᵖ) ) ∘ α⟨a,b,c⟩ ≈ Gₘ (id A , id C , h) ∘ α⟨a,b,c′⟩ ]

syntax ExtranaturalTransformation F G = F Ex⇒ G
