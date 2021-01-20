open import Level
 
open import Categories.Core

module Objects.Product {o m : Level} (𝒞 : Category o m) where

-- A B : Ob(𝒞)
record Product (A B : Category.Obj 𝒞) : Set (o ⊔ m) where
  open Category 𝒞 using (Obj; _⇒_)
  field
    A×B   : Obj
    π₁    : A×B ⇒ A
    π₂    : A×B ⇒ B
    ⟨_,_⟩ : ∀ {C} → C ⇒ A → C ⇒ B → C ⇒ A×B
