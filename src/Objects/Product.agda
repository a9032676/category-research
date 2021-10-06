open import Level
open import Categories.Core using (Category)

module Objects.Product {o m e : Level} (𝐶 : Category o m e) where

open Category 𝐶 using (Obj; _⇒_)

syntax Product A B = A × B

-- A B : Ob(𝐶)
record Product (A B : Obj) : Set (o ⊔ m) where
  field
    A×B   : Obj
    π₁    : A×B ⇒ A
    π₂    : A×B ⇒ B
    ⟨_,_⟩ : ∀ {C} → C ⇒ A → C ⇒ B → C ⇒ A×B
