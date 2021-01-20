open import Level
 
open import Categories.Core

module Objects.Coproduct {o m : Level} (𝒞 : Category o m) where

-- A B : Ob(𝒞)
record Coproduct (A B : Category.Obj 𝒞) : Set (o ⊔ m) where
  open Category 𝒞 using (Obj; _⇒_)
  field
    A+B : Obj
    i₁  : A ⇒ A+B
    i₂  : B ⇒ A+B
    _∐_ : ∀ {C} → A ⇒ C → B ⇒ C → A+B ⇒ C
