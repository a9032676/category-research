open import Level
 
open import Categories.Core

module Objects.Coproduct {o m e : Level} where

-- A B : Ob(𝐶)
record Coproduct {𝐶 : Category o m e} (A B : Category.Obj 𝐶) : Set (o ⊔ m ⊔ e) where
  open Category 𝐶 using (_⇒_)
  field
    A+B : Obj 𝐶
    i₁  : A ⇒ A+B
    i₂  : B ⇒ A+B
    _∐_ : ∀ {C} → A ⇒ C → B ⇒ C → A+B ⇒ C
