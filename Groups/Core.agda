module Groups.Core where

open import Relation.Binary.PropositionalEquality
open import Level

private
  variable
    ℓ : Level

record Group (G : Set ℓ) (𝑒 : G) (_∙_ : G → G → G) : Set ℓ where
  field
    assoc : ∀ {f g h} → (f ∙ g) ∙ h ≡ f ∙ (g ∙ h)
    id    : ∀ {g} → g ∙ 𝑒 ≡ 𝑒 ∙ g
    invₗ  : ∀ {g h} → g ∙ h ≡ 𝑒
    invᵣ  : ∀ {g h} → 𝑒 ≡ h ∙ g

