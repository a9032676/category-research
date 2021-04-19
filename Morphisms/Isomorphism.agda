module Morphisms.Isomorphism where

open import Level
open import Relation.Binary.PropositionalEquality public

record _≅_ {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} (a : A) (b : B) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    to : A → B
    from : B → A
    to∘from : from (to a) ≡ a
    from∘to : to (from b) ≡ b
