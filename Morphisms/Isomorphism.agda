module Morphisms.Isomorphism where

open import Level
open import Relation.Binary.PropositionalEquality public

record _≅_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    to∘from : ∀ (a : A) → from (to a) ≡ a
    from∘to : ∀ (b : B) → to (from b) ≡ b
