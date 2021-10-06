open import Level

module Functors.Bifunctor {o₁ m₁ e₁ o₂ m₂ e₂ o₃ m₃ e₃ : Level} where

open import Categories.Product public
open import Functors.Core public

Bifunctor : ∀ (C₁ : Category o₁ m₁ e₁) (C₂ : Category o₂ m₂ e₂) (D : Category o₃ m₃ e₃) → Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂ ⊔ o₃ ⊔ m₃ ⊔ e₃)
Bifunctor C₁ C₂ D = Functor (C₁ × C₂) D
