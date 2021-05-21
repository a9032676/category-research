module Functors.Bifunctor where

open import Level

open import Categories.Core
open import Categories.Product
open import Categories.Sets
open import Functors.Core

private
  variable
    o₁ m₁ e₁ o₂ m₂ e₂ o₃ m₃ e₃ : Level

Bifunctor : ∀ (C₁ : Category o₁ m₁ e₁) (C₂ : Category o₂ m₂ e₂) (D : Category o₃ m₃ e₃) → Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂ ⊔ o₃ ⊔ m₃ ⊔ e₃)
Bifunctor C₁ C₂ D = Functor (C₁ × C₂) D
