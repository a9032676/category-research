module Functors.Bifunctor where

open import Level

open import Categories.Core
open import Categories.Product
open import Categories.Sets
open import Functors.Core

private
  variable
    o₁ m₁ o₂ m₂ : Level

Bifunctor : ∀ (C₁ C₂ : Category o₁ m₁) (D : Category o₂ m₂) → Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂)
Bifunctor C₁ C₂ D = Functor (C₁ × C₂) D
