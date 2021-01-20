module Functors.Bifunctor where

open import Level

open import Categories.Core
open import Categories.Product
open import Categories.Sets
open import Functors.Core

private
  variable
    o m o' m' : Level

Bifunctor : ∀ (C₁ C₂ : Category o m) (D : Category o' m') → Set (o ⊔ m ⊔ o' ⊔ m')
Bifunctor C₁ C₂ D = Functor (C₁ × C₂) D
