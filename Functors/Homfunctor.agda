module Functors.Homfunctor where

open import Level
open import Function using (flip)
open import Data.Product renaming (_×_ to _×ᵖ_)

open import Categories.Core
open import Categories.Product
open import Categories.Sets
open import Functors.Core
open import Functors.Bifunctor

open Category

private
  variable
    o m : Level

Hom[_,_] : (C₁ C₂ : Category o m) → Set (o ⊔ suc m)
Hom[_,_] {m = m} C₁ C₂ = Bifunctor C₁ C₂ (𝒮ℯ𝓉 m)

-- Mixed-variant hom-functor
-- C needs to be locally small category (or called category of set)
MixedVariantHomfunctor : (C : Category o m) → Hom[ op C , C ]
MixedVariantHomfunctor record { _⇒_ = _⇒_ ; _∘_ = _∘_ } = record
  { Fₒ = λ Cᵒᵖ×C → proj₁ Cᵒᵖ×C ⇒ proj₂ Cᵒᵖ×C
  ; Fₘ = λ fᵒᵖ×g q → proj₂ fᵒᵖ×g ∘ (q ∘ proj₁ fᵒᵖ×g)
  }

Representablefunctor : (Category o m) → Set (o ⊔ suc m)
Representablefunctor {m = m} C = Functor C (𝒮ℯ𝓉 m)

-- Covariant hom-functor
-- Hom(X, ─) : C → Set
CovariantHomfunctor : (C : Category o m) (X : Obj C) → Representablefunctor C
CovariantHomfunctor (record { _⇒_ = _⇒_ ;  _∘_ = _∘_ }) X = record
  { Fₒ = λ ─ → X ⇒ ─
  ; Fₘ = _∘_
  }

syntax CovariantHomfunctor C X = Hom C [ X ,─]

-- Contravariant hom-functor
-- Hom(─, X) : Cᵒᵖ → Set
ContravariantHomfunctor : (C : Category o m) (X : Obj C) → Representablefunctor (op C)
ContravariantHomfunctor record { _⇒_ = _⇒_ ; _∘_ = _∘_ } X = record
  { Fₒ = λ ─ → ─ ⇒ X
  ; Fₘ = flip _∘_
  }

syntax ContravariantHomfunctor C X = Hom C [─, X ] 

