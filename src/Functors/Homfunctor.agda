module Functors.Homfunctor where

open import Level
open import Function using (flip)

open import Categories.Product public
open import Categories.Sets public
open import Functors.Bifunctor public

private
  variable
    o m e : Level

Hom[_,_] : {ℓ : Level} (C D : Category o m e) → Set (o ⊔ m ⊔ e ⊔ suc ℓ)
Hom[_,_] {ℓ = ℓ} C D = Bifunctor C D (𝑆𝑒𝑡 ℓ)

--Hom : (ℓ₁ ℓ₂ : Level) (C₁ : Category o₁ m₁ e₁) (C₂ : Category o₂ m₂ e₂) → Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂ ⊔ suc (ℓ₁ ⊔ ℓ₂))
--Hom ℓ₁ ℓ₂ = Hom[_,_] {ℓ = ℓ₁ ⊔ ℓ₂}

-- Mixed-variant hom-functor
-- C needs to be locally small category (or called category of set)
MixedVariantHomfunctor : (C : Category o m e) → Hom[ op C , C ]
MixedVariantHomfunctor record { _⇒_ = _⇒_ ; _∘_ = _∘_ } = record
  { Fₒ = λ Cᵒᵖ×C → proj₁ Cᵒᵖ×C ⇒ proj₂ Cᵒᵖ×C
  ; Fₘ = λ fᵒᵖ×g q → proj₂ fᵒᵖ×g ∘ (q ∘ proj₁ fᵒᵖ×g)
  }

Representablefunctor : (Category o m e) → Set (o ⊔ suc m ⊔ e)
Representablefunctor {m = m} C = Functor C (𝑆𝑒𝑡 m)

-- Covariant hom-functor
-- Hom(X, ─) : C → Set
CovariantHomfunctor : (C : Category o m e) (X : Obj C) → Representablefunctor C
CovariantHomfunctor (record { _⇒_ = _⇒_ ;  _∘_ = _∘_ }) X = record
  { Fₒ = λ ─ → X ⇒ ─
  ; Fₘ = _∘_
  }

syntax CovariantHomfunctor C X = Hom C [ X ,─]

-- Contravariant hom-functor
-- Hom(─, X) : Cᵒᵖ → Set
ContravariantHomfunctor : (C : Category o m e) (X : Obj C) → Representablefunctor (op C)
ContravariantHomfunctor record { _⇒_ = _⇒_ ; _∘_ = _∘_ } X = record
  { Fₒ = _⇒ X
  ; Fₘ = flip _∘_
  }

syntax ContravariantHomfunctor C X = Hom C [─, X ] 

