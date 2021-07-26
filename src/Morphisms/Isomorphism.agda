module Morphisms.Isomorphism where

open import Level
open import Categories.Core
open import Functors.Core
open import NaturalTransformations.Core
open import Function renaming (id to idᶠ; _∘′_ to _∘ᶠ_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality public

record Isomorphic
  {ℓ₁ ℓ₂ : Level} {T : Set ℓ₁}
  (_⇒_ : Rel T ℓ₂) (id : ∀ {A} → A ⇒ A)
  (_∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C))
  (A : T) (B : T)
  : Set (ℓ₁ ⊔ suc ℓ₂) where
  field
    f : A ⇒ B
    g : B ⇒ A
    isoₗ : g ∘ f ≡ id
    isoᵣ : f ∘ g ≡ id

infixr 4 Isomorphism
infixr 5 CategoricalIsomorphism
infixr 6 NaturalIsomorphism

syntax Isomorphism A B = A ≅ B
syntax CategoricalIsomorphism 𝐶 A B = 𝐶 [ A ≅ B ]
syntax NaturalIsomorphism 𝐶 𝐷 F G = [ 𝐶 , 𝐷 ]⟨ F ≅ G ⟩

Isomorphism : ∀ {ℓ : Level} (A B : Set ℓ) → Set (suc ℓ)
Isomorphism = Isomorphic (λ X Y → X → Y) idᶠ _∘ᶠ_

private
  variable
    o₁ m₁ e₁ o₂ m₂ e₂ : Level

CategoricalIsomorphism : ∀ (𝐶 : Category o₁ m₁ e₁) (A B : Obj 𝐶) → Set (o₁ ⊔ suc m₁)
CategoricalIsomorphism 𝐶 = Isomorphic (𝐶 [_,_]) (id 𝐶) (𝐶 [_∘_])

NaturalIsomorphism :
  (𝐶 : Category o₁ m₁ e₁) (𝐷 : Category o₂ m₂ e₂)
  (F G : Functor 𝐶 𝐷) → Set (suc (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂))
NaturalIsomorphism 𝐶 𝐷 = Isomorphic (λ dom cod → [ 𝐶 , 𝐷 ]⟨ dom , cod ⟩) (η (id 𝐷)) _∘ᵛ_
