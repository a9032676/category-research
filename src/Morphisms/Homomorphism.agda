module Morphisms.Homomorphism where

open import Level
open import Categories.Core
open import Morphisms.Isomorphism
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality public

private
  variable
    o m e ℓ : Level

Homomorphism :
  ∀ {A B : Set ℓ} (f : A → B)
  (_∙_ : ∀ {A} → A → A → A) (x y : A) → Set ℓ
Homomorphism f _∙_ x y = f (x ∙ y) ≡ f x ∙ f y

Endomorphism : {𝐶 : Category o m e} (A : Obj 𝐶) → Set m
Endomorphism {𝐶 = 𝐶} A = 𝐶 [ A , A ]

syntax Monomorphism X Y = X ↪ Y

record Monomorphism {𝐶 : Category o m e} (X Y : Obj 𝐶) : Set (o ⊔ m ⊔ e) where
  field
    cancelₗ :
      ∀ {Z : Obj 𝐶} (f : 𝐶 [ X , Y ]) (g₁ g₂ : 𝐶 [ Z , X ])
      → 𝐶 [ f ∘ g₁ ≈ f ∘ g₂ ] → 𝐶 [ g₁ ≈ g₂ ]

_[_↪_] : (𝐶 : Category o m e) (X Y : Obj 𝐶) → Set (o ⊔ m ⊔ e)
𝐶 [ X ↪ Y ] = Monomorphism {𝐶 = 𝐶} X Y

syntax Epimorphism X Y = X ↣ Y

record Epimorphism {𝐶 : Category o m e} (X Y : Obj 𝐶) : Set (o ⊔ m ⊔ e) where
  field
    cancelᵣ :
      ∀ {Z : Obj 𝐶} (f : 𝐶 [ X , Y ]) (g₁ g₂ : 𝐶 [ Y , Z ])
      → 𝐶 [ g₁ ∘ f ≈ g₂ ∘ f ] → 𝐶 [ g₁ ≈ g₂ ]

_[_↣_] : (𝐶 : Category o m e) (X Y : Obj 𝐶) → Set (o ⊔ m ⊔ e)
𝐶 [ X ↣ Y ] = Epimorphism {𝐶 = 𝐶} X Y
