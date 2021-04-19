module Categories.Product where

open import Level
open import Data.Product renaming (_×_ to _×ᵖ_)

open import Categories.Core
open import Functors.Core
open import Objects.Product

-- Product Category
ProductCategory : ∀ {o₁ m₁ o₂ m₂ : Level} (C : Category o₁ m₁) (D : Category o₂ m₂) → Category (o₁ ⊔ o₂) (m₁ ⊔ m₂)
ProductCategory C D = record
  { Obj = C.Obj ×ᵖ D.Obj
  ; _⇒_ = λ p q → C [ proj₁ p , proj₁ q ] ×ᵖ D [ proj₂ p , proj₂ q ]
  ; id = C.id , D.id
  ; _∘_ = λ bc ab → proj₁ bc C.∘ proj₁ ab , proj₂ bc D.∘ proj₂ ab
  }
  where
    private module C = Category C
    private module D = Category D

syntax ProductCategory C D = C × D
