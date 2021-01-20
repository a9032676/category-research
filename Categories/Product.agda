module Categories.Product where

open import Level
open import Data.Product renaming (_×_ to _×ᵖ_)

open import Categories.Core
open import Functors.Core
open import Objects.Product

-- Product Category
_×_ : ∀ {o m o' m' : Level} (C : Category o m) (D : Category o' m') → Category (o ⊔ o') (m ⊔ m')
C × D = record
  { Obj = C.Obj ×ᵖ D.Obj
  ; _⇒_ = λ p q → (proj₁ p C.⇒ proj₁ q) ×ᵖ (proj₂ p D.⇒ proj₂ q)
  ; id = C.id , D.id
  ; _∘_ = λ bc ab → proj₁ bc C.∘ proj₁ ab , proj₂ bc D.∘ proj₂ ab
  }
  where
    private module C = Category C
    private module D = Category D
