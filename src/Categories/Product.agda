open import Level

module Categories.Product {o₁ m₁ e₁ o₂ m₂ e₂ : Level} where

open import Data.Product renaming (_×_ to _×ᵖ_) public

open import Categories.Core
open import CategoricalRelation.Heterogeneous using (hid)

open import Relation.Binary.PropositionalEquality using (refl)

record _≡×Cat_
  {𝐶 : Category o₁ m₁ e₁} {𝐷 : Category o₂ m₂ e₂}
  {A B : Obj 𝐶} {C D : Obj 𝐷}
  (p q : 𝐶 [ A , B ] ×ᵖ 𝐷 [ C , D ])
  : Set (e₁ ⊔ e₂) where
  field 
    eqₗ : 𝐶 [ hid {𝐶 = 𝐶} refl ∘ proj₁ p ≈ proj₁ q ∘ hid {𝐶 = 𝐶} refl ]
    eqᵣ : 𝐷 [ hid {𝐶 = 𝐷} refl ∘ proj₂ p ≈ proj₂ q ∘ hid {𝐶 = 𝐷} refl ]

-- Product Category
ProductCategory : (𝐶 : Category o₁ m₁ e₁) (𝐷 : Category o₂ m₂ e₂) → Category (o₁ ⊔ o₂) (m₁ ⊔ m₂) (e₁ ⊔ e₂)
ProductCategory 𝐶 𝐷 = record
  { Obj  = 𝐶.Obj ×ᵖ 𝐷.Obj
  ; _⇒_ = λ p q → 𝐶 [ proj₁ p , proj₁ q ] ×ᵖ 𝐷 [ proj₂ p , proj₂ q ]
  ; id   = 𝐶.id , 𝐷.id
  ; _∘_  = λ bc ab → proj₁ bc 𝐶.∘ proj₁ ab , proj₂ bc 𝐷.∘ proj₂ ab
  ; _≈_  = _≡×Cat_ {𝐶 = 𝐶} {𝐷 = 𝐷}
  }
  where
    private module 𝐶 = Category 𝐶
    private module 𝐷 = Category 𝐷

infixr 2 ProductCategory
syntax ProductCategory 𝐶 𝐷 = 𝐶 × 𝐷
