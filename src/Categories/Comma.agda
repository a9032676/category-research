open import Level
open import Categories.Core

module Categories.Comma
  {o₁ m₁ e₁ o₂ m₂ e₂ o₃ m₃ e₃ : Level}
  {A : Category o₁ m₁ e₁}
  {B : Category o₂ m₂ e₂}
  {C : Category o₃ m₃ e₃}
  where

open import Categories.Product public
open import Functors.Core hiding (_∘_)
open import CategoricalRelation.Heterogeneous using (hid)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record CommaObj (S : Functor A C) (T : Functor B C) : Set (o₁ ⊔ o₂ ⊔ m₃) where
  open Functor S renaming (Fₒ to Sₒ)
  open Functor T renaming (Fₒ to Tₒ)
  field
    α : Obj A
    β : Obj B
    m : C [ Sₒ α , Tₒ β ]

open CommaObj

record _≡↓_
  {S : Functor A C} {T : Functor B C}
  {dom₁ cod₁ dom₂ cod₂ : CommaObj S T}
  (p : A [ α dom₁ , α cod₁ ] ×ᵖ B [ β dom₁ , β cod₁ ])
  (q : A [ α dom₂ , α cod₂ ] ×ᵖ B [ β dom₂ , β cod₂ ])
  : Set (o₁ ⊔ e₁ ⊔ o₂ ⊔ e₂) where
  field
    eq-α-dom : α dom₁ ≡ α dom₂
    eq-α-cod : α cod₁ ≡ α cod₂
    eq-β-dom : β dom₁ ≡ β dom₂
    eq-β-cod : β cod₁ ≡ β cod₂
    eq-αₘ : A [ hid {𝐶 = A} eq-α-cod ∘ proj₁ p ≈ proj₁ q ∘ hid {𝐶 = A} eq-α-dom ]
    eq-βₘ : B [ hid {𝐶 = B} eq-β-cod ∘ proj₂ p ≈ proj₂ q ∘ hid {𝐶 = B} eq-β-dom ]

infix 4 Comma
syntax Comma S T = S ↓ T

Comma : (S : Functor A C) (T : Functor B C) → Category (o₁ ⊔ o₂ ⊔ m₃) (m₁ ⊔ m₂) (o₁ ⊔ e₁ ⊔ o₂ ⊔ e₂)
Comma S T = record
  { Obj  = CommaObj S T
  ; _⇒_ = λ dom cod → A [ α dom , α cod ] ×ᵖ B [ β dom , β cod ]
  ; id   = id A , id B
  ; _∘_  = λ B⇒C A⇒B → proj₁ B⇒C ∘ᴬ proj₁ A⇒B , proj₂ B⇒C ∘ᴮ proj₂ A⇒B
  ; _≈_  = λ {dom} {cod} → _≡↓_ {S = S} {T = T} {dom} {cod} {dom} {cod}
  }
  where
    open CommaObj using (α; β)
    open Category using (id)
    open Category A renaming (_∘_ to _∘ᴬ_)
    open Category B renaming (_∘_ to _∘ᴮ_)

