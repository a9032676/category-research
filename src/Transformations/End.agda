open import Level
open import Categories.Core using (Category)

module Transformations.End
  {o₁ m₁ e₁ o₂ m₂ e₂ : Level}
  (𝐶 : Category o₁ m₁ e₁)
  {𝑋 : Category o₂ m₂ e₂}
  where

open import Categories.Product
open import Transformations.Extranatural

record Wedge
  (w : Obj 𝑋)
  (F : Functor (𝐶 ᵒᵖ × 𝐶) 𝑋)
  : Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
  constructor Wedge⟨_,_⟩
  open Category 𝑋 using (_⇒_)
  open Functor F using (Fₒ; Fₘ)
  field
    𝑒⟨_⟩ : ∀ (c : Obj 𝐶) → w ⇒ Fₒ (c , c)
    -- Naturality condition
    nat-cond :
      ∀ (c c′ : Obj 𝐶) (f : 𝐶 [ c , c′ ])
      → 𝑋 [ Fₘ (f , id 𝐶) ∘ 𝑒⟨ c′ ⟩ ≈ Fₘ (id 𝐶 , f) ∘ 𝑒⟨ c ⟩ ]

syntax Wedge w F = w W⇒ F

-- Universal wedge version
record End
  {w : Obj 𝑋} (c : Obj 𝐶)
  (F : Functor (𝐶 ᵒᵖ × 𝐶) 𝑋)
  : Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
  open Category 𝑋 using (_∘_; _⇒_)
  field
    apex : w W⇒ F
    uni-prop :
      ∀ (w′ : Obj 𝑋) (wedge : w′ W⇒ F) (h : w′ ⇒ w)
      (open Wedge apex)
      (open Wedge wedge renaming (𝑒⟨_⟩ to 𝑒⟨_⟩′))
      → 𝑋 [ 𝑒⟨ c ⟩ ∘ h ≈ 𝑒⟨ c ⟩′ ]

syntax End 𝐶 c F = ∫⟨ c ∈ 𝐶 ⟩ F

