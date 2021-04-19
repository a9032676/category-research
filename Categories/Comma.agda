open import Level
module Categories.Comma { o₁ m₁ o₂ m₂ o₃ m₃ : Level } where

open import Categories.Core
open import Categories.Product
open import Data.Product renaming (_×_ to _×ᵖ_)
open import Functors.Core hiding (id; _∘_)

private
  variable
    A : Category o₁ m₁
    B : Category o₂ m₂
    C : Category o₃ m₃

record CommaObj (S : Functor A C) (T : Functor B C) : Set (o₁ ⊔ o₂ ⊔ m₃) where
  private module A = Category A
  private module B = Category B
  open Category hiding (_⇒_)
  open Category C using (_⇒_)
  open Functor S renaming (Fₒ to Sₒ)
  open Functor T renaming (Fₒ to Tₒ)
  field
    α : Obj A
    β : Obj B
    m : Sₒ α ⇒ Tₒ β

syntax Comma S T = S ↓ T

Comma : (S : Functor A C) (T : Functor B C) → Category (o₁ ⊔ o₂ ⊔ m₃) (m₁ ⊔ m₂)
Comma {A = A} {B = B} S T = record
  { Obj  = CommaObj S T
  ; _⇒_ = λ dom cod → A [ α dom , α cod ] ×ᵖ B [ β dom , β cod ]
  ; id   = id A , id B
  ; _∘_  = λ B⇒C A⇒B → proj₁ B⇒C ∘ᴬ proj₁ A⇒B , proj₂ B⇒C ∘ᴮ proj₂ A⇒B
  }
  where
    open CommaObj using (α; β)
    open Category using (id)
    open Category A renaming (_∘_ to _∘ᴬ_)
    open Category B renaming (_∘_ to _∘ᴮ_)

