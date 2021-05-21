module Categories.2-Category where

open import Level
open import Function hiding (Inverse) renaming (_∘_ to _∘ᶠ_; id to idᶠ)

open import Categories.Core
open import Functors.Core
open import NaturalTransformations.Core
open import Morphisms.Isomorphism using (CategoricalIsomorphism)

open Functor using (Fₒ; Fₘ)
open Category using (id; _∘_)
open NaturalTransformation

private
  variable
    o₁ m₁ e₁ o₂ m₂ e₂ : Level

-- Cat Category
Cat : Category (suc (o₁ ⊔ m₁ ⊔ e₁)) (o₁ ⊔ m₁ ⊔ e₁) (o₁ ⊔ m₁ ⊔ e₁)
Cat {o} {m} {e} = record
  { Obj  = Category o m e
  ; _⇒_ = Functor
  ; id   = record
    { Fₒ = idᶠ
    ; Fₘ = idᶠ
    }
  ; _∘_ = λ fbc fab → record
    { Fₒ = Fₒ fbc ∘ᶠ Fₒ fab
    ; Fₘ = Fₘ fbc ∘ᶠ Fₘ fab
    }
  ; _≈_ = _≡F_
  }

-- Functor Category
[_,_] : Category o₁ m₁ e₁
     → Category o₂ m₂ e₂
     → Category (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂)
                 (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂)
                 (o₁ ⊔ e₂)
[ 𝐶 , 𝐷 ] = record
  { Obj  = Functor 𝐶 𝐷
  ; _⇒_ = NaturalTransformation 𝐶 𝐷
  ; id   = λ {F} → η (Fₘ F (id 𝐶))
  ; _∘_  = _∘ᵛ_
  ; _≈_  = λ (η α) (η β) → ∀ {X} → 𝐷 [ α {X = X} ≈ β ]
  }
