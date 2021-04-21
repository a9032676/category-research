module Functors.Core where

open import Level
open import Function hiding (Inverse) renaming (_∘_ to _∘ᶠ_; id to idᶠ)

open import Categories.Core

private
  variable
    o₁ m₁ o₂ m₂ o₃ m₃ : Level

record Functor (C : Category o₁ m₁) (D : Category o₂ m₂) : Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂) where
  eta-equality
  private module C = Category C
  private module D = Category D
  field
    Fₒ : C.Obj → D.Obj
    Fₘ : ∀ {A B : C.Obj} → (A C.⇒ B) → (Fₒ A D.⇒ Fₒ B)

  OppositeFunctor : ∀ C D → Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂)
  OppositeFunctor C D = Functor C.op D.op

  -- Opposite functor
  op : OppositeFunctor C D
  op = record { Fₒ = Fₒ; Fₘ = Fₘ }

  -- Cotravariant functor for some specific cases only, just for instance: Constant functor, Covector ... etc.
  --ContravariantFunctorˡ : ∀ C D → Set _
  --ContravariantFunctorˡ C D = Functor o m o' m' C.op D

  --ContravariantFunctorʳ : ∀ C D → Set _
  --ContravariantFunctorʳ C D = Functor o m o' m' C D.op

private
  variable
    C : Category o₁ m₁
    D : Category o₂ m₂
    E : Category o₃ m₃


-- Endo functor
EndoFunctor : Category o₁ m₁ → Set (o₁ ⊔ m₁)
EndoFunctor {o₁ = o₁} {m₁ = m₁} C = Functor C C

-- Identity functor
IdentityFunctor : EndoFunctor C
IdentityFunctor = record { Fₒ = idᶠ; Fₘ = idᶠ }

open Category using (Obj) renaming (id to idᶜ)

-- Constant functor
ConstantFunctor : (X : Obj D) → Functor C D
ConstantFunctor {D = D} X = record { Fₒ = λ _ → X; Fₘ = λ A⇒B → idᶜ D }

syntax ConstantFunctor X = Δ X

--constant∘contraˡ : Functor C.op D
--constant∘contraˡ = record { Fₒ = Fₒ; Fₘ = λ A⇒ᵒᵖB → Fₘ C.id }
 
--constant∘contraʳ : Functor C D.op
--constant∘contraʳ = record { Fₒ = Fₒ; Fₘ = λ A⇒B → Fₘ C.id }

infixr 9 _∘_

_∘_ : (F : Functor C D) (G : Functor D E) → Functor C E
_∘_
  record { Fₒ = Fₒ₁ ; Fₘ = Fₘ₁ }
  record { Fₒ = Fₒ₂ ; Fₘ = Fₘ₂ }
  = record { Fₒ = Fₒ₂ ∘ᶠ Fₒ₁ ; Fₘ = Fₘ₂ ∘ᶠ Fₘ₁ }
