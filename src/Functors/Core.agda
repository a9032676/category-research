module Functors.Core where

open import Level
open import Function hiding (Inverse) renaming (_∘_ to _∘ᶠ_; id to idᶠ)
open import Relation.Binary using (Rel)
open import CategoricalRelation.Heterogeneous

open import Categories.Core hiding (op; id) public

private
  variable
    o₁ m₁ e₁ o₂ m₂ e₂ o₃ m₃ e₃ : Level

record Functor (𝐶 : Category o₁ m₁ e₁) (𝐷 : Category o₂ m₂ e₂) : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
  eta-equality
  private module 𝐶 = Category 𝐶
  private module 𝐷 = Category 𝐷
  field
    Fₒ : Obj 𝐶 → Obj 𝐷
    Fₘ : ∀ {A B : Obj 𝐶} → 𝐶 [ A , B ] → 𝐷 [ Fₒ A , Fₒ B ]
    
  OppositeFunctor : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂)
  OppositeFunctor = Functor 𝐶.op 𝐷.op

  -- Opposite functor
  op : OppositeFunctor
  op = record { Fₒ = Fₒ; Fₘ = Fₘ }

  -- Cotravariant functor for some specific cases only, just for instance: Constant functor, Covector ... etc.
  --ContravariantFunctorˡ : ∀ C D → Set _
  --ContravariantFunctorˡ C D = Functor o m o' m' C.op D

  --ContravariantFunctorʳ : ∀ C D → Set _
  --ContravariantFunctorʳ C D = Functor o m o' m' C D.op

record _≡F_
  {𝐶 : Category o₁ m₁ e₁} {𝐷 : Category o₂ m₂ e₂}
  (F G : Functor 𝐶 𝐷) : Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ e₂) where
  open Functor F
  open Functor G renaming (Fₒ to Gₒ; Fₘ to Gₘ)
  field
    eqₒ : ∀ {X : Obj 𝐶} → Fₒ X ≡ Gₒ X
    eqₘ :
      ∀ {X Y : Obj 𝐶} (f : 𝐶 [ X , Y ])
      → 𝐷 [ hid {𝐶 = 𝐷} eqₒ ∘ Fₘ f ≈ Gₘ f ∘ hid {𝐶 = 𝐷} eqₒ ]

private
  variable
    𝐶 : Category o₁ m₁ e₁
    𝐷 : Category o₂ m₂ e₂
    𝐸 : Category o₃ m₃ e₃

-- Endo functor
EndoFunctor : Category o₁ m₁ e₁ → Set (o₁ ⊔ m₁ ⊔ e₁)
EndoFunctor 𝐶 = Functor 𝐶 𝐶

syntax EndoFunctor 𝐶 = End⟨ 𝐶 ⟩

-- Identity functor
IdentityFunctor : EndoFunctor 𝐶
IdentityFunctor = record { Fₒ = idᶠ; Fₘ = idᶠ }

Id : ∀ (𝐶 : Category o₁ m₁ e₁) → EndoFunctor 𝐶
Id 𝐶 = IdentityFunctor {𝐶 = 𝐶}

open Category using (Obj) renaming (id to idᶜ)

-- Constant functor
ConstantFunctor : (X : Obj 𝐷) → Functor 𝐶 𝐷
ConstantFunctor {𝐷 = 𝐷} X = record { Fₒ = λ _ → X; Fₘ = λ A⇒B → idᶜ 𝐷 }

syntax ConstantFunctor X = Δ X

--constant∘contraˡ : Functor C.op D
--constant∘contraˡ = record { Fₒ = Fₒ; Fₘ = λ A⇒ᵒᵖB → Fₘ C.id }
 
--constant∘contraʳ : Functor C D.op
--constant∘contraʳ = record { Fₒ = Fₒ; Fₘ = λ A⇒B → Fₘ C.id }

module Syntax where

  infixr 9 _∘_

  _∘_ : (F : Functor 𝐶 𝐷) (G : Functor 𝐷 𝐸) → Functor 𝐶 𝐸
  _∘_
    record { Fₒ = Fₒ₁ ; Fₘ = Fₘ₁ }
    record { Fₒ = Fₒ₂ ; Fₘ = Fₘ₂ }
    = record { Fₒ = Fₒ₂ ∘ᶠ Fₒ₁ ; Fₘ = Fₘ₂ ∘ᶠ Fₘ₁ }

  _² : (F : Functor 𝐶 𝐶) → Functor 𝐶 𝐶
  F ² = F ∘ F
