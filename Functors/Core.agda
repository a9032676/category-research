module Functors.Core where

open import Level
open import Function hiding (Inverse) renaming (_∘_ to _∘ᶠ_; id to idᶠ)

open import Categories.Core

private
  variable
    o m o' m' : Level

record Functor (C : Category o m) (D : Category o' m') : Set (o ⊔ m ⊔ o' ⊔ m') where
  eta-equality
  private module C = Category C
  private module D = Category D
  field
    Fₒ : C.Obj → D.Obj
    Fₘ : ∀ {A B : C.Obj} → (A C.⇒ B) → (Fₒ A D.⇒ Fₒ B)

  OppositeFunctor : ∀ C D → Set _
  OppositeFunctor C D = Functor C.op D.op

  -- Opposite functor
  op : OppositeFunctor C D
  op = record { Fₒ = Fₒ; Fₘ = Fₘ }

  -- Endo functor
  EndoFunctor : ∀ C → Set _
  EndoFunctor C = Functor C C

  -- Identity functor
  id : EndoFunctor C
  id = record { Fₒ = idᶠ; Fₘ = idᶠ }

  -- Cotravariant functor for some special cases only, just for instance: Constant functor, Covector ... etc.
  --ContravariantFunctorˡ : ∀ C D → Set _
  --ContravariantFunctorˡ C D = Functor o m o' m' C.op D

  --ContravariantFunctorʳ : ∀ C D → Set _
  --ContravariantFunctorʳ C D = Functor o m o' m' C D.op

  -- Constant functor
  ConstantFunctor : ∀ C D → Set _
  ConstantFunctor C D = Functor C D.constant

  constant : ConstantFunctor C D
  constant = record { Fₒ = Fₒ; Fₘ = λ A⇒B → Fₘ C.id }

  constant∘contraˡ : ConstantFunctor C.op D
  constant∘contraˡ = record { Fₒ = Fₒ; Fₘ = λ A⇒ᵒᵖB → Fₘ C.id }
  
  constant∘contraʳ : ConstantFunctor C D.op
  constant∘contraʳ = record { Fₒ = Fₒ; Fₘ = λ A⇒B → Fₘ C.id }
