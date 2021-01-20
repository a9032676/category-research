module Categories.Core where

open import Level
open import Relation.Binary using (REL; Rel)
open import Function hiding (Inverse) renaming (_∘_ to _∘ᶠ_; id to idᶠ)


record Category (o m : Level) : Set (suc (o ⊔ m)) where
  eta-equality
  -- Cause bug, declaration is ignored by Agda
  infixr 20 _∘_
  field
    Obj  : Set o
    _⇒_ : Rel Obj m
    id   : ∀ {A} → A ⇒ A
    _∘_  : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)

  -- Opposite category
  op : Category o m
  op = record { Obj = Obj; _⇒_ = flip _⇒_; id = id; _∘_ = flip _∘_ }

  -- Constant category
  constant : Category o m
  constant = record { Obj = Obj; _⇒_ = λ a _ → a ⇒ a; id = id; _∘_ = λ _ → idᶠ }

record Inverse {o m : Level} (C : Category o m) : Set (suc (o ⊔ m)) where
  open Category C public
  field
    inv : ∀ {A B} → A ⇒ B → B ⇒ A

