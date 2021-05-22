module Categories.Core where

open import Level
open import Relation.Binary using (REL; Rel)
open import Relation.Binary.PropositionalEquality
open import Function hiding (Inverse) renaming (_∘_ to _∘ᶠ_; id to idᶠ)

record Category (o m e : Level) : Set (suc (o ⊔ m ⊔ e)) where
  eta-equality
  -- Cause bug, declaration is ignored by Agda
  infix  4 _≈_ _⇒_
  infixr 9 _∘_
  
  field
    Obj  : Set o
    _⇒_ : Rel Obj m
    id   : ∀ {A} → A ⇒ A
    _∘_  : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
    _≈_  : ∀ {A B} → Rel (A ⇒ B) e

  -- Opposite category
  op : Category o m e
  op = record
    { Obj  = Obj
    ; _⇒_ = flip _⇒_
    ; id   = id
    ; _∘_  = flip _∘_
    ; _≈_  = flip _≈_
    }

private
  variable
    o m e : Level

module Syntaxes (𝐶 : Category o m e) where
  open Category 𝐶 using (Obj; _⇒_; _∘_; _≈_)

  _[_,_] : (A B : Obj) → Set m
  _[_,_] = _⇒_

  _[_∘_] : {A B C : Obj} (g : B ⇒ C) (f : A ⇒ B) → A ⇒ C
  _[_∘_] = _∘_
  
  _[_≈_] : {A B : Obj} (f g : A ⇒ B) → Set e
  _[_≈_] = _≈_

open Syntaxes public

CommutativeSquare :
  {𝐶 : Category o m e} {A B C D : Category.Obj 𝐶}
  (f : 𝐶 [ A , B ]) (g : 𝐶 [ A , C ])
  (h : 𝐶 [ B , D ]) (i : 𝐶 [ C , D ])
  → Set e
CommutativeSquare {𝐶 = 𝐶} f g h i = h ∘ f ≈ i ∘ g
  where
    open Category 𝐶 using (_∘_; _≈_)

record Inverse {𝐶 : Category o m e} : Set (suc (o ⊔ m)) where
  open Category 𝐶 using (_⇒_)
  field
    inv : ∀ {A B} → A ⇒ B → B ⇒ A

open Category hiding (_⇒_; _∘_; _≈_) public
