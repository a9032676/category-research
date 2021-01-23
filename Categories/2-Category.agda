module Categories.2-Category where

open import Level
open import Function hiding (Inverse) renaming (_∘_ to _∘ᶠ_; id to idᶠ)

open import Categories.Core
open import Functors.Core
open import NaturalTransformations.Core

open Functor using (Fₒ; Fₘ)
open Category using (id; _∘_)
open NaturalTransformation using (η)

private
  variable
    o m o' m' : Level

-- Cat Category
Cat : Category (suc (o ⊔ m)) (o ⊔ m)
Cat {o} {m} = record
  { Obj  = Category o m
  ; _⇒_ = Functor
  ; id   = record
    { Fₒ = idᶠ
    ; Fₘ = idᶠ
    }
  ; _∘_ = λ fbc fab → record
    { Fₒ = Fₒ fbc ∘ᶠ Fₒ fab
    ; Fₘ = Fₘ fbc ∘ᶠ Fₘ fab
    }
  }

-- Functor Category
[_,_] : Category o m → Category o' m' → Category (o ⊔ m ⊔ o' ⊔ m') (o ⊔ m ⊔ o' ⊔ m')
[ C , D ] = record
  { Obj  = Functor C D
  ; _⇒_ = NaturalTransformation C D
  ; id   = λ {F} → record { η = Fₘ F (id C) }
  ; _∘_  = _∘ᵛ_
  }
