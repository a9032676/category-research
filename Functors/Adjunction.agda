module Functors.Adjunction where

open import Level

open import Categories.Core
open import Functors.Core
open import Morphisms.Isomorphism

private
  variable
    o₁ m₁ o₂ m₂ : Level

-- Functor F left adjoint to G
syntax AdjointFunctor F G = F ⊣ G

record AdjointFunctor
  {C : Category o₁ m₁} {D : Category o₂ m₂}
  (F : Functor D C) (G : Functor C D)
  {X : Category.Obj C} {Y : Category.Obj D} : Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂) where
  private module C = Category C
  private module D = Category D
  private module F = Functor F
  private module G = Functor G
  field
    -- Unit
    η : Y D.⇒ G.Fₒ X
    -- Counit
    ε : F.Fₒ Y C.⇒ X
    -- Adjunction
    ϕ : ε ≅ η

