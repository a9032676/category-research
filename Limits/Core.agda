module Limits.Core where

open import Level

open import Categories.Core
open import Functors.Core
open import NaturalTransformations.Core

private
  variable
    o₁ m₁ o₂ m₂ : Level

open Category using (Obj)

-- ψ is a natural transformation from Δ(N) to F
Cone : (𝐽 : Category o₁ m₁) (𝐶 : Category o₂ m₂)
       (F : Functor 𝐽 𝐶) (N : Obj 𝐶)
       → Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂)
Cone 𝐽 𝐶 F N = [ 𝐽 , 𝐶 ]⟨ Δ N , F ⟩
  where
    private module F = Functor F

Cocone : (𝐽 : Category o₁ m₁) (𝐶 : Category o₂ m₂)
         (F : Functor 𝐽 𝐶) (N : Obj 𝐶)
         → Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂)
Cocone 𝐽 𝐶 F N = [ 𝐽 , 𝐶 ]⟨ F , Δ N ⟩
  where
    private module F = Functor F

record Limit (𝐼 : Category o₁ m₁) : Set (o₁ ⊔ m₁) where
  field
    todo : {!!}
