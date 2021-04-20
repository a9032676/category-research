open import Level

module Limits.Core { o₁ m₁ o₂ m₂ : Level } where

open import Categories.Core
open import Categories.Comma
open import Functors.Core
open import NaturalTransformations.Core

open Category using (Obj)

record Cone {𝐽 : Category o₁ m₁} {𝐶 : Category o₂ m₂} {F : Functor 𝐽 𝐶} : Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂) where
  open Functor F using (Fₒ)
  field
    N : Obj 𝐶
    ψ : {X : Obj 𝐽} → 𝐶 [ N , Fₒ X ]

record Cocone {𝐽 : Category o₁ m₁} {𝐶 : Category o₂ m₂} {F : Functor 𝐽 𝐶} : Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂) where
  open Functor F using (Fₒ)
  field
    N : Obj 𝐶
    ψ : {X : Obj 𝐽} → 𝐶 [ Fₒ X , N ]

-- Natural transformation version of cone from Δ(N) to F
Cone-η : {𝐽 : Category o₁ m₁} {𝐶 : Category o₂ m₂}
         (N : Obj 𝐶) (F : Functor 𝐽 𝐶)
         → Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂)
Cone-η {𝐽 = 𝐽} {𝐶 = 𝐶} N F = [ 𝐽 , 𝐶 ]⟨ Δ N , F ⟩
  where
    private module F = Functor F

-- Natural transformation version of co-cone from F to Δ(N)
Cocone-η : {𝐽 : Category o₁ m₁} {𝐶 : Category o₂ m₂}
           (N : Obj 𝐶) (F : Functor 𝐽 𝐶)
           → Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂)
Cocone-η {𝐽 = 𝐽} {𝐶 = 𝐶} N F = [ 𝐽 , 𝐶 ]⟨ F , Δ N ⟩
  where
    private module F = Functor F

-- Comma category version of cone (Δ ↓ F) with object (N, ψ)
Cone-↓ : {𝐽 : Category o₁ m₁} {𝐶 : Category o₂ m₂}
         (N : Obj 𝐶) (F : Functor 𝐽 𝐶)
         → Category (o₁ ⊔ m₂) m₁
Cone-↓ {𝐽} {𝐶} N F = Δ ↓ F
  where
    Δ : Functor 𝐽 𝐶
    Δ = ConstantFunctor {o₂} {m₂} {_} {o₁} {m₁} {𝐽} N

-- Comma category version of co-cone (F ↓ Δ) with object (N, ψ)
Cocone-↓ : {𝐽 : Category o₁ m₁} {𝐶 : Category o₂ m₂}
         (N : Obj 𝐶) (F : Functor 𝐽 𝐶)
         → Category _ _ 
Cocone-↓ {𝐽} {𝐶} N F = F ↓ Δ
  where
    Δ : Functor 𝐽 𝐶
    Δ = ConstantFunctor {o₂} {m₂} {_} {o₁} {m₁} {𝐽} N


--record Limit (𝐼 : Category o₁ m₁) : Set (o₁ ⊔ m₁) where
--  field
--    todo : {!!}
