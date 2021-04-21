open import Level

module Limits.Core { o₁ m₁ o₂ m₂ : Level } where

open import Categories.Core
open import Categories.Comma
open import Functors.Core hiding (_∘_)
open import NaturalTransformations.Core
open import Morphisms.Isomorphism

open Category using (Obj)

record Cone
  {𝐽 : Category o₁ m₁} {𝐶 : Category o₂ m₂}
  (F : Functor 𝐽 𝐶) : Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂) where
  open Functor F using (Fₒ)
  field
    -- Apex of the cone
    Apex : Obj 𝐶
    ψ : (X : Obj 𝐽) → 𝐶 [ Apex , Fₒ X ]

record Cocone
  {𝐽 : Category o₁ m₁} {𝐶 : Category o₂ m₂}
  (F : Functor 𝐽 𝐶) : Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂) where
  open Functor F using (Fₒ)
  field
    Apex : Obj 𝐶
    ψ : (X : Obj 𝐽) → 𝐶 [ Fₒ X , Apex ]

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
           → Category (o₁ ⊔ m₂) m₁ 
Cocone-↓ {𝐽} {𝐶} N F = F ↓ Δ
  where
    Δ : Functor 𝐽 𝐶
    Δ = ConstantFunctor {o₂} {m₂} {_} {o₁} {m₁} {𝐽} N

record Limit
  {𝐽 : Category o₁ m₁} {𝐶 : Category o₂ m₂} (F : Functor 𝐽 𝐶)
  {𝑈 : Cone F} {C : Cone F} : Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂) where
  open Category 𝐶 using (_⇒_; _∘_)
  open Functor F using (Fₒ)
  open Cone C renaming (Apex to N)
  open Cone 𝑈 renaming (Apex to L; ψ to ϕ)
  field
    lim : ∀ (X : Obj 𝐽) (𝑢 : N ⇒ L) → (ϕ X ∘ 𝑢) ≅ ψ X

record Colimit
  {𝐽 : Category o₁ m₁} {𝐶 : Category o₂ m₂} (F : Functor 𝐽 𝐶)
  {𝑈 : Cocone F} {C : Cocone F} : Set (o₁ ⊔ m₁ ⊔ o₂ ⊔ m₂) where
  open Category 𝐶 using (_⇒_; _∘_)
  open Functor F using (Fₒ)
  open Cocone C renaming (Apex to N)
  open Cocone 𝑈 renaming (Apex to L; ψ to ϕ)
  field
    colim : ∀ (X : Obj 𝐽) (𝑢 : L ⇒ N) → 𝑢 ∘ ϕ X ≅ ψ X
