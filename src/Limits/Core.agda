open import Level
open import Categories.Core

module Limits.Core
  {o₁ m₁ e₁ o₂ m₂ e₂ : Level}
  {𝐽 𝐷 : Category o₁ m₁ e₁}
  {𝐶 : Category o₂ m₂ e₂}
  where

open import Categories.Comma
open import Categories.Sets
open import Categories.2-Category renaming ([_,_] to Hom[_,_])
open import Functors.Core hiding (_∘_)
open import NaturalTransformations.Core

open Category using (Obj)

record Cone (F : Functor 𝐽 𝐶) : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
  open Functor F using (Fₒ)
  field
    -- Apex of the cone
    Apex : Obj 𝐶
    ψ : (X : Obj 𝐽) → 𝐶 [ Apex , Fₒ X ]

record Cocone (F : Functor 𝐽 𝐶) : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂) where
  open Functor F using (Fₒ)
  field
    Apex : Obj 𝐶
    ψ : (X : Obj 𝐽) → 𝐶 [ Fₒ X , Apex ]

-- Natural transformation version of cone from Δ(N) to F
Cone-η : (N : Obj 𝐶) (F : Functor 𝐽 𝐶) → Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂)
Cone-η N F = [ 𝐽 , 𝐶 ]⟨ Δ N , F ⟩

-- Natural transformation version of co-cone from F to Δ(N)
Cocone-η : (N : Obj 𝐶) (F : Functor 𝐽 𝐶) → Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ o₂ ⊔ m₂ ⊔ e₂)
Cocone-η N F = [ 𝐽 , 𝐶 ]⟨ F , Δ N ⟩

-- Comma category version of cone (Δ ↓ F) with object (N, ψ)
Cone-↓ : (N : Obj 𝐶) (F : Functor 𝐽 𝐶) → Category (o₁ ⊔ m₂) m₁ (o₁ ⊔ e₁)
Cone-↓ N F = Δ ↓ F
  where
    Δ : Functor 𝐽 𝐶
    Δ = ConstantFunctor N

-- Comma category version of co-cone (F ↓ Δ) with object (N, ψ)
Cocone-↓ : (N : Obj 𝐶) (F : Functor 𝐽 𝐶) → Category (o₁ ⊔ m₂) m₁ (o₁ ⊔ e₁) 
Cocone-↓ N F = F ↓ Δ
  where
    Δ : Functor 𝐽 𝐶
    Δ = ConstantFunctor N

-- Limit also called a universal cone over some functor F
record Limit (F : Functor 𝐽 𝐶) {𝑈 : Cone F} {C : Cone F} : Set (o₁ ⊔ m₂ ⊔ e₂) where
  open Category 𝐶 using (_⇒_; _∘_)
  open Functor F using (Fₒ)
  open Cone C renaming (Apex to N)
  open Cone 𝑈 renaming (Apex to L; ψ to ϕ)
  field
    lim : ∀ (X : Obj 𝐽) (𝑢 : N ⇒ L) → 𝐶 [ (ϕ X ∘ 𝑢) ≈ ψ X ]

record Colimit (F : Functor 𝐽 𝐶) {𝑈 : Cocone F} {C : Cocone F} : Set (o₁ ⊔ m₂ ⊔ e₂) where
  open Category 𝐶 using (_⇒_; _∘_)
  open Functor F using (Fₒ)
  open Cocone C renaming (Apex to N)
  open Cocone 𝑈 renaming (Apex to L; ψ to ϕ)
  field
    colim : ∀ (X : Obj 𝐽) (𝑢 : L ⇒ N) → 𝐶 [ (𝑢 ∘ ϕ X) ≈ ψ X ]

-- Local definition of (co)limit of Set-valued functor in presheaf category
module _ (F : Functor (𝐷 ᵒᵖ) (𝑆𝑒𝑡 o₂)) (✶ : Obj (𝑆𝑒𝑡 o₂)) where
  --open import Objects.Terminal {𝐶 = 𝑆𝑒𝑡 o₂} renaming (𝟙 to ✶)

  pt : Functor (𝐷 ᵒᵖ) (𝑆𝑒𝑡 o₂)
  pt = record { Fₒ = λ d → ✶ ; Fₘ = λ _ ✶ → ✶ }

  record Limit-SVF : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ suc o₂) where
    field
      lim : Hom[ 𝐷 ᵒᵖ , 𝑆𝑒𝑡 o₂ ] [ pt , F ]

  record Colimit-SVF : Set (o₁ ⊔ m₁ ⊔ e₁ ⊔ suc o₂) where
    field
      colim : Hom[ 𝐷 ᵒᵖ , 𝑆𝑒𝑡 o₂ ] [ F , pt ]
