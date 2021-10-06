open import Level

module Functors.Adjunction {o m e : Level} where

open import Categories.Sets
open import Categories.Product using (ProductCategory; _,_; _×ᵖ_)
open import Functors.Core using (Functor)
open import Functors.Homfunctor using (Hom[_,_])
open import Morphisms.Isomorphism using (NaturalIsomorphism)

-- Functor F is left adjoint to G, and G is right adjoint to F
syntax HomSetAdjointFunctor F G = F ⊣ G

record HomSetAdjointFunctor
  {𝐶 𝐷 : Category o m e}
  (F : Functor 𝐷 𝐶) (G : Functor 𝐶 𝐷)
  : Set (suc (o ⊔ suc m ⊔ e)) where
  private module 𝐶 = Category 𝐶 using (_∘_)
  private module 𝐷 = Category 𝐷 using (_∘_; op)
  open Functor F using (Fₒ; Fₘ)
  open Functor G renaming (Fₒ to Gₒ; Fₘ to Gₘ)
  instance
    homᶜ⟨F─,─⟩ : Hom[ 𝐷.op , 𝐶 ]
    homᶜ⟨F─,─⟩ = record
               { Fₒ = λ (Y , X) → 𝐶 [ Fₒ Y , X ]
               ; Fₘ = λ (g , f) h → f 𝐶.∘ h 𝐶.∘ (Fₘ g) }
    homᴰ⟨─,G─⟩ : Hom[ 𝐷.op , 𝐶 ]
    homᴰ⟨─,G─⟩ = record
               { Fₒ = λ (Y , X) → 𝐷 [ Y , Gₒ X ]
               ; Fₘ = λ (g , f) i → (Gₘ f) 𝐷.∘ i 𝐷.∘ g }
  field
    -- Adjunction
    ϕ : [ 𝐷.op × 𝐶 , 𝑆𝑒𝑡 m ]⟨ homᶜ⟨F─,─⟩ ≅ homᴰ⟨─,G─⟩ ⟩
