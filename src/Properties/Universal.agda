open import Level
open import Categories.Core
open import Functors.Core hiding (_∘_)

module Properties.Universal
  {o₁ m₁ e₁ o₂ m₂ e₂ : Level}
  {𝐶 : Category o₁ m₁ e₁} {𝐷 : Category o₂ m₂ e₂}
  {F : Functor 𝐶 𝐷} {X : Obj 𝐷} {A′ : Obj 𝐶}
  where

open import Data.Product using (Σ; _,_)
open import Morphisms.Universal

{-
  Cannot pattern-matching telescopes in record declarations:
  -> https://github.com/agda/agda/issues/4503
-}

module _
  ((UM⟨ A , 𝑢 ⟩) : X 𝒰-⇒ F) (open Functor F using (Fₒ))
  (f : 𝐷 [ X , Fₒ A′ ]) (h : 𝐶 [ A , A′ ])
  where
    record UniversalProperty : Set e₂ where
      open Category 𝐷 using (_∘_)
      open Functor F using (Fₘ)
      field
        commutes : 𝐷 [ Fₘ h ∘ 𝑢 ≈ f ]

module _
  ((UM!⟨ A , 𝑢 ⟩) : X 𝒰-⇒! F) (open Functor F using (Fₒ))
  (f : 𝐷 [ Fₒ A′ , X ]) (h : 𝐶 [ A′ , A ])
  where
    record DualUniversalProperty : Set e₂ where
      open Category 𝐷 using (_∘_)
      open Functor F using (Fₘ)
      field
        commutes : 𝐷 [ 𝑢 ∘ (Fₘ h) ≈ f ]

