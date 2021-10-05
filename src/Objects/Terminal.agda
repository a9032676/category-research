open import Level
open import Categories.Core hiding (Obj)
open import Limits.Core
open import Morphisms.Isomorphism using (CategoricalIsomorphism; refl)

module Objects.Terminal
  {o m e : Level}
  {𝐶 : Category o m e}
  where

open import Properties.Universal

-- Terminal object with universal property
record Terminal : Set (o ⊔ m ⊔ e) where
  open Category 𝐶
  field
    𝟙 : Obj
    ! : ∀ {X : Obj} → X ⇒ 𝟙
    !-unique : ∀ {X : Obj} (f : X ⇒ 𝟙) → f ≈ !

-- Unique up to unique isomorphism
!↑≅ : (t₁ t₂ : Terminal) → 𝐶 [ Terminal.𝟙 t₁ ≅ Terminal.𝟙 t₂ ]
!↑≅
  record { 𝟙 = 𝟙₁ ; ! = !₁ ; !-unique = !-unique₁ }
  record { 𝟙 = 𝟙₂ ; ! = !₂ ; !-unique = !-unique₂ } =
  record
    { f = !₂
    ; g = !₁
    ; isoₗ = {!!}
    ; isoᵣ = {!!}
    }
