open import Level

module Limits.Equalizer {o m e : Level} where

open import Morphisms.Parallel
     
record Equalizer {𝐶 : Category o m e} (X Y : Obj 𝐶) (f g : 𝐶 [ X , Y ]) : Set (o ⊔ m ⊔ e) where
  open Category 𝐶 using (_⇒_)
  field
    𝐸 : Obj 𝐶
    𝑒𝑞 : 𝐸 ⇒ X
    commute₁ : 𝐶 [ f ∘ 𝑒𝑞 ≈ g ∘ 𝑒𝑞 ]
    𝑂 : Obj 𝐶
    𝑚 : 𝑂 ⇒ X
    commute₂ : 𝐶 [ f ∘ 𝑚 ≈ g ∘ 𝑚 ]
