module Limits.Pushout where

open import Level
open import Categories.Core
open import Functors.Core hiding (_∘_)
open import Properties.Universal
open import Morphisms.Universal using (UM⟨_,_⟩)

private
  variable
    o₁ m₁ e₁ : Level

syntax Pushout X Y Z = X +[ Z ] Y
infix 5 Push⟨_,_,_⟩

record Pushout
  {𝐶 : Category o₁ m₁ e₁} (X Y Z : Obj 𝐶)
  {f : 𝐶 [ Z , X ]} {g : 𝐶 [ Z , Y ]}
  : Set (o₁ ⊔ m₁ ⊔ e₁) where
  constructor Push⟨_,_,_⟩
  field
    P  : Obj 𝐶
    𝑖₁ : 𝐶 [ X , P ]
    𝑖₂ : 𝐶 [ Y , P ]
  field
    commute : 𝐶 [ 𝑖₁ ∘ f ≈ 𝑖₂ ∘ g ]

  module _
    ((record { P = Q ; 𝑖₁ = 𝑗₁ ; 𝑖₂ = 𝑗₂ })
    : Pushout {𝐶 = 𝐶} X Y Z {f = f} {g = g})
    (𝑢 : 𝐶 [ P , Q ])
    where
      open Category 𝐶

      record Pushout-UniversalProperty : Set e₁ where
        field
          uni-prop₁ : 𝑢 ∘ 𝑖₁ ≈ 𝑗₁
          uni-prop₂ : 𝑢 ∘ 𝑖₂ ≈ 𝑗₂
