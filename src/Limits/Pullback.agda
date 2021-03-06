module Limits.Pullback where

open import Level
open import Properties.Universal

private
  variable
    o₁ m₁ e₁ : Level
    
syntax Pullback X Y Z = X ×[ Z ] Y
infix 5 Pull⟨_,_,_⟩

record Pullback 
  {𝐶 : Category o₁ m₁ e₁} (X Y Z : Obj 𝐶)
  {f : 𝐶 [ X , Z ]} {g : 𝐶 [ Y , Z ]}
  : Set (o₁ ⊔ m₁ ⊔ e₁) where
  constructor Pull⟨_,_,_⟩
  field
    P  : Obj 𝐶
    𝑝₁ : 𝐶 [ P , X ]
    𝑝₂ : 𝐶 [ P , Y ]
  field
    commute : 𝐶 [ f ∘ 𝑝₁ ≈ g ∘ 𝑝₂ ]

  module _
    ((record { P = Q ; 𝑝₁ = 𝑞₁ ; 𝑝₂ = 𝑞₂ })
    : Pullback {𝐶 = 𝐶} X Y Z {f = f} {g = g})
    (𝑢 : 𝐶 [ Q , P ])
    where
      open Category 𝐶

      record Pullback-UniversalProperty : Set e₁ where
        field
          uni-prop₁ : 𝑝₁ ∘ 𝑢 ≈ 𝑞₁
          uni-prop₂ : 𝑝₂ ∘ 𝑢 ≈ 𝑞₂
