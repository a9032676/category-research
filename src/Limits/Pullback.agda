module Limits.Pullback where


open import Level
open import Categories.Core
open import Functors.Core hiding (_∘_)
open import Limits.Core using (Cone; Limit)
open import Properties.Universal
open import Morphisms.Universal using (UM⟨_,_⟩)

private
  variable
    o₁ m₁ e₁ : Level

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
    commute : CommutativeSquare {𝐶 = 𝐶} 𝑝₁ 𝑝₂ f g

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
