module Properties.Universal where

open import Level
open import Categories.Core
open import Functors.Core hiding (_∘_)
open import Data.Product using (Σ; _,_)

private
  variable
    o₁ m₁ e₁ o₂ m₂ e₂ : Level

syntax UniversalMorphism X F = X Universal-⇒ F

record UniversalMorphism
  {𝑪 : Category o₁ m₁ e₁} {𝑫 : Category o₂ m₂ e₂}
  (X : Obj 𝑫) (F : Functor 𝑪 𝑫) : Set (o₁ ⊔ m₂) where
  constructor _,_
  open Functor F using (Fₒ)
  field
    A : Obj 𝑪
    𝑢 : 𝑫 [ X , Fₒ A ]


{-

Cannot pattern-matching telescopes in record declarations:
-> https://github.com/agda/agda/issues/4503

record UniversalProperty
  {𝑪 : Category o₁ m₁ e₁} {𝑫 : Category o₂ m₂ e₂}
  {F : Functor 𝑪 𝑫} {X : Obj 𝑫} {A′ : Obj 𝑪}
  ((A , 𝑢) : X Universal-⇒ F) (f : 𝑫 [ X , Functor.Fₒ F A′ ]) (h : 𝑪 [ A , A′ ])
  : Set (e₂) where
  field
    prop : 𝑫 [ f ≈ ? ]

-}

module _
  {𝑪 : Category o₁ m₁ e₁} {𝑫 : Category o₂ m₂ e₂}
  {F : Functor 𝑪 𝑫} {X : Obj 𝑫} {A′ : Obj 𝑪}
  ((A , 𝑢) : X Universal-⇒ F) (open Functor F using (Fₒ))
  (f : 𝑫 [ X , Fₒ A′ ]) (h : 𝑪 [ A , A′ ])
  where
    record UniversalProperty
      : Set (e₂) where
      open Category 𝑫 using (_∘_)
      open Functor F using (Fₘ)
      field
        commutes : 𝑫 [ f ≈ Fₘ h ∘ 𝑢 ]

