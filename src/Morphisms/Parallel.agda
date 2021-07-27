open import Level

module Morphisms.Parallel {o m e : Level} where

open import Categories.Core

syntax ParallelMorphism X Y = X ⇉ Y

record ParallelMorphism {𝐶 : Category o m e} (X Y : Obj 𝐶) : Set m where
  constructor ⇉⟨_,_⟩
  open Category 𝐶
  field
    f : X ⇒ Y
    g : X ⇒ Y

_[_⇉_] : (𝐶 : Category o m e) (X Y : Obj 𝐶) → Set m
𝐶 [ X ⇉ Y ] = ParallelMorphism {𝐶 = 𝐶} X Y
