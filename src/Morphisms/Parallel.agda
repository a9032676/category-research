module Morphisms.Parallel where

open import Level
open import Categories.Core

private
  variable
    o m e : Level

syntax ParallelMorphism X Y = X ⇉ Y

record ParallelMorphism {𝐶 : Category o m e} (X Y : Obj 𝐶) : Set m where
  constructor ⇉⟨_,_⟩
  open Category 𝐶
  field
    f : X ⇒ Y
    g : X ⇒ Y
