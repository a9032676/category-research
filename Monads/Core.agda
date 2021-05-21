module Monads.Core where

open import Level

open import Categories.Core
open import Functors.Core
open import Functors.Adjunction
open import NaturalTransformations.Core

private
  variable
    o m e : Level

record Monad (𝐶 : Category o m e) (𝑇 : End⟨ 𝐶 ⟩) : Set (o ⊔ m ⊔ e) where
  field
    η : [ 𝐶 , 𝐶 ]⟨ Id 𝐶 , 𝑇 ⟩
    μ : [ 𝐶 , 𝐶 ]⟨ 𝑇 ² , 𝑇 ⟩
