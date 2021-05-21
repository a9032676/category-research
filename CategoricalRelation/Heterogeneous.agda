open import Level

module CategoricalRelation.Heterogeneous where

open import Categories.Core using (Category; Obj; _[_,_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

private
  variable
    o m e : Level

-- Heterogeneous identity
hid : {𝐶 : Category o m e} {A B : Obj 𝐶} → A ≡ B → 𝐶 [ A , B ]
hid {𝐶 = 𝐶} {A = A} p = subst (A ⇒_) p id
  where
    open Category 𝐶
