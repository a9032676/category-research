module Categories.Sets where

open import Level
open import Categories.Core public

open import Relation.Binary.PropositionalEquality using (_≡_)

-- Category of Sets
𝑆𝑒𝑡 : (o : Level) → Category (suc o) o o
𝑆𝑒𝑡 o = record
  { Obj  = Set o
  ; _⇒_ = λ A B → (A → B)
  ; id   = λ x → x
  ; _∘_  = λ x y z → x (y z)
  ; _≈_  = _≡_
  }
