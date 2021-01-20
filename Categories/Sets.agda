module Categories.Sets where

open import Level

open import Categories.Core


-- Category of Sets
𝒮ℯ𝓉 : (o : Level) → Category (suc o) o
𝒮ℯ𝓉 o = record
  { Obj  = Set o
  ; _⇒_ = λ A B → (A → B)
  ; id   = λ x → x
  ; _∘_  = λ x y z → x (y z)
  }
