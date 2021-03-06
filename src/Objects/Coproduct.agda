open import Level 
open import Categories.Core using (Category)

module Objects.Coproduct {o m e : Level} where

open import Categories.Core public

-- A B : Ob(š¶)
record Coproduct {š¶ : Category o m e} (A B : Category.Obj š¶) : Set (o ā m ā e) where
  open Category š¶ using (_ā_)
  field
    A+B : Obj š¶
    iā  : A ā A+B
    iā  : B ā A+B
    _ā_ : ā {C} ā A ā C ā B ā C ā A+B ā C
