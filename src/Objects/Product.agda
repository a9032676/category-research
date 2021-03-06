open import Level
open import Categories.Core using (Category)

module Objects.Product {o m e : Level} (š¶ : Category o m e) where

open Category š¶ using (Obj; _ā_)

syntax Product A B = A Ć B

-- A B : Ob(š¶)
record Product (A B : Obj) : Set (o ā m) where
  field
    AĆB   : Obj
    Ļā    : AĆB ā A
    Ļā    : AĆB ā B
    āØ_,_ā© : ā {C} ā C ā A ā C ā B ā C ā AĆB
