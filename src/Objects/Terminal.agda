open import Level
open import Categories.Core hiding (Obj)
open import Morphisms.Isomorphism using (CategoricalIsomorphism; refl)

module Objects.Terminal
  {o m e : Level}
  {πΆ : Category o m e}
  where

open import Properties.Universal hiding (Obj)

-- Terminal object with universal property
record Terminal : Set (o β m β e) where
  open Category πΆ
  field
    π : Obj
    ! : β {X : Obj} β X β π
    !-unique : β {X : Obj} (f : X β π) β f β !

-- Unique up to unique isomorphism
!ββ : (tβ tβ : Terminal) β πΆ [ Terminal.π tβ β Terminal.π tβ ]
!ββ
  record { π = πβ ; ! = !β ; !-unique = !-uniqueβ }
  record { π = πβ ; ! = !β ; !-unique = !-uniqueβ } =
  record
    { f = !β
    ; g = !β
    ; isoβ = {!!}
    ; isoα΅£ = {!!}
    }
