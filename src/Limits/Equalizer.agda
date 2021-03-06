open import Level

module Limits.Equalizer {o m e : Level} where

open import Morphisms.Parallel
     
record Equalizer {πΆ : Category o m e} (X Y : Obj πΆ) (f g : πΆ [ X , Y ]) : Set (o β m β e) where
  open Category πΆ using (_β_)
  field
    πΈ : Obj πΆ
    ππ : πΈ β X
    commuteβ : πΆ [ f β ππ β g β ππ ]
    π : Obj πΆ
    π : π β X
    commuteβ : πΆ [ f β π β g β π ]
