open import Level

module Functors.Adjunction {o m e : Level} where

open import Categories.Sets
open import Categories.Product using (ProductCategory; _,_; _Ãáµ_)
open import Functors.Core using (Functor)
open import Functors.Homfunctor using (Hom[_,_])
open import Morphisms.Isomorphism using (NaturalIsomorphism)

-- Functor F is left adjoint to G, and G is right adjoint to F
syntax HomSetAdjointFunctor F G = F â£ G

record HomSetAdjointFunctor
  {ð¶ ð· : Category o m e}
  (F : Functor ð· ð¶) (G : Functor ð¶ ð·)
  : Set (suc (o â suc m â e)) where
  private module ð¶ = Category ð¶ using (_â_)
  private module ð· = Category ð· using (_â_; op)
  open Functor F using (Fâ; Fâ)
  open Functor G renaming (Fâ to Gâ; Fâ to Gâ)
  instance
    homá¶â¨Fâ,ââ© : Hom[ ð·.op , ð¶ ]
    homá¶â¨Fâ,ââ© = record
               { Fâ = Î» (Y , X) â ð¶ [ Fâ Y , X ]
               ; Fâ = Î» (g , f) h â f ð¶.â h ð¶.â (Fâ g) }
    homá´°â¨â,Gââ© : Hom[ ð·.op , ð¶ ]
    homá´°â¨â,Gââ© = record
               { Fâ = Î» (Y , X) â ð· [ Y , Gâ X ]
               ; Fâ = Î» (g , f) i â (Gâ f) ð·.â i ð·.â g }
  field
    -- Adjunction
    Ï : [ ð·.op Ã ð¶ , ððð¡ m ]â¨ homá¶â¨Fâ,ââ© â homá´°â¨â,Gââ© â©
