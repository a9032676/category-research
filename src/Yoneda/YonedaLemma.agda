open import Level

module Yoneda.YonedaLemma {o m e : Level} where

open import Functors.Homfunctor public
open import Transformations.Core public

module Yoneda (C : Category o m e) {X : Obj C} {F : Functor C (đđđĄ m)} where
  open Functor F

  toYoneda : [ C , đđđĄ m ]â¨ Hom C [ X ,â] , F âŠ â Fâ X
  toYoneda (Îˇ Îą) = Îą (id C)

  fromYoneda : Fâ X â [ C , đđđĄ m ]â¨ Hom C [ X ,â] , F âŠ
  fromYoneda u = Îˇ (Îť f â (Fâ f) u)
