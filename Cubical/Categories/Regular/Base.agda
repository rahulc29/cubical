{-# OPTIONS --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Morphism
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Categories.Limits.Coequalizers

module Cubical.Categories.Regular.Base where

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where
  open Category C
  private
    variable
      x y z w : ob

  isRegularEpic : Hom[ y , z ] → Type (ℓ-max ℓ ℓ')
  isRegularEpic {y} {z} p =
    ∃[ x ∈ ob ]
    ∃[ f ∈ Hom[ x , y ] ]
    ∃[ g ∈ Hom[ x , y ] ]
    IsCoequalizer {C = C} f g p

  isPropIsRegularEpic : ∀ {y} {z} p → isProp (isRegularEpic {y} {z} p)
  isPropIsRegularEpic p = isPropPropTrunc
