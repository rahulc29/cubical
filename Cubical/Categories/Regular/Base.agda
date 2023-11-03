{-# OPTIONS --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Morphism
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation

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
    isCoequalizer x f g where
      module _ (x : ob) (f g : Hom[ x , y ]) where
        glues : (z' : ob) → Hom[ y , z' ] → Type ℓ'
        glues z' p = f ⋆ p ≡ g ⋆ p

        factorizes : Type (ℓ-max ℓ ℓ')
        factorizes = ∀ {w} (q : Hom[ y , w ]) → (glues w q) → ∃![ ! ∈ Hom[ w , z ] ] (q ⋆ ! ≡ p)
        
        isCoequalizer : Type (ℓ-max ℓ ℓ')
        isCoequalizer = glues z p × factorizes

  isPropIsRegularEpic : ∀ {y} {z} p → isProp (isRegularEpic {y} {z} p)
  isPropIsRegularEpic p = isPropPropTrunc

      
