{-# OPTIONS --safe #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Data.Sigma

module Cubical.Categories.Limits.Coequalizers where

private
  variable
    ℓ ℓ' : Level

module _ {C : Category ℓ ℓ'} where
  open Category C
  private
    variable
      A B D E : ob
      f g : Hom[ A , B ]

  -- Inspired by the corresponding development at the 1lab
  record IsCoequalizer {E} (f g : Hom[ A , B ]) (coeq : Hom[ B , E ]) : Type (ℓ-max ℓ ℓ') where
    field
      glues : f ⋆ coeq ≡ g ⋆ coeq
      univProp :
               ∀ {D} (q : Hom[ B , D ])
               → f ⋆ q ≡ g ⋆ q
               ----------------------------------------
               → ∃![ ! ∈ Hom[ E , D ] ] (coeq ⋆ ! ≡ q)

  record Coequalizer (f g : Hom[ A , B ]) : Type (ℓ-max ℓ ℓ') where
    field
      coapex : ob
      coeq   : Hom[ B , coapex ]
      isCoequalizer : IsCoequalizer f g coeq
    open IsCoequalizer isCoequalizer public
