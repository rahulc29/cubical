module Cubical.Categories.Regular.ExactCompletion where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Regular.Base
open import Cubical.Categories.Regular.Exact

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where

  open Category C
  
  module PseduoEquivRelation where

    record PseudoEquivRelation : Type _ where
      field
        dom : ob
        cod : ob
        p₁ : Hom[ dom , cod ]
        p₂ : Hom[ dom , cod ]
        isReflexive : ∃[ r ∈ Hom[ cod , dom ] ] (r ⋆ p₁ ≡ id) × (r ⋆ p₂ ≡ id)
        isSymmetric : ∃[ σ ∈ Hom[ dom , dom ] ] (σ ⋆ p₁ ≡ p₂) × (σ ⋆ p₂ ≡ p₁)
        isTransitive : {!!}
