{-# OPTIONS #-}
module Cubical.Categories.Regular.InternalRelation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Morphism
open import Cubical.Categories.Limits.Pullback
open import Cubical.Data.Bool
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where

  open Category C
  -- Definition inspired by the corresponding development
  -- at (https://agda.github.io/agda-categories/Categories.Object.InternalRelation.html)
  record Relation (x y : ob) : Type (ℓ-max ℓ ℓ') where
    constructor internalRel
    field
      dom : ob
      p₁ : Hom[ dom , x ]
      p₂ : Hom[ dom , y ]
      isRelation : isJointMono C {a = dom} Bool (λ { false → x ; true → y }) λ { false → p₁ ; true → p₂ }
      
  module _ {a : ob} (r : Relation a a) where
    open Relation r

    isReflexive : Type _
    isReflexive = Σ[ δ ∈ Hom[ a , dom ] ] (δ ⋆ p₁ ≡ id) × (δ ⋆ p₂ ≡ id)

    isSymmetric : Type _
    isSymmetric = Σ[ σ ∈ Hom[ dom , dom ] ] (σ ⋆ p₁ ≡ p₂) × (σ ⋆ p₂ ≡ p₁)

    isTransitive : Type _
    isTransitive = Σ[ P ∈ Pullback C (cospan dom a dom p₁ p₂) ]
                   Σ[ τ ∈ Hom[ P .pbOb , dom ] ] (τ ⋆ p₁ ≡ P .pbPr₁ ⋆ p₁) × (τ ⋆ p₂ ≡ P .pbPr₂ ⋆ p₂) where
      open Pullback
    
    isEquivalenceRelation : Type (ℓ-max ℓ ℓ')
    isEquivalenceRelation = isReflexive × isSymmetric × isTransitive
