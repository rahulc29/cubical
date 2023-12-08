module Cubical.Categories.Regular.Exact where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Regular.InternalRelation
open import Cubical.Categories.Limits.Coequalizers
open import Cubical.Categories.Regular.KernelPair

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where
  open Category C
  module _ {a : ob} (r : Relation C a a) where
    open Relation r
    -- A relation R ⇉ A is *effective* iff
    -- there is a coequalizer of it such that the
    -- coequalizer inclusion is the kernel pair of the
    -- relation projections
    isEffective : Type _
    isEffective = Σ[ c ∈ Coequalizer {C = C} p₁ p₂ ] isKernelPair C (c .quotientInc) p₁ p₂ where
      open Coequalizer renaming (coeq to quotientInc)

  isExact : Type (ℓ-max ℓ ℓ')
  isExact = ∀ {a} (r : Relation C a a) → isEquivalenceRelation C r → isEffective r
