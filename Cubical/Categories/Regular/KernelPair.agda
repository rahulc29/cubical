{-# OPTIONS  #-}

module Cubical.Categories.Regular.KernelPair where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Regular.InternalRelation
open import Cubical.HITs.PropositionalTruncation.Base

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where

  open Category C

  module _ {x y : ob}
           (f : Hom[ x , y ]) where

           kernelPairCospan : Cospan C
           kernelPairCospan = cospan x y x f f

           KernelPair : Type (ℓ-max ℓ ℓ')
           KernelPair = Pullback C kernelPairCospan

           isKernelPair : {z : ob} (p₁ : Hom[ z , x ]) (p₂ : Hom[ z , x ]) → Type (ℓ-max ℓ ℓ')
           isKernelPair p₁ p₂ = Σ[ H ∈ (p₁ ⋆ f ≡ p₂ ⋆ f) ] isPullback C kernelPairCospan p₁ p₂ H

  KernelPairs : Type (ℓ-max ℓ ℓ')
  KernelPairs = ∀ {x y : ob} (f : Hom[ x , y ]) → KernelPair f

  hasKernelPairs : Type (ℓ-max ℓ ℓ')
  hasKernelPairs = ∥ KernelPairs ∥₁
