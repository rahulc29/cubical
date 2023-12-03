{-# OPTIONS  #-}

module Cubical.Categories.Regular.KernelPair where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Pullback
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

  KernelPairs : Type (ℓ-max ℓ ℓ')
  KernelPairs = ∀ {x y : ob} (f : Hom[ x , y ]) → KernelPair f

  hasKernelPairs : Type (ℓ-max ℓ ℓ')
  hasKernelPairs = ∥ KernelPairs ∥₁
