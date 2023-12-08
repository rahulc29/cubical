{-# OPTIONS #-}

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Morphism
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Categories.Limits.Coequalizers
open import Cubical.Categories.Regular.KernelPair
open import Cubical.Categories.Limits.Pullback

module Cubical.Categories.Regular.Base where

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where
  open Category C
  private
    variable
      x y z w : ob

  -- To define regular categories, we must first define
  -- the notion of a regular epic
  isRegularEpic : Hom[ y , z ] → Type (ℓ-max ℓ ℓ')
  isRegularEpic {y} {z} p =
    ∃[ x ∈ ob ]
    ∃[ f ∈ Hom[ x , y ] ]
    ∃[ g ∈ Hom[ x , y ] ]
    IsCoequalizer {C = C} f g p

  isPropIsRegularEpic : ∀ {y} {z} p → isProp (isRegularEpic {y} {z} p)
  isPropIsRegularEpic p = isPropPropTrunc

  open Pullback
  regularEpicPreservedUnderPullback : Type (ℓ-max ℓ ℓ')
  regularEpicPreservedUnderPullback = ∀ {a b c : ob} (f : Hom[ b , a ]) (g : Hom[ c , a ])
                                     → isRegularEpic f
                                     → (p : Pullback C (cospan c a b g f))
                                     ------------------------------------------------------
                                     → isRegularEpic (p .pbPr₁)

  -- The second component is to formulate the constraint
  -- that every kernel pair has a coequalizer
  kernelPairHasCoequalizer : Type (ℓ-max ℓ ℓ')
  kernelPairHasCoequalizer = ∀ {x y : ob} → (f : Hom[ x , y ]) → ∥ KernelPair C f ∥₁

  record IsRegular : Type (ℓ-max ℓ ℓ') where
    field
      arrowHasKernelPairs : hasKernelPairs C
      kPairHasCoequalizer : kernelPairHasCoequalizer
      regularEpiPreservedPullback : regularEpicPreservedUnderPullback
