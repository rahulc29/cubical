-- Cartesian closed categories
-- in the style of 1lab
{-# OPTIONS --safe #-}
module Cubical.Categories.CartesianClosed.Base where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.Terminal

module _ {ℓ ℓ'} (C : Category ℓ ℓ') (bp : BinProducts C) where
open Category C
private variable
  A B : ob

private
  _⊗_ : (x y : ob) → BinProduct x y
  x ⊗ y = BinProduct x y
  
record isExponential (B̂A : ob) (eval : Hom[ B̂A ⊗ A , B ])
  field
    univProp : ∀ (C : ob) → (f : Hom[ C ⊗ A , B ]) → ∃![ g ∈ Hom[ C , B̂A ] ] 
