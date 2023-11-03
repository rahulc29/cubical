-- Binary products
{-# OPTIONS --allow-unsolved-metas #-}

module Cubical.Categories.Limits.BinProduct where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Data.Sigma.Base
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation.Base

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where
  open Category C

  module _ {x y x×y : ob}
           (π₁ : Hom[ x×y , x ])
           (π₂ : Hom[ x×y , y ]) where

    isBinProduct : Type (ℓ-max ℓ ℓ')
    isBinProduct = ∀ {z : ob} (f₁ : Hom[ z , x ]) (f₂ : Hom[ z , y ]) →
        ∃![ f ∈ Hom[ z , x×y ] ] (f ⋆ π₁ ≡ f₁) × (f ⋆ π₂ ≡ f₂)

    isPropIsBinProduct : isProp (isBinProduct)
    isPropIsBinProduct = isPropImplicitΠ (λ _ → isPropΠ2 (λ _ _ → isPropIsContr))


  record BinProduct (x y : ob) : Type (ℓ-max ℓ ℓ') where
    field
      binProdOb : ob
      binProdPr₁ : Hom[ binProdOb , x ]
      binProdPr₂ : Hom[ binProdOb , y ]
      univProp : isBinProduct binProdPr₁ binProdPr₂


  BinProducts : Type (ℓ-max ℓ ℓ')
  BinProducts = (x y : ob) → BinProduct x y

  hasBinProducts : Type (ℓ-max ℓ ℓ')
  hasBinProducts = ∥ BinProducts ∥₁

  module _ (binProducts : BinProducts) where
    {-
      Given morphisms f : Hom[ a , b ] and g : Hom[ c , d ]
      we can construct a morphism f×g : Hom[ a × c , b × d ].
      This is given by f , g ⟨ a , c ⟩ ⊢ ⟨ f a , g c ⟩
      Here the ⊢ and ⟨⟩ notation have their obvious meanings
    -}
    open BinProduct
    private variable
      a b c d : ob
    infix 20 _⊗₀_
    _⊗₀_ : ob → ob → ob
    x ⊗₀ y = binProducts x y .binProdOb
    
    _⊗₁_ : (f : Hom[ a , b ]) (g : Hom[ c , d ]) → Hom[ a ⊗₀ c , b ⊗₀ d ]
    _⊗₁_ {a} {b} {c} {d} f g = b⊗d .univProp (a⊗c .binProdPr₁ ⋆ f) (a⊗c .binProdPr₂ ⋆ g) .fst .fst where
         b⊗d = binProducts b d
         a⊗c = binProducts a c

    open Functor
    prodFunctor : Functor (C ×C C) C
    prodFunctor .F-ob (x , y) = x ⊗₀ y
    prodFunctor .F-hom {x , y} {x' , y'} (f , g) = f ⊗₁ g
    prodFunctor .F-id {x , y} i =
      (isContr→isProp
        (x×y .univProp
          (x×y .binProdPr₁ ⋆ id)
          (x×y .binProdPr₂ ⋆ id))
        ( id {x} ⊗₁ id {y}
        , x×y .univProp (x×y .binProdPr₁ ⋆ id) (x×y .binProdPr₂ ⋆ id) .fst .snd .fst
        , x×y .univProp (x×y .binProdPr₁ ⋆ id) (x×y .binProdPr₂ ⋆ id) .fst .snd .snd)
        ( id {x ⊗₀ y}
        , (id ⋆ (x×y .binProdPr₁) ≡⟨ ⋆IdL _ ⟩
          x×y .binProdPr₁ ≡⟨ sym (⋆IdR _) ⟩
          x×y .binProdPr₁ ⋆ id ∎)
        , (id ⋆ (x×y .binProdPr₂) ≡⟨ ⋆IdL _ ⟩
          x×y .binProdPr₂ ≡⟨ sym (⋆IdR _) ⟩
          x×y .binProdPr₂ ⋆ id ∎)))
        i .fst where
          x×y = binProducts x y
    prodFunctor .F-seq {a , b} {c , d} {e , f} (α , β) (δ , γ) =
      {!!}
