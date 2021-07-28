{-# OPTIONS --allow-unsolved-metas #-}

-- Lib Imports
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; subst ; sym ; cong ; inspect ; [_] )
open import Data.Maybe.Relation.Unary.Any renaming ( just to any-just )
open import Data.Product using (Σ ; Σ-syntax ; _×_  ; _,_  ; proj₁ ; proj₂ )
open import Data.Maybe using ( Maybe ; just ; nothing ; _>>=_ ; Is-just ; to-witness )
import Data.Maybe.Relation.Unary.Any 
open Data.Maybe.Relation.Unary.Any.Any renaming ( just to any-just )
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using ( ⊥ ; ⊥-elim )
open import Data.Bool
open import Function using (_$_ ; _∘_)
open import Function.Equivalence hiding (sym)


-- Project Imports
open import Representation.Data using (Data-Implementation)
open import Representation.State using (S-Representation)

open import Misc

module Hoare-Logic.Semantics ( 𝔡 : Data-Implementation )
  (sRep : S-Representation 𝔡 ) where

  open Data-Implementation 𝔡
  open S-Representation sRep

  open import Mini-C.Expressions 𝔡 sRep
  open import Assertions.Props 𝔡 sRep

  open import Mini-C.Lang 𝔡 sRep

  open import Hoare-Logic.Termination 𝔡 sRep

  -- Hoare's Notation: {P}C{Q}   P → wp C P   ( Partial Correctness )
  ⟪_⟫_⟪_⟫ :  𝐴 → C → 𝐴 → Set
  ⟪ P ⟫ C ⟪ Q ⟫ = ( s : S ) → Σ⊢ s P → (ϕ : ⌊ᵗ C ⸴ s ᵗ⌋) → Σ⊢ (‵ ϕ) Q 

  -- Total Correctness 
  ⟦_⟧_⟦_⟧ :  𝐴 → C → 𝐴 → Set
  ⟦ P ⟧ C ⟦ Q ⟧ = (s : S) → ⌊ᵗ C ⸴ s ᵗ⌋ × ⟪ P ⟫ C ⟪ Q ⟫


--                  ((ϕ : Terminates C s) → Σ⊢ (Result ϕ) Q))

  -- ⟪ 𝐹 ⟫ C ⟪ Q ⟫ = 𝑇  for all C Q, so the definition above needs
  -- to give us:  ∀ C Q → ⟪ 𝐹 ⟫ C ⟪ Q ⟫ → 

  -- Need to exclude trivially true assertions that don't actually
  -- 𝑔𝑢𝑎𝑟𝑎𝑛𝑡𝑒𝑒 correctness (i.e.  ⟪ 𝑇 ⟫ 𝔁 := 2 / 𝔂 ⟪ 𝔁 == 1 ⟫ → ⊥ )


  -- ⟦𝑃𝑟𝑒𝐶𝑜𝑛𝑑⟧ P 𝑓𝑜𝑟 s C Q -- Σ[ s ∈ S ] Terminates C s ×  ⟪ P ⟫ C ⟪ Q ⟫ 










