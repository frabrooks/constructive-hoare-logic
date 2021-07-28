
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym )
open import Relation.Nullary using (  yes ; no ; ¬_ ) 
open import Data.Empty 

module Misc where

  sym¬ : ∀ {ℓ} {A : Set ℓ} {a : A} {b : A} → ¬ a ≡ b → ¬ b ≡ a
  sym¬ {A} {a} {b} p = λ x → ⊥-elim (p (sym x))

  
