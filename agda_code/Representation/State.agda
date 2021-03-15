
-- Store and Heap module, abstracting away implementation details
------------------------------------------------------------------


open import Representation.Data using (D-Representation)

module Representation.State (dRep : D-Representation ) where

  open D-Representation dRep

  open import Data.Maybe using (Maybe ; just ; nothing)
  open import Relation.Nullary using ( ¬_ )
  open import Relation.Binary.PropositionalEquality using (_≡_)
  open import Data.Empty using (⊥)


  record S-Representation  : Set₁ where
    field
      S              : Set
      --H            : Set
      ●              : S  -- Initial State 
      updateState    : Id → Val → S → S
      getVarVal      : Id → S → Maybe Val
      dropValue      : S → Id → S
      hasVarVal      : Id → Val → S → Set
      updateGet      : ∀ i v s  → getVarVal i (updateState i v s) ≡ just v
      irrelUpdate    : ∀ i x v y → ¬ i ≡ x → (s : S) →
                       getVarVal x (updateState i v s) ≡ y → getVarVal x s ≡ y
      nothingRec     : ∀ x i v s → getVarVal x (updateState i v s) ≡ nothing
                       → getVarVal x s ≡ nothing
      hasValueSame   : (x : Id) → (v v' : Val) → (s : S)
                       → (hasVarVal x v (updateState x v' s)) → v ≡ v'
      hasValueDiff   : (x y : Id) → (xval yval : Val)
                       → (s : S) → ¬ (x ≡ y)
                       → (hasVarVal x xval (updateState y yval s))
                       → (hasVarVal x xval s)
      updateState¬●  : (i : Id) → (f : Val) → (s : S )
                       → ( updateState i f s ≡ ● ) → ⊥


  import State-List-Rep dRep as List-Rep'
  -- S = List localVar
  ListRep : S-Representation
  ListRep = record { List-Rep' }




