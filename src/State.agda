
-- Store and Heap module, abstracting away implementation details
------------------------------------------------------------------


open import Data using (Data-Implementation)

module State ( 𝔡 : Data-Implementation ) where

  open Data-Implementation 𝔡

  open import Data.Maybe using (Maybe ; just ; nothing)
  open import Relation.Nullary using ( ¬_ )
  open import Relation.Binary.PropositionalEquality using (_≡_)
  open import Data.Empty using (⊥)

                         
  record State-Implementation  : Set₁ where
    field
      S              : Set
      --H            : Set
      ●              : S  -- Initial State 
      updateState    : Id → Val → S → S
      getVarVal      : Id → S → Maybe Val
      dropValue      : S → Id → S
      hasVarVal      : Id → Val → S → Set
      updateGet      : ∀ i v s  → getVarVal i (updateState i v s) ≡ just v
      ignoreTop      : ∀ i x v  → ¬ i ≡ x → (s : S) →
                       getVarVal x (updateState i v s) ≡ getVarVal x s
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

    
    getVarValM : Id → Maybe S → Maybe Val
    getVarValM i nothing = nothing
    getVarValM i (just s) = getVarVal i s


  import Representations.State-List-Rep 𝔡 as List-Rep
  -- S = List localVar
  ListRep : State-Implementation
  ListRep = record { List-Rep }




