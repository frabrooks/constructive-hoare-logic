
-- Lib Imports
open import Relation.Binary.Definitions using ( Decidable )
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym )
open import Relation.Nullary.Decidable using ( ⌊_⌋ )
open import Relation.Nullary using ( yes ; no ; ¬_ )
open import Data.Bool using ( true ; false)
open import Data.List as List using (List; _∷_; [] )
open import Data.Maybe using (Maybe ; nothing ; just )
open import Data.Product using ( _×_ ; _,_ )
open import Data.Empty using (⊥ ; ⊥-elim)


-- Local Imports
open import Data-Interface using (Data-Implementation)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Representations.State-As-List ( 𝔡 : Data-Implementation) where

  
  -- Local Dependent Imports
  open Data-Implementation 𝔡
  open import State-Interface 𝔡

  -- ════════════════════════════════════════════════════════════════════════════
  -- Representations.State-As-List:
  --
  -- Implementation of the state interface with the state represented as a list
  -- of pairs of identifiers and corresponding values.



  pattern [_] z = z ∷ []
  pattern [_؛_] y z = y ∷ z ∷ []
  pattern [_؛_؛_] x y z = x ∷ y ∷ z ∷ []
  pattern [_؛_؛_؛_] w x y z = w ∷ x ∷ y ∷ z ∷ []

  -- ════════════════════════════════════════════════════════════════════════════
  module List-Rep where

    S = List (Id × Val)

    ● : S
    ● = []


    ---------------------------------------------------------------------------
    -- Operations upon the state space

    updateState : Id → Val → S → S
    updateState id z  []  = [ ( id , z ) ]
    updateState id e ((fst , snd) ∷ zs) with id ?id= fst
    ... | yes _ = (id , e) ∷ zs
    ... | no _ = (fst , snd ) ∷ updateState id e zs


    getVarVal : Id → S → Maybe Val
    getVarVal _ [] = nothing
    getVarVal id ((fst , snd) ∷ zs) with ⌊ id ?id= fst ⌋
    ... | true =  just snd 
    ... | false = getVarVal id zs


    dropValue : Id → S → S
    dropValue _  []  = []
    dropValue id ((fst , snd) ∷ s) with ⌊ id ?id= fst ⌋
    ... | true  = s
    ... | false = (fst , snd) ∷ (dropValue id s)

    ---------------------------------------------------------------------------
    -- Predicates/Lemmas upon the state space

    --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    private removeFromTop : ∀ i x w s  → (¬ i ≡ x )
                          → getVarVal i ((x , w ) ∷  s ) ≡ getVarVal i s
    --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -                   
    removeFromTop i x w s n with i ?id= x
    ... | yes p  = ⊥-elim (n p)
    removeFromTop i x w []      n | no _ = refl
    removeFromTop i x w (_ ∷ s) n | no _ = refl


    --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    private getFromTop :  ∀ i x w s  → ( i ≡ x )
                       → getVarVal i ((x , w ) ∷  s ) ≡ just w
    --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -               
    getFromTop i x w s p with i ?id= x
    ... | yes _ = refl
    ... | no ¬p = ⊥-elim (¬p p)


    --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    updateGet : ∀ i v s → getVarVal i (updateState i v s) ≡ just v
    --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    updateGet i v [] with i ?id= i
    ... | yes p = refl
    ... | no ¬p = ⊥-elim (¬p refl)
    updateGet i v ( (x , w )  ∷ s) with i ?id= x
    updateGet i v ( (x , w )  ∷ s) | yes p with i ?id= i
    updateGet i v ( (x , w )  ∷ s) | yes p | yes q = refl
    updateGet i v ( (x , w )  ∷ s) | yes p | no ¬q = ⊥-elim (¬q refl)
    updateGet i v ( (x , w )  ∷ s) | no ¬p with i ?id= x
    updateGet i v ( (x , w )  ∷ s) | no ¬p | yes q = ⊥-elim (¬p q)
    updateGet i v ( (x , w )  ∷ s) | no ¬p | no ¬q = updateGet i v s

    --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    ignoreTop : ∀ i v x  → ¬ i ≡ x → (s : S)
              → getVarVal x (updateState i v s) ≡ getVarVal x s
    --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    ignoreTop i v x ≢ [] with x ?id= i
    ... | yes p = ⊥-elim (≢ (sym p))
    ... | no _  = refl
    ignoreTop i v x ≢ ( (i' , v')  ∷ s) = go
        where
        go : getVarVal x (updateState i v ((i' , v') ∷ s))
           ≡ getVarVal x ((i' , v')  ∷ s)
        go with  i ?id= i' | x ?id= i'
        go | yes p | yes q rewrite p = ⊥-elim (≢ (sym q))
        go | yes p | no ¬q with x ?id= i
        go | yes p | no ¬q | yes w = ⊥-elim (≢ (sym w))
        go | yes p | no ¬q | no ¬w = refl
        go | no ¬p | yes q with x ?id= i'
        go | no ¬p | yes q | yes r = refl
        go | no ¬p | yes q | no ¬r = ⊥-elim (¬r q)        
        go | no ¬p | no ¬q with x ?id= i'
        go | no ¬p | no ¬q | yes r = ⊥-elim (¬q r)
        go | no ¬p | no ¬q | no ¬r = ignoreTop i v x ≢ s



    --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    irrelUpdate : ∀ i x v y → ¬ i ≡ x → (s : S)
                →  getVarVal x (updateState i v s) ≡ y → getVarVal x s ≡ y
    --- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    irrelUpdate i x v y ≢ [] eq with x ?id= i
    ... | yes p = ⊥-elim (≢ (sym p))
    ... | no ¬p = eq
    irrelUpdate i x v y ≢ ((i' , v') ∷ s) eq = go
        where
        go : getVarVal x ((i' , v') ∷ s) ≡ y
        go with x ?id= i' | i ?id= i'
        go | yes p | yes q rewrite q = ⊥-elim (≢ (sym p))
        go | yes p | no ¬q with x ?id= i'
        go | yes p | no ¬q | yes w = eq
        go | yes p | no ¬q | no ¬w = ⊥-elim (¬w p)
        go | no ¬p | yes q with x ?id= i'
        go | no ¬p | yes q | yes w = ⊥-elim (¬p w)
        go | no ¬p | yes q | no ¬w with x ?id= i
        go | no ¬p | yes q | no ¬w | yes r = ⊥-elim (≢ (sym r))
        go | no ¬p | yes q | no ¬w | no ¬r = eq        
        go | no ¬p | no ¬q with x ?id= i'
        go | no ¬p | no ¬q | yes w = ⊥-elim (¬p w)
        go | no ¬p | no ¬q | no ¬w = irrelUpdate i x v y ≢ s eq



    updateState¬● : ∀ i f s → updateState i f s ≡ ● → ⊥
    updateState¬● i f ((fst , snd) ∷ s) p with (i ?id= fst) | p
    ...                                   | yes _  | ()
    ...                                   | no  _  | ()

  -- ════════════════════════════════════════════════════════════════════════════

  -- S = List of pairs of Identifiers and Values
  State-List-Implementation : State-Implementation
  State-List-Implementation = record { List-Rep }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━


