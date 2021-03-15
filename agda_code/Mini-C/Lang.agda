
-- Lib imports
open import Relation.Binary.PropositionalEquality using ( _≡_ )
open import Data.Maybe using ( Maybe ; just ; nothing )
open import Data.Bool using ( true )
import Data.Integer using ( ℤ )
import Data.Nat using (ℕ)

open import Representation.Data using (D-Representation)
open import Representation.State using (S-Representation)

module Mini-C.Lang (dRep : D-Representation )
  (sRep : S-Representation dRep ) where

  open D-Representation dRep
  open S-Representation sRep

  open import List-Patterns
  
  -- Expressions ---------------------------
  open import Mini-C.Expressions dRep sRep


  -- Assignment (i.e. AssiProgram ) 
  
  data _:=_ : Id → Exp → Set where
    _:=''_ : ∀ (id : Id) → (exp : Exp) →  id := exp


  data _:=_|evalExp=_USING_GIVES_ : Id → Exp → Val → S → S →  Set where
    _:='_w/_andPExp : ∀ {v : Val} (id : Id) → (exp : Exp) → (s : S )
                        → (evalExp exp s) ≡ just v
                        → id := exp |evalExp= v USING s GIVES (updateState id v s)



  evalAssiVal : ∀ (id : Id ) ( v : Maybe Val ) → S → Maybe S
  -- Computation fail (e.g. S = nothing after ÷ by 0 error)
  evalAssiVal id nothing _ = nothing
  -- Computation success
  evalAssiVal id (just v) s = just (updateState id v s )

  
  evalAssi : ∀ {i e} (p : i := e) → S → Maybe S
  evalAssi (id :='' exp) s  = evalAssiVal id (evalExp exp s) s
