

-- Lib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_ )
open import Data.Maybe using ( Maybe ; just ; nothing  )
open import Relation.Nullary using ( yes ;  no )


open import Representation.Data using (D-Representation)
open import Representation.State using (S-Representation)

module Assertions.Props (dRep : D-Representation )
  (sRep : S-Representation dRep ) where

  open D-Representation dRep
  open S-Representation sRep
  
  -- Using the same expression language as the
  -- Mini-C language itself at the moment,
  -- This may need to change later
  open import Mini-C.Expressions dRep sRep 


  -- Propositions (P) are expressions in the Mini-C language that compute
  -- to either 𝑻 or a 𝑭 - as defined in the D-Representation
  -- i.e. `(x < 3) || (y > 6)` is a proposition but `(x + 3)` is not
  -- even though both are valid expressions in the Mini-C language
  -- as both `x := (x < 3)` and `x := (x + 4)` are valid assignment ops
  𝑃 = 𝔹Exp

  -- Backwards epsilon notation for 'such that' from Peano
  Assert :  𝑃 → S → Set
  Assert p s = eval𝔹Exp p s ≡ just 𝑻


  -- Alternative syntax
  _←_ : 𝑃 → S → Set
  p ← s = Assert p s 

  --    x :=  T

  -- substitute Value for Identifier in Integer expression
  subℤExp : Val → Id → ℤExp → ℤExp
  subℤExp v i (⇉ᶻ l +ᶻ r) = (⇉ᶻ (subℤExp v i l) +ᶻ (subℤExp v i r))
  subℤExp v i (⇉ᶻ l -ᶻ r) = (⇉ᶻ (subℤExp v i l) -ᶻ (subℤExp v i r))
  subℤExp v i (⇉ᶻ l *ᶻ r) = (⇉ᶻ (subℤExp v i l) *ᶻ (subℤExp v i r)) 
  subℤExp v i (⇉ᶻ l /ᶻ r) = (⇉ᶻ (subℤExp v i l) /ᶻ (subℤExp v i r))  
  subℤExp v i (⇉ᶻ l %ᶻ r) = (⇉ᶻ (subℤExp v i l) %ᶻ (subℤExp v i r))
  subℤExp v i (Const x) = (Const x)
  subℤExp v i (Var x) with i ?id= x
  ... | yes _ = (Const v)
  ... | no  _ = (Var x)

  -- substitute Value for Identifier in Proposition
  sub : Val → Id → 𝑃 → 𝑃
  sub v i (ᶻ⇉ᵇ l ≤ r)  =  (ᶻ⇉ᵇ ( subℤExp v i l ) ≤  ( subℤExp v i r ))
  sub v i (ᶻ⇉ᵇ l < r)  =  (ᶻ⇉ᵇ ( subℤExp v i l ) <  ( subℤExp v i r ))
  sub v i (ᶻ⇉ᵇ l == r) =  (ᶻ⇉ᵇ ( subℤExp v i l ) == ( subℤExp v i r ))
  sub v i (ᶻ⇉ᵇ l ≥ r)  =  (ᶻ⇉ᵇ ( subℤExp v i l ) ≥  ( subℤExp v i r ))
  sub v i (ᶻ⇉ᵇ l > r)  =  (ᶻ⇉ᵇ ( subℤExp v i l ) >  ( subℤExp v i r ))
  sub v i (⇉ᵇ l && r) =  (⇉ᵇ (sub v i l) && (sub v i r))
  sub v i (⇉ᵇ l || r) =  (⇉ᵇ (sub v i l) || (sub v i r))
  sub v i (⇉ᵇ l ⇔ r) =  (⇉ᵇ (sub v i l) ⇔ (sub v i r))
  sub v i (⇾ᵇ ! e) = (⇾ᵇ ! (sub v i e))
  sub v i 𝒕 = 𝒕
  sub v i 𝒇 = 𝒇




