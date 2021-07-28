
-- Lib imports
open import Relation.Binary.PropositionalEquality using ( _≡_ )
open import Data.Maybe using ( Maybe ; just ; nothing )
open import Data.Bool using ( true )
import Data.Integer using ( ℤ )
import Data.Nat using (ℕ)

open import Representation.Data using (Data-Implementation)
open import Representation.State using (S-Representation)

module Mini-C.Lang (𝔡 : Data-Implementation )
  (sRep : S-Representation 𝔡 ) where

  open Data-Implementation 𝔡
  
  -- Expressions ---------------------------
  open import Mini-C.Expressions 𝔡 sRep

  -- Commands/Programs
  data 𝐶 : Set
  
  -- Assignment Command
  data _:=_ : Id → Exp → Set where
    _꞉=_ : ∀ id exp →  id := exp

  -- Sequence  Command
  data _;_ : 𝐶 → 𝐶 → Set where
    _﹔_ : ∀ c₁ c₂ → c₁ ; c₂

  -- If Then Else Command
  data IF_THEN_ELSE_ :  Exp → 𝐶 → 𝐶 → Set  where
    𝑖𝑓_𝑡ℎ𝑒𝑛_𝑒𝑙𝑠𝑒_ : ∀ b c₁ c₂ → IF b THEN c₁ ELSE c₂

  -- WHILE LOOP Command
  data WHILE_DO_ : Exp → 𝐶 → Set where
    𝑤ℎ𝑖𝑙𝑒_𝑑𝑜_ : ∀ b c →  WHILE b DO c

  data 𝐶 where
    𝑎𝑠𝑠𝑖꞉ : ∀ {id} {exp} → id := exp → 𝐶
    𝑠𝑒𝑞꞉ : ∀ {c₁} {c₂} → c₁ ; c₂ → 𝐶
    𝑐𝑡𝑟𝑙꞉  : ∀ {b} {c₁} {c₂} → IF b THEN c₁ ELSE c₂ → 𝐶
    𝑙𝑜𝑜𝑝꞉ : ∀ {b} {c} → WHILE b DO c → 𝐶
    𝑠𝑘𝑖𝑝  : 𝐶


