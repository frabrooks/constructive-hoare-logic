
-- Lib imports
import Data.Integer using ( ℤ )
import Data.Nat using (ℕ)


module Top-Level where

   -- Data Representation -------------------
  open import Representation.Data
  -- Identifier = ℕ
  -- Values = ℤ
  open D-Representation SimpleRep

  -- State Representation ------------------
  open import Representation.State SimpleRep
  -- S = List localVar
  open S-Representation ListRep

  -- Expressions ---------------------------
  open import Mini-C.Expressions SimpleRep ListRep

  -- Assertions ---------------------------- 
  open import Assertions.Props SimpleRep ListRep


  ----------------------------------------------------------------------------------------------------
  -- Examples:
  
  -- Assuming identifier 𝔁 is encoded with 0, identifier 𝔃 is 1, and identifier 𝔂 is encoded with 2:
  -- exp1 = [  (( 𝔁 + 1 ) < 𝔃  ) && ( 𝔂 == 1 )  ]  = a 𝔹Exp that outputs either 𝑻 or 𝑭 
  --private exp1 : Exp 
  --exp1 = 𝔹: ( ( ( (Var zero ) +ᶻ  (Const (pos 1) ) ) < (Var (suc zero) ) )  && ( (Var (suc (suc 2)) ) == (Const (pos 1) ) ) )
  --  where open Data.Integer.ℤ
  --        open Data.Nat.ℕ
  -- Old way: Op &&𝓬 [ Op ≤𝓬 [ (Op +𝓬 [ (Var 4) ؛ (Constant (pos 1)) ] ) ؛ (Var 3 ) ] ؛ Op ==𝓬 [ (Var 6) ؛  (Constant (pos 1)) ] ]
  
