
-- Lib imports
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym )
import Data.Integer using ( ℤ )
open Data.Integer.ℤ
open import Data.Nat using ( ℕ ; suc ; zero ; _*_ )
open import Data.Maybe using ( Maybe ; nothing ; just )
open import Data.Product using (Σ ; Σ-syntax ; _×_  ; _,_  ; proj₁ ; proj₂)
open import Relation.Nullary using (  yes ; no ; ¬_ ) 

-- Project imports
open import Misc


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

  -- Language
  open import Mini-C.Lang SimpleRep ListRep 
  
  -- Evaluation
  open import Mini-C.Evaluation SimpleRep ListRep


  ----------------------------------------------------------------------------------------------------
  -- Examples:
  
  -- Assuming identifier 𝔁 is encoded with 0, identifier 𝔃 is 1, and identifier 𝔂 is encoded with 2:
  -- exp1 = [  (( 𝔁 + 1 ) < 𝔃  ) && ( 𝔂 == 1 )  ]  = a 𝔹Exp that outputs either 𝑻 or 𝑭 
  --private exp1 : Exp 
  --exp1 = 𝔹: ( ( ( (Var zero ) +ᶻ  (Const (pos 1) ) ) < (Var (suc zero) ) )  && ( (Var (suc (suc 2)) ) == (Const (pos 1) ) ) )
  --  where open Data.Integer.ℤ
  --        open Data.Nat.ℕ
  -- Old way: Op &&𝓬 [ Op ≤𝓬 [ (Op +𝓬 [ (Var 4) ؛ (Constant (pos 1)) ] ) ؛ (Var 3 ) ] ؛ Op ==𝓬 [ (Var 6) ؛  (Constant (pos 1)) ] ]


  
  -- Assign x and y = 1 , z = 2 program
  1+1=2Prog : C
  1+1=2Prog = (𝑠𝑒𝑞꞉ ( (𝑎𝑠𝑠𝑖꞉ ( 𝔁 ꞉= ( ℤ: (Const ➊ ) ) )) ﹔ (𝑠𝑒𝑞꞉ ( (𝑎𝑠𝑠𝑖꞉ ( 𝔂 ꞉= ( ℤ: (Const ➊ ) ) ) ) ﹔ (𝑎𝑠𝑠𝑖꞉ ( 𝔃 ꞉=  ( ℤ: (binary-ℤ-op:ℤ (Var 𝔁) (+ᶻ) (Var 𝔂)) ) ))  ))))
  
  1+1=2ProgWorks : getVarValM 𝔃 ( proj₂ (ssEvalwithFuel 100 ( 1+1=2Prog , just ● ))) ≡ ( just ➋ )
  1+1=2ProgWorks = refl

{-
    factorial : Program
  factorial = let l1 = Assignment 𝑌 (Constant (ℤ.pos 1)) in
              let while = While (Op Greater [ (Var 𝑋)  , (Constant (ℤ.pos 0)) ] ) in
                        let l3 = Assignment 𝑌 (Op Mul [ (Var 𝑌) , (Var 𝑋) ] ) in
                        let l4 = Assignment 𝑋 (Op Sub [ (Var 𝑋) , (Constant (ℤ.pos 1)) ] ) in
              let block = Block [ l3 , l4 ] in
              Block [ l1 , while block ]
-}

  
  _! : ℕ → ℕ
  zero ! = (suc zero)
  (suc n) !  = (suc n) * ( n ! )  
  

  facSt : ℕ → S
  facSt n = updateState 𝔁 (pos n) ● 

  factorialProg : C
  factorialProg = let 𝔂*𝔁 = ℤ: (binary-ℤ-op:ℤ (Var 𝔂) *ᶻ (Var 𝔁)) in
              let 𝔁-1 = ℤ: (binary-ℤ-op:ℤ (Var 𝔁) -ᶻ (Const ➊)) in
              let 𝔁>0 = binary-ℤ-op:𝔹 (Var 𝔁) > (Const ⓪) in
              (𝑠𝑒𝑞꞉ ( ( 𝑎𝑠𝑠𝑖꞉ ( 𝔂 ꞉= ( ℤ: (Const ➊ )))) ﹔ (𝑙𝑜𝑜𝑝꞉ ( 𝑤ℎ𝑖𝑙𝑒 𝔁>0 𝑑𝑜 (𝑠𝑒𝑞꞉ ( ( 𝑎𝑠𝑠𝑖꞉ (𝔂 ꞉= 𝔂*𝔁 ) ) ﹔ ( 𝑎𝑠𝑠𝑖꞉ ( 𝔁 ꞉= 𝔁-1 ) ))))))) 


  factorialProgCheck : getVarValM 𝔂 ( proj₂ (ssEvalwithFuel 100 ( factorialProg , just (facSt 4) ))) ≡ ( just (pos 24) )
  factorialProgCheck = refl

  factorialProgWorks : ∀ n
                     → Σ[ m ∈ ℕ ] getVarValM 𝔂 ( proj₂ (ssEvalwithFuel (m * n) ( factorialProg , just (facSt n) ))) ≡ ( just (pos ( n ! )) )
  factorialProgWorks n =  {!!}

  res : Maybe S
  res with ssEvalwithFuel 100 ( 1+1=2Prog , just ● )
  ... | (_ , nothing  ) = nothing
  ... | (_ , (just s) ) = (just s)


  𝔂≢𝔁 : ¬ 𝔂 ≡ 𝔁
  𝔂≢𝔁 = sym¬ 𝔁≢𝔂 
  
  
  foo : Maybe Val
  foo rewrite ignoreTop 𝔂 𝔁 ➊ (sym¬ 𝔁≢𝔂) (updateState 𝔁 ➊ ●) | updateGet 𝔁 ➊ ● with res
  ... | nothing = nothing
  ... | (just s) = getVarVal 𝔃 s
  


