 

-- Lib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_ )
open import Data.Sum
open import Data.Empty
open import Data.Bool
open import Relation.Binary
open import Relation.Nullary using ( yes ; no )
open import Relation.Nullary.Decidable using ( map′)

open import Representation.Data using (Data-Implementation)
open import Representation.State using (S-Representation)

module Mini-C.Expressions ( 𝔡 : Data-Implementation )
  (sRep : S-Representation 𝔡 ) where

  open Data-Implementation 𝔡
  open S-Representation sRep

  open import List-Patterns
  open import Data.Maybe using (Maybe ; nothing ; just )
  open import Data.List as List using (List; _∷_; []  )

  -- An expression can either be an ℤ expression
  -- ,such as one that may be used in an assignment,
  --
  -- i.e. x := (y + 4)
  --
  -- or a 𝔹 expression that may be used in either:
  -- a conditional statement as part of control flow
  --
  -- i.e. if (y < 4) then {...} else {...}
  --
  -- or within the propositional reasoning about
  -- program state within the Hoare/Separation logic
  --
  -- i.e. [ x < 4 ]
  --      y := 4
  --   ∴  [ x < y ]
  -------------------------------------------------


  -------------------------------------------------
  -- Operators

  -- Binary Operators ------------------------

  -- :𝔹 -> binary output (i.e. |x ∙ y| ⊆ Bool )
  data BinOp : Set where
    &&   : BinOp
    ||   : BinOp
    ==   : BinOp
    ≤    : BinOp
    <    : BinOp
    ≥    : BinOp
    >    : BinOp
    +    : BinOp
    -    : BinOp
    *    : BinOp
    /    : BinOp
    %    : BinOp

  -- Unary Operators ------------------------
  
  data UnOp : Set where
    ++   : UnOp
    ─-   : UnOp
    ¬ᵇ   : UnOp
    
  -------------------------------------------------
  -- Definition of Expressions

  data Terminal : Set where
    Const  : Val → Terminal
    Var    : Id  → Terminal
    𝒕      : Terminal
    𝒇      : Terminal

  data Exp : Set where
    op₂    : Exp → BinOp → Exp → Exp
    op₁    : UnOp → Exp → Exp 
    term   : Terminal → Exp


  -------------------------------------------------
  -- Utility Functions


  -- Const and var below are to simplify hard coding expressions within agda
  -- e.g.    (op₂ (𝑣𝑎𝑟 𝔁) ( == :𝔹 ) (𝑐𝑜𝑛𝑠𝑡 ➋)) : Exp
  pattern 𝑐𝑜𝑛𝑠𝑡 n = term (Const n)
  pattern 𝑣𝑎𝑟 i = term (Var i)


  ∀ₛ : Exp
  ∀ₛ = term 𝒕

  ∅ₛ : Exp
  ∅ₛ = term 𝒇

  getOp₁ : UnOp → Maybe Val → Maybe Val
  getOp₁ ¬ᵇ  = ¬𝓿
  getOp₁ ++  = ++𝓿
  getOp₁ ─-  = ─-𝓿

  getOp₂ : BinOp → Maybe Val → Maybe Val → Maybe Val
  getOp₂ +   = _+𝓿_
  getOp₂ -   = _-𝓿_
  getOp₂ *   = _*𝓿_
  getOp₂ /   = _/𝓿_
  getOp₂ %   = _%𝓿_
  getOp₂ ≤   = _≤𝓿_
  getOp₂ <   = _<𝓿_
  getOp₂ ≥   = _≥𝓿_
  getOp₂ >   = _>𝓿_
  getOp₂ ==  = _==𝓿_
  getOp₂ &&  = _&&𝓿_
  getOp₂ ||  = _||𝓿_

  _isAry₁ : ∀ ∙ → (OP₁ (getOp₁ ∙))
  ¬ᵇ isAry₁ = ¬𝓿₁
  ++ isAry₁ = ++𝓿₁
  ─- isAry₁ = ─-𝓿₁

  _isAry₂ : ∀ ∙ → (OP₂ (getOp₂ ∙))
  +  isAry₂ = +𝓿₂
  -  isAry₂ = -𝓿₂
  *  isAry₂ = *𝓿₂
  /  isAry₂ = /𝓿₂
  %  isAry₂ = %𝓿₂
  && isAry₂ = &&𝓿₂
  || isAry₂ = ||𝓿₂
  == isAry₂ = ==𝓿₂
  ≤  isAry₂ = ≤𝓿₂
  <  isAry₂ = <𝓿₂
  ≥  isAry₂ = ≥𝓿₂
  >  isAry₂ = >𝓿₂

  -------------------------------------------------
  -- Evaluation of Expressions (Decidable)
  
  evalExp : Exp → S → Maybe Val
  evalTerm : Terminal → S → Maybe Val

  evalExp (term t) s = evalTerm t s
  evalExp (op₁ ∙ x) s = (getOp₁ ∙) (evalExp x s)
  evalExp (op₂ l α r) s = let _∙_ = getOp₂ α in
                   (evalExp l s) ∙ (evalExp r s)
                            
  evalTerm (Const x) _ = just x
  evalTerm (Var x) s = getVarVal x s
  evalTerm  𝒕 _ = 𝑻
  evalTerm  𝒇 _ = 𝑭



