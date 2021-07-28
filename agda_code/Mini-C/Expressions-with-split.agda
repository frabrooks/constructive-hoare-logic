 

-- Lib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_ )
open import Data.Sum
open import Data.Empty
open import Data.Bool
open import Relation.Binary
open import Relation.Nullary using ( yes ; no )
open import Relation.Nullary.Decidable using ( map′)

open import Representation.Data using (D-Representation)
open import Representation.State using (S-Representation)

module Mini-C.Expressions (dRep : D-Representation )
  (sRep : S-Representation dRep ) where

  open D-Representation dRep
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
  data BinOp:𝔹 : Set where
    &&   : BinOp:𝔹
    ||   : BinOp:𝔹
    ==   : BinOp:𝔹
    ≤    : BinOp:𝔹
    <    : BinOp:𝔹
    ≥    : BinOp:𝔹
    >    : BinOp:𝔹

  -- :𝕍 -> output is a Value.
  -- That is, a (possibly bounded) integer
  -- i.e. |x ∙ y| ⊆ { z |minInt < z ∧ z < maxInt}
  data BinOp:𝕍 : Set where
    +    : BinOp:𝕍
    -    : BinOp:𝕍
    *    : BinOp:𝕍
    /    : BinOp:𝕍
    %    : BinOp:𝕍
    
  data BinOp : Set where
    _:𝕍  : BinOp:𝕍 → BinOp
    _:𝔹  : BinOp:𝔹 → BinOp

  -- Unary Operators ------------------------
  
  data UnOp:𝕍 : Set where
    ++   : UnOp:𝕍
    ─-   : UnOp:𝕍

  data UnOp:𝔹 : Set where
    ¬ᵇ   : UnOp:𝔹

  data UnaryOp : Set where
    _:𝔹  : UnOp:𝔹 → UnaryOp
    _:𝕍  : UnOp:𝕍 → UnaryOp


  -------------------------------------------------
  -- Definition of Expressions

  data Terminal : Set where
    Const  : Val → Terminal
    Var    : Id  → Terminal
    𝒕      : Terminal
    𝒇      : Terminal

  data Exp : Set where
    op₂    : Exp → BinOp → Exp → Exp
    op₁    : UnaryOp → Exp → Exp 
    term   : Terminal → Exp


  -------------------------------------------------
  -- Utility Functions


  -- Const and var below are to simplify hard coding expressions within agda
  -- e.g.    (op₂ (𝑣𝑎𝑟 𝔁) ( == :𝔹 ) (𝑐𝑜𝑛𝑠𝑡 ➋)) : Exp
  𝑐𝑜𝑛𝑠𝑡 : Val → Exp
  𝑐𝑜𝑛𝑠𝑡 n = term (Const n)

  𝑣𝑎𝑟 : Id → Exp
  𝑣𝑎𝑟 i = term (Var i)

  ∀ₛ : Exp
  ∀ₛ = term 𝒕

  ∅ₛ : Exp
  ∅ₛ = term 𝒇

  getOp₁ : UnaryOp → Maybe Val → Maybe Val
  getOp₁ (¬ᵇ :𝔹) = ¬𝓿
  getOp₁ (++ :𝕍) = ++𝓿
  getOp₁ (─- :𝕍) = ─-𝓿

  getOp₂ : BinOp → Maybe Val → Maybe Val → Maybe Val
  getOp₂ (+  :𝕍)  = _+𝓿_
  getOp₂ (-  :𝕍)  = _-𝓿_
  getOp₂ (*  :𝕍)  = _*𝓿_
  getOp₂ (/  :𝕍)  = _/𝓿_
  getOp₂ (%  :𝕍)  = _%𝓿_
  getOp₂ (≤  :𝔹)  = _≤𝓿_
  getOp₂ (<  :𝔹)  = _<𝓿_
  getOp₂ (≥  :𝔹)  = _≥𝓿_
  getOp₂ (>  :𝔹)  = _>𝓿_
  getOp₂ (== :𝔹)  = _==𝓿_
  getOp₂ (&& :𝔹)  = _&&𝓿_
  getOp₂ (|| :𝔹)  = _||𝓿_

  _isAry₁ : ∀ ∙ → (OP₁ (getOp₁ ∙))
  (¬ᵇ :𝔹) isAry₁ = ¬𝓿₁
  (++ :𝕍) isAry₁ = ++𝓿₁
  (─- :𝕍) isAry₁ = ─-𝓿₁

  _isAry₂ : ∀ ∙ → (OP₂ (getOp₂ ∙))
  (+  :𝕍) isAry₂ = +𝓿₂
  (-  :𝕍) isAry₂ = -𝓿₂
  (*  :𝕍) isAry₂ = *𝓿₂
  (/  :𝕍) isAry₂ = /𝓿₂
  (%  :𝕍) isAry₂ = %𝓿₂
  (&& :𝔹) isAry₂ = &&𝓿₂
  (|| :𝔹) isAry₂ = ||𝓿₂
  (== :𝔹) isAry₂ = ==𝓿₂
  (≤  :𝔹) isAry₂ = ≤𝓿₂
  (<  :𝔹) isAry₂ = <𝓿₂
  (≥  :𝔹) isAry₂ = ≥𝓿₂
  (>  :𝔹) isAry₂ = >𝓿₂

  _:𝕍₁ : ∀ ∙ → OP₁:𝕍 ((∙ :𝕍) isAry₁)
  ++ :𝕍₁ = ++𝓿:𝕍
  ─- :𝕍₁ = ─-𝓿:𝕍

  _:𝕍₂ : ∀ ∙ → OP₂:𝕍 ((∙ :𝕍) isAry₂)
  + :𝕍₂   = +𝓿:𝕍
  - :𝕍₂   = -𝓿:𝕍
  * :𝕍₂   = *𝓿:𝕍
  / :𝕍₂   = /𝓿:𝕍
  % :𝕍₂   = %𝓿:𝕍

  _:𝔹₁ : ∀ ∙ → OP₁:𝔹 ((∙ :𝔹) isAry₁)
  ¬ᵇ :𝔹₁ = ¬𝓿:𝔹

  _:𝔹₂ : ∀ ∙ → OP₂:𝔹 ((∙ :𝔹) isAry₂)
  && :𝔹₂  = &&𝓿:𝔹
  || :𝔹₂  = ||𝓿:𝔹
  == :𝔹₂  = ==𝓿:𝔹
  ≤  :𝔹₂  = ≤𝓿:𝔹
  <  :𝔹₂  = <𝓿:𝔹
  ≥  :𝔹₂  = ≥𝓿:𝔹
  >  :𝔹₂  = >𝓿:𝔹

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



