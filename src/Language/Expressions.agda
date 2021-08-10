 

-- Lib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_ ; refl )
open import Data.Sum
open import Data.Empty
open import Data.Bool hiding (_∧_ ; _∨_ )
open import Relation.Binary
open import Relation.Nullary using ( yes ; no )
open import Relation.Nullary.Decidable using ( map′)

open import Data-Interface using (Data-Implementation)
open import State-Interface using (State-Implementation)

module Language.Expressions ( 𝔡 : Data-Implementation )
  (sRep : State-Implementation 𝔡 ) where

  open Data-Implementation 𝔡
  open State-Implementation sRep

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
    &&ₒ   : BinOp
    ||ₒ   : BinOp
    ==ₒ   : BinOp
    ≤ₒ    : BinOp
    <ₒ    : BinOp
    ≥ₒ    : BinOp
    >ₒ    : BinOp
    +ₒ    : BinOp
    -ₒ    : BinOp
    *ₒ    : BinOp
    /ₒ    : BinOp
    %ₒ    : BinOp

  -- Unary Operators ------------------------
  
  data UnOp : Set where
    ++ₒ   : UnOp
    ─-ₒ   : UnOp
    ¬ₒ    : UnOp
    ──ₒ   : UnOp

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
  -- e.g.    (op₂ (𝑣𝑎𝑟 𝔁) ( == :𝔹 ) (𝑐𝑜𝑛𝑠𝑡 ②)) : Exp
  pattern 𝑐𝑜𝑛𝑠𝑡 n = term (Const n)
  -- pattern 𝑣𝑎𝑟 i = term (Var i)
  pattern 𝑣𝑎𝑙 i = term (Var i)
  infix 40 𝑐𝑜𝑛𝑠𝑡
  infix 40 𝑣𝑎𝑙


  𝑇 : Exp
  𝑇 = term 𝒕

  𝐹 : Exp
  𝐹 = term 𝒇

  _∧_ : Exp → Exp → Exp
  P ∧ Q = op₂ P &&ₒ Q

  _∨_ : Exp → Exp → Exp
  P ∨ Q = op₂ P ||ₒ Q
  
  𝑛𝑜𝑡 : Exp → Exp
  𝑛𝑜𝑡 = op₁ ¬ₒ
  infix 40 𝑛𝑜𝑡

  _≥_ : Exp → Exp → Exp
  _≥_ l r = op₂ l ≥ₒ r
  infix 36 _≥_

  _>_ : Exp → Exp → Exp
  _>_ l r = op₂ l >ₒ r
  infix 36 _>_

  _-_ : Exp → Exp → Exp
  _-_ l r = op₂ l -ₒ r
  infix 36 _-_

  _+_ : Exp → Exp → Exp
  _+_ l r = op₂ l +ₒ r
  infix 36 _+_

  _/_ : Exp → Exp → Exp
  _/_ l r = op₂ l /ₒ r
  infix 37 _/_

  ── : Exp → Exp
  ── = op₁ ──ₒ

  _==_ : Exp → Exp → Exp
  _==_ l r = op₂ l ==ₒ r
  infix 36 _==_

  _=̌=̌_ : Id → Id → Exp
  _=̌=̌_ l r = op₂ (𝑣𝑎𝑙 l) ==ₒ (𝑣𝑎𝑙 r)
  infix 36 _=̌=̌_

  _=̌=_ : Id → Exp → Exp
  _=̌=_ l r = op₂ (𝑣𝑎𝑙 l) ==ₒ r
  infix 36 _=̌=_

  𝑒𝑣𝑒𝑛〈_〉 : Exp → Exp
  𝑒𝑣𝑒𝑛〈 P 〉 = op₂ (op₂ P %ₒ (𝑐𝑜𝑛𝑠𝑡 ②)) ==ₒ (𝑐𝑜𝑛𝑠𝑡 ⓪)

  𝑜𝑑𝑑〈_〉 : Exp → Exp
  𝑜𝑑𝑑〈 P 〉 = op₂ (op₂ P %ₒ (𝑐𝑜𝑛𝑠𝑡 ②)) ==ₒ (𝑐𝑜𝑛𝑠𝑡 ①)

  getOp₁ : UnOp → Maybe Val → Maybe Val
  getOp₁ ¬ₒ  = ¬𝓿
  getOp₁ ++ₒ  = ++𝓿
  getOp₁ ─-ₒ  = ─-𝓿
  getOp₁ ──ₒ  = ──𝓿

  getOp₂ : BinOp → Maybe Val → Maybe Val → Maybe Val
  getOp₂ +ₒ   = _+𝓿_
  getOp₂ -ₒ   = _-𝓿_
  getOp₂ *ₒ   = _*𝓿_
  getOp₂ /ₒ   = _/𝓿_
  getOp₂ %ₒ   = _%𝓿_
  getOp₂ ≤ₒ   = _≤𝓿_
  getOp₂ <ₒ   = _<𝓿_
  getOp₂ ≥ₒ   = _≥𝓿_
  getOp₂ >ₒ   = _>𝓿_
  getOp₂ ==ₒ  = _==𝓿_
  getOp₂ &&ₒ  = _&&𝓿_
  getOp₂ ||ₒ  = _||𝓿_

  _isAry₁ : ∀ ∙ → (OP₁ (getOp₁ ∙))
  ¬ₒ  isAry₁ = ¬𝓿₁
  ++ₒ  isAry₁ = ++𝓿₁
  ─-ₒ  isAry₁ = ─-𝓿₁
  ──ₒ isAry₁ = ──𝓿₁

  _isAry₂ : ∀ ∙ → (OP₂ (getOp₂ ∙))
  +ₒ  isAry₂ = +𝓿₂
  -ₒ  isAry₂ = -𝓿₂
  *ₒ  isAry₂ = *𝓿₂
  /ₒ  isAry₂ = /𝓿₂
  %ₒ  isAry₂ = %𝓿₂
  &&ₒ isAry₂ = &&𝓿₂
  ||ₒ isAry₂ = ||𝓿₂
  ==ₒ isAry₂ = ==𝓿₂
  ≤ₒ  isAry₂ = ≤𝓿₂
  <ₒ  isAry₂ = <𝓿₂
  ≥ₒ  isAry₂ = ≥𝓿₂
  >ₒ  isAry₂ = >𝓿₂

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
  evalTerm  𝒕 _ = just 𝑻
  evalTerm  𝒇 _ = just 𝑭



  sub : Exp → Id → Exp → Exp
  sub e' id (op₂ l ∙ r) = let lhs = sub e' id l in
                             let rhs = sub e' id r in
                             (op₂ lhs ∙ rhs)
  sub e' id (op₁ ∙ e) = op₁ ∙ (sub e' id e)
  sub e' id e@(term (Const x)) = e
  sub e' id e@(term 𝒕) = e
  sub e' id e@(term 𝒇) = e
  -- This is where the substitution happens:
  sub e' id e@(term (Var id')) with id ?id= id'
  ... | yes _ = e'
  ... | no  _ = e

  sub⁻¹ : ∀ 𝒙 𝒚 P → sub (𝑣𝑎𝑙 𝒚) 𝒙 (sub (𝑣𝑎𝑙 𝒙) 𝒚 P) ≡ sub (𝑣𝑎𝑙 𝒚) 𝒙 P
  sub⁻¹ x y (op₂ l o r) rewrite sub⁻¹ x y l | sub⁻¹ x y r = refl
  sub⁻¹ x y (op₁ o P)   rewrite sub⁻¹ x y P = refl
  sub⁻¹ x y (𝑐𝑜𝑛𝑠𝑡 _) = refl
  sub⁻¹ x y (term 𝒕)  = refl
  sub⁻¹ x y (term 𝒇)  = refl
  sub⁻¹ x y (𝑣𝑎𝑙 v)   with y ?id= v
  ---------------------------------------
  sub⁻¹ x y (𝑣𝑎𝑙 v) | no ¬p with x ?id= v
  sub⁻¹ x y (𝑣𝑎𝑙 v) | no ¬p | yes q = refl
  sub⁻¹ x y (𝑣𝑎𝑙 v) | no ¬p | no ¬q = refl
  ---------------------------------------
  sub⁻¹ x y (𝑣𝑎𝑙 v) | yes p with x ?id= v | x ?id= x
  sub⁻¹ x y (𝑣𝑎𝑙 v) | yes _ | yes _ | yes _ = refl
  sub⁻¹ x y (𝑣𝑎𝑙 v) | yes _ | yes _ | no ¬w = ⊥-elim (¬w refl)  
  sub⁻¹ x y (𝑣𝑎𝑙 v) | yes p | no  _ | yes _ rewrite p = refl
  sub⁻¹ x y (𝑣𝑎𝑙 v) | yes _ | no  _ | no ¬w = ⊥-elim (¬w refl)  





