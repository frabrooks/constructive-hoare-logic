 

-- Lib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_ ; refl )
open import Data.Empty using ( ⊥-elim )
open import Relation.Nullary using ( yes ; no )
open import Data.Maybe using (Maybe ; nothing ; just )

-- Local Imports
open import Data-Interface using (Data-Implementation)
open import State-Interface using (State-Implementation)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Language.Expressions ( 𝔡 : Data-Implementation )
  (𝔖 : State-Implementation 𝔡 ) where

  -- Local Dependent Imports
  open Data-Implementation 𝔡
  open State-Implementation 𝔖

  -- ════════════════════════════════════════════════════════════════════════════

  -- Definition of the Expression Language used in both the Mini-Imp programming
  -- language and the assertions manipulated within the Hoare-Logic calculus.

  -- Implicit casting of ℤ ⇄ 𝔹 is assumed of the underlying representation.


  -- ════════════════════════════════════════════════════════════════════════════
  -- Operators

  -- Binary Operators -----------------------------------------------------------

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

  -- Unary Operators ------------------------------------------------------------
  
  data UnOp : Set where
    ++ₒ   : UnOp
    ─-ₒ   : UnOp
    ¬ₒ    : UnOp
    ──ₒ   : UnOp

  -------------------------------------------------------------------------------
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


  -------------------------------------------------------------------------------
  -- Utility Declarations for terser description/hard-coding of expressions


  -- Assertion Utility functions

  pattern 𝑐𝑜𝑛𝑠𝑡 n = term (Const n)
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



  -- Utility functions relating expression ops to their implementation

  getOp₁ : UnOp → Maybe Val → Maybe Val
  getOp₁ ¬ₒ  = ¬ᵥ
  getOp₁ ++ₒ  = ++ᵥ
  getOp₁ ─-ₒ  = ─-ᵥ
  getOp₁ ──ₒ  = ──ᵥ
  
  getOp₂ : BinOp → Maybe Val → Maybe Val → Maybe Val
  getOp₂ +ₒ   = _+ᵥ_
  getOp₂ -ₒ   = _-ᵥ_
  getOp₂ *ₒ   = _*ᵥ_
  getOp₂ /ₒ   = _/ᵥ_
  getOp₂ %ₒ   = _%ᵥ_
  getOp₂ ≤ₒ   = _≤ᵥ_
  getOp₂ <ₒ   = _<ᵥ_
  getOp₂ ≥ₒ   = _≥ᵥ_
  getOp₂ >ₒ   = _>ᵥ_
  getOp₂ ==ₒ  = _==ᵥ_
  getOp₂ &&ₒ  = _&&ᵥ_
  getOp₂ ||ₒ  = _||ᵥ_



  -------------------------------------------------------------------------------
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





