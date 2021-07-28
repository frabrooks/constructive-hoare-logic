

open import Representation.Data using (D-Representation)
open import Representation.State using (S-Representation)

module Mini-C.Expressions (dRep : D-Representation )
  (sRep : S-Representation dRep ) where

open D-Representation dRep
open S-Representation sRep

open import List-Patterns
open import Data.Maybe using (Maybe ; nothing ; just )
open import Data.List as List using (List; _∷_; []  )

data Exp : Set
data 𝔹Exp : Set

data Terminal : Set where
  Const  : Val → Terminal
  Var    : Id  → Terminal
  𝒕      : Terminal
  𝒇      : Terminal


data ℤ→ℤ→ℤ : Set where
  +ᶻ  : ℤ→ℤ→ℤ
  -ᶻ  : ℤ→ℤ→ℤ
  *ᶻ  : ℤ→ℤ→ℤ
  /ᶻ  : ℤ→ℤ→ℤ
  %ᶻ  : ℤ→ℤ→ℤ

data ℤ→ℤ : Set where
-- i.e. (++) & (--)
-- none atm, may add later

data ℤExp : Set where
  𝔹Exp-ℤExp     : 𝔹Exp → ℤExp
  binary-ℤ-op:ℤ : ℤExp → ℤ→ℤ→ℤ → ℤExp → ℤExp
  termℤ         : Terminal → ℤExp

pattern ⇉ᶻ l o r = binary-ℤ-op:ℤ l o r
-- pattern ⇾ᶻ o e    = binary-ℤ-op:ℤ o e

data ℤ→ℤ→𝔹 : Set where
  ≤    : ℤ→ℤ→𝔹
  <    : ℤ→ℤ→𝔹
  ==   : ℤ→ℤ→𝔹
  ≥    : ℤ→ℤ→𝔹
  >    : ℤ→ℤ→𝔹

data 𝔹→𝔹→𝔹 : Set where
  &&   : 𝔹→𝔹→𝔹
  ||   : 𝔹→𝔹→𝔹
  ⇔  : 𝔹→𝔹→𝔹


data 𝔹→𝔹 : Set where
  ¬ᵇ    : 𝔹→𝔹

data 𝔹Exp where  
  binary-ℤ-op:𝔹 : ℤExp → ℤ→ℤ→𝔹 → ℤExp → 𝔹Exp
  binary-𝔹-op:𝔹 : 𝔹Exp → 𝔹→𝔹→𝔹 → 𝔹Exp → 𝔹Exp
  unary-𝔹-op:𝔹  : 𝔹→𝔹 → 𝔹Exp → 𝔹Exp
  term𝔹         : Terminal → 𝔹Exp


pattern ⇉ᵇ l o r = binary-𝔹-op:𝔹 l o r
pattern ᶻ⇉ᵇ l o r  = binary-ℤ-op:𝔹 l o r 
pattern ⇾ᵇ o e = unary-𝔹-op:𝔹 o e

-- Top level of the grammar
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
data Exp where
  𝔹: : 𝔹Exp → Exp
  ℤ: : ℤExp → Exp
  term: : Terminal → Exp 


getOpᶻ : ℤ→ℤ→ℤ → Maybe Val → Maybe Val → Maybe Val
getOpᶻ +ᶻ = _+𝓿_
getOpᶻ -ᶻ = _-𝓿_
getOpᶻ *ᶻ = _*𝓿_
getOpᶻ /ᶻ = _/𝓿_
getOpᶻ %ᶻ = _%𝓿_

getOpᶻᵇ : ℤ→ℤ→𝔹 → Maybe Val → Maybe Val → Maybe Val
getOpᶻᵇ ≤ = _≤𝓿_
getOpᶻᵇ < = _<𝓿_
getOpᶻᵇ == = _==𝓿_
getOpᶻᵇ ≥ = _≥𝓿_
getOpᶻᵇ > = _>𝓿_

getOpᵇ : 𝔹→𝔹→𝔹 → Maybe Val → Maybe Val → Maybe Val
getOpᵇ && = _&&𝓿_
getOpᵇ || = _||𝓿_
getOpᵇ ⇔ = _==𝓿_


{-
evalℤExp : ℤExp → S → Maybe Val
evalℤExp (binary-ℤ-op:ℤ l α r) s = let _∙_ = getOpᶻ α in evalℤExp l s ∙ evalℤExp r s
evalℤExp (Const x) s = just x
evalℤExp (Var x) s = getVarVal x s

eval𝔹Exp : 𝔹Exp → S → Maybe Val
eval𝔹Exp (binary-ℤ-op:𝔹 l α r) s = let _∙_ = getOpᶻᵇ α in evalℤExp l s ∙ evalℤExp r s
eval𝔹Exp (binary-𝔹-op:𝔹 l α r) s = let _∙_ = getOpᵇ α in eval𝔹Exp l s ∙ eval𝔹Exp r sw
eval𝔹Exp (unary-𝔹-op:𝔹 ¬ᵇ e) s = !𝓿 (eval𝔹Exp e s)
eval𝔹Exp 𝒕 s = just 𝑻
eval𝔹Exp 𝒇 s = just 𝑭
-}


-- Evaluation of expressions:
evalExp : Exp → S → Maybe Val
eval𝔹Exp : 𝔹Exp → S → Maybe Val
evalℤExp : ℤExp → S → Maybe Val
evalTerm : Terminal → S → Maybe Val


evalTerm (Const x) _ = just x
evalTerm (Var x)   s = getVarVal x s
evalTerm  𝒕 _ = just 𝑻
evalTerm  𝒇 _ = just 𝑭


evalℤExp (⇉ᶻ l α r) s = let _∙_ = getOpᶻ α in evalℤExp l s ∙ evalℤExp r s
evalℤExp (𝔹Exp-ℤExp b) s = eval𝔹Exp b s
evalℤExp (termℤ t) s = evalTerm t s

eval𝔹Exp (ᶻ⇉ᵇ l α r) s = let _∙_ = getOpᶻᵇ α in evalℤExp l s ∙ evalℤExp r s
eval𝔹Exp (⇉ᵇ l α r) s = let _∙_ = getOpᵇ α in eval𝔹Exp l s ∙ eval𝔹Exp r s
eval𝔹Exp (⇾ᵇ ¬ᵇ e) s = !𝓿 (eval𝔹Exp e s)
eval𝔹Exp (term𝔹 t ) s = evalTerm t s

evalExp (𝔹: e) s = eval𝔹Exp e s
evalExp (ℤ: e) s = evalℤExp e s
evalExp (term: t) s = evalTerm t s



