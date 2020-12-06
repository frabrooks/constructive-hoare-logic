

module integer_operations where


  --open import Relation.Binary.PropositionalEquality as Eq
  --open Eq using ( _≡_  ; refl ; sym ; cong)
  open import Relation.Nullary.Decidable using (False ; True ; isYes ; isNo ; ⌊_⌋ )
  open import Data.Bool as Bool renaming (Bool to 𝔹) using ( true ; false) 
  open import Data.Integer as Int using (ℤ ; _+_ ; _-_ ; _*_ )
  open import Data.Integer.Base using (∣_∣ )  
  open import Data.Integer.DivMod using ( _div_ ; _mod_ )
  open import Data.List as List using (List; _∷_; [] ; map ; _++_ )
  open import Data.String.Properties using (_≈?_)
  open import Data.Nat as ℕ renaming (_+_ to _⊕_ ; _*_ to _⊛_ ) using (ℕ; zero; suc; _∸_; _≤_; pred ; _≟_ ; _≤?_)
  open import Data.Maybe using (Maybe)
  open import Data.Maybe.Categorical as Cₘ
  --open import Data.Maybe.Relation.Binary.Pointwise using (Pointwise ; drop-just)
  open import Data.Product renaming (_,_ to _∧_  )

  open Maybe
  open ℤ


  open import Agda.Builtin.Unit
  open import Data.Empty using (⊥)


  open import operators  -- (categorical operators)
  -- examples of use:
  maybeAdd : Maybe ℤ → Maybe ℤ → Maybe ℤ
  maybeAdd x y = (_+_) <$>ₘ  x ⊛ₘ  y

  maybeAdd' : Maybe ℤ → Maybe ℤ → Maybe ℤ
  maybeAdd' x y = (_+_) <$>⟨ Cₘ.functor ⟩ x ⊛⟨ Cₘ.applicative ⟩ y


  pattern [_] z = z ∷ []
  pattern [_,_] y z = y ∷ z ∷ []
  pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
  pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
  pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
  pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

  data OpName : Set where

       Or :  OpName

       And : OpName

       Eq : OpName

       Leq : OpName
       Less : OpName
       Geq : OpName
       Greater : OpName

       Add : OpName
       Sub : OpName

       Mul : OpName
       Div : OpName
       Mod : OpName
       not : OpName

  ℤBool : ℤ → ℤ
  ℤBool (negsuc _) = pos 0 
  ℤBool (pos n)    = pos (ℕBool n)
    where
    ℕBool : ℕ → ℕ
    ℕBool ℕ.zero = 0
    ℕBool  n     = 1

  
  is-pos : ℤ → ℤ
  is-pos (pos    _) = pos 1
  is-pos (negsuc _) = pos 0

  opEval : OpName → List ( Maybe ℤ ) → Maybe ℤ
  opEval Or  [ x , y ]  =   orℤ <$>ₘ  x ⊛ₘ y
    where
    orℤ : ℤ → ℤ → ℤ
    orℤ (pos 0) (pos 0) = pos 0
    orℤ (pos n)    _    = pos 1
    orℤ   _    (pos n)  = pos 1
    orℤ   _     _       = pos 0
  opEval And  [ x ,  y ]  = andℤ <$>ₘ x ⊛ₘ y
    where
    andℤ : ℤ → ℤ → ℤ
    andℤ (pos 0)  _      = pos 0
    andℤ  _      (pos 0) = pos 0
    andℤ (pos _) (pos _) = pos 1
    andℤ  _       _      = pos 0
  opEval Eq   [ x , y  ]       = eqℤ <$>ₘ x ⊛ₘ y
    where
    is-zero : ℤ → ℤ
    is-zero (pos 0) = pos 1
    is-zero    _    = pos 0
    eqℤ : ℤ → ℤ → ℤ
    eqℤ   x   y = is-zero (x - y)
  opEval Leq  [ x , y ]      = leqℤ <$>ₘ x ⊛ₘ y -- x ≤ y
    where
    is-neg : ℤ → ℤ
    is-neg (negsuc _) = pos 1
    is-neg (pos    _) = pos 0
    leqℤ : ℤ → ℤ → ℤ
    leqℤ   x   y = is-neg ((x - y) - (pos 1))
  opEval Less   [ x , y ]     = lessℤ <$>ₘ x ⊛ₘ y -- x < y
    where
    is-neg : ℤ → ℤ
    is-neg (negsuc _) = pos 1
    is-neg (pos    _) = pos 0
    lessℤ : ℤ → ℤ → ℤ
    lessℤ   x   y = is-neg (x - y)
  opEval Geq  [ x , y ]    = geqℤ <$>ₘ x ⊛ₘ y  -- x ≥ y
    where
    geqℤ : ℤ → ℤ → ℤ
    geqℤ   x   y = is-pos (x - y)
  opEval Greater [ x , y ]     = greaterℤ <$>ₘ x ⊛ₘ y -- x > y
    where
    greaterℤ : ℤ → ℤ → ℤ
    greaterℤ   x   y = is-pos ((x - y) - (pos 1))
  opEval Add  [ x , y ]  = (_+_)   <$>ₘ x ⊛ₘ y
  opEval Sub  [ x , y ]  = (_-_)   <$>ₘ x ⊛ₘ y
  opEval Mul  [ x , y ]  = (_*_)   <$>ₘ x ⊛ₘ y
  opEval Div  [ x , y ]  = (maybeDiv y)  ⊛ₘ x 
    where
    maybe≢0 : (z : ℤ) →  Maybe ( False ( ∣ z ∣ ℕ.≟ 0) )
    maybe≢0 (pos ℕ.zero)         = nothing
    maybe≢0 (Int.+[1+ n ])       = just (tt)
    maybe≢0 (negsuc n)           = just (tt)
    maybeDiv : Maybe ℤ → Maybe (ℤ → ℤ)
    maybeDiv nothing = nothing
    maybeDiv (just divisor) = (λ p → (λ z₁ → (z₁ div divisor) {p} )) <$>ₘ (maybe≢0 divisor)
  opEval Mod  [ x , y ]  = (maybeMod y)  ⊛ₘ x 
    where
    maybe≢0 : (z : ℤ) →  Maybe ( False ( ∣ z ∣ ℕ.≟ 0) )
    maybe≢0 (pos ℕ.zero)         = nothing
    maybe≢0 (Int.+[1+ n ])       = just (tt)
    maybe≢0 (negsuc n)           = just (tt)
    maybeMod : Maybe ℤ → Maybe (ℤ → ℤ)
    maybeMod nothing = nothing
    maybeMod (just divisor) = (λ p → (λ z₁ → pos ((z₁ mod divisor) {p}))) <$>ₘ (maybe≢0 divisor)
  opEval Not  [ x ]      = x >>=ₘ notℤ 
    where
    notℤ : ℤ → Maybe ℤ
    notℤ (pos ℕ.zero) = just (pos 1)
    notℤ Int.+[1+ ℕ.zero ] = just (pos 0)
    notℤ Int.+[1+ ℕ.suc n ] = nothing
    notℤ (negsuc n) = nothing
  opEval _     _           = nothing
