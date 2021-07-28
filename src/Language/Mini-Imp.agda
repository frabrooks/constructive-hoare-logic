
-- Lib imports
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import Data.Maybe using ( Maybe ; just ; nothing )
open import Data.Bool using ( true )
import Data.Integer using ( ℤ )
import Data.Nat using (ℕ)
open import Data.Empty
open import Data.Unit using ( ⊤ )
open import Data.Product

open import Data using (Data-Implementation)
open import State using (State-Implementation)

module Language.Mini-Imp
  (𝔡 : Data-Implementation )
  (𝔖 : State-Implementation 𝔡 ) where

  open Data-Implementation 𝔡
  open import Language.Expressions 𝔡 𝔖


  -- Commands/Programs/Computations
  data Block : Set
  {-
  -- Assignment
  _:=_ : Id → Exp → Set
  _ := _ = ⊤

  -- Control Flow
  𝔦𝔣_𝔱𝔥𝔢𝔫_𝔢𝔩𝔰𝔢_ : Exp → Block → Block → Set
  𝔦𝔣 _ 𝔱𝔥𝔢𝔫 _ 𝔢𝔩𝔰𝔢 _ = ⊤

  -- Looping
  𝔴𝔥𝔦𝔩𝔢_𝒹ℴ_ : Exp → Block → Set
  𝔴𝔥𝔦𝔩𝔢 _ 𝒹ℴ _ = ⊤
  -}

  data ↪S : Set where
    𝑠𝑘𝑖𝑝  : ↪S
    𝔴𝔥𝔦𝔩𝔢_𝒹ℴ_ : Exp → Block → ↪S
    𝔦𝔣_𝔱𝔥𝔢𝔫_𝔢𝔩𝔰𝔢_ : Exp → Block → Block → ↪S
    _:=_ : Id → Exp → ↪S
  open ↪S public

  infix 30 𝔦𝔣_𝔱𝔥𝔢𝔫_𝔢𝔩𝔰𝔢_
  infix 30 𝔴𝔥𝔦𝔩𝔢_𝒹ℴ_
  infix 32 _:=_
  
  data Block where
    _;  : ↪S → Block
    _;_ : ↪S → Block → Block
  open Block public

  infixr 18 _;_
  infix  31 _; 


  _𝔱𝔥𝔢𝔫_ : Block → Block → Block
  (c ;) 𝔱𝔥𝔢𝔫 b = c ; b
  (c ; b₁) 𝔱𝔥𝔢𝔫 b₂ = c ; (b₁ 𝔱𝔥𝔢𝔫 b₂)

  infixl 16 _𝔱𝔥𝔢𝔫_ 

  𝔱𝔥𝔢𝔫-comm : ∀ c₁ c₂ c₃ →
    c₁ 𝔱𝔥𝔢𝔫 (c₂ 𝔱𝔥𝔢𝔫 c₃) ≡ (c₁ 𝔱𝔥𝔢𝔫 c₂) 𝔱𝔥𝔢𝔫 c₃
  𝔱𝔥𝔢𝔫-comm (↪s ;) c₂ c₃ = refl
  𝔱𝔥𝔢𝔫-comm (↪s ; c₁) c₂ c₃
    rewrite 𝔱𝔥𝔢𝔫-comm c₁ c₂ c₃ = refl

  -- Computation is a block of
  -- State transformers
  C : Set
  C = Block


