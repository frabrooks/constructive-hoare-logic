
-- Lib imports
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )

-- Local Imports
open import Data-Interface using (Data-Implementation)
open import State-Interface using (State-Implementation)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Language.Mini-Imp
  (𝔡 : Data-Implementation )
  (𝔖 : State-Implementation 𝔡 ) where

  -- Local Dependent Imports
  open Data-Implementation 𝔡
  open import Language.Expressions 𝔡 𝔖

  -- ════════════════════════════════════════════════════════════════════════════
  -- Language.Mini-Imp :
  --
  -- A deep embedding of an imperative programming language. Programs can then
  -- be encoded as in 𝐸𝑥𝑎𝑚𝑝𝑙𝑒𝑃𝑟𝑜𝑔𝑠.𝑎𝑔𝑑𝑎 for later reasoning and construction of
  -- correctness proofs in the Hoare-Logic calculus.
  --
  -- ════════════════════════════════════════════════════════════════════════════

  data Block : Set

  -- Commands/Programs/Mechanisms/Statements
  -- Defined as '↪S' (read 'State transformer')
  -- to emphasise all these different meanings
  data ↪S : Set where
    𝑠𝑘𝑖𝑝  : ↪S
    𝔴𝔥𝔦𝔩𝔢_𝒹ℴ_ : Exp → Block → ↪S
    𝔦𝔣_𝔱𝔥𝔢𝔫_𝔢𝔩𝔰𝔢_ : Exp → Block → Block → ↪S
    _:=_ : Id → Exp → ↪S
  open ↪S public

  data Block where
    -- Terminator:
    _;  : ↪S → Block
    -- Separator:
    _;_ : ↪S → Block → Block
  open Block public

  -- Program composition
  _𝔱𝔥𝔢𝔫_ : Block → Block → Block
  (c ;) 𝔱𝔥𝔢𝔫 b = c ; b
  (c ; b₁) 𝔱𝔥𝔢𝔫 b₂ = c ; (b₁ 𝔱𝔥𝔢𝔫 b₂)

  -- Commutativity of program composition
  𝔱𝔥𝔢𝔫-comm : ∀ c₁ c₂ c₃ →
    c₁ 𝔱𝔥𝔢𝔫 (c₂ 𝔱𝔥𝔢𝔫 c₃) ≡ (c₁ 𝔱𝔥𝔢𝔫 c₂) 𝔱𝔥𝔢𝔫 c₃
  𝔱𝔥𝔢𝔫-comm (↪s ;) c₂ c₃ = refl
  𝔱𝔥𝔢𝔫-comm (↪s ; c₁) c₂ c₃
    rewrite 𝔱𝔥𝔢𝔫-comm c₁ c₂ c₃ = refl


  infix  30 𝔦𝔣_𝔱𝔥𝔢𝔫_𝔢𝔩𝔰𝔢_
  infix  30 𝔴𝔥𝔦𝔩𝔢_𝒹ℴ_
  infix  32 _:=_
  infixr 18 _;_
  infix  22 _; 
  infixl 16 _𝔱𝔥𝔢𝔫_ 

  -- Computation is a block of
  -- State transformers
  C : Set
  C = Block

