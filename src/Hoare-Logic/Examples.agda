
-- Project Imports
open import Data using (Data-Implementation)
open import State using (State-Implementation)

open import Misc

module Hoare-Logic.Semantics ( 𝔡 : Data-Implementation )
  (𝔖 : State-Implementation 𝔡 ) where

  open Data-Implementation 𝔡
  open State-Implementation 𝔖

  open import Language.Expressions 𝔡 𝔖
  open import Language.Assertions 𝔡 𝔖

  open import Language.Mini-Imp 𝔡 𝔖

  open import Evaluation.Termination 𝔡 𝔖
  
  open import Hoare-Logic.Semantics 𝔡 𝔖
  open import Hoare-Logic.Axioms 𝔡 𝔖

  


