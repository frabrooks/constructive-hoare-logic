


-- Local Imports
open import Representations.Data-Infinite-Arithmetic
     renaming (Data-Infinite-Arith-Implementation to 𝔡-∞ )
open import Representations.State-As-List
     renaming (State-List-Implementation to 𝔖-List )


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Main where


  -- ════════════════════════════════════════════════════════════════════════════  
  -- Main module to import everything and check interface implementation
  --
  -- This is probably not the place to start if you're looking to get a sense of
  -- what this library is and what can be done with it, you probably want to
  -- examine Hoare-Logic/𝑆𝑤𝑎𝑝𝐸𝑥𝑎𝒎𝑝𝑙𝑒.𝑎𝑔𝑑𝑎 for a proof of correctness of the
  -- swap program.



  -- Import Everything to check it all compiles:

  -- src/Language
  open import Language.Expressions 𝔡-∞ (𝔖-List 𝔡-∞)
  open import Language.Assertions 𝔡-∞ (𝔖-List 𝔡-∞)
  open import Language.ExampleProgs 𝔡-∞ (𝔖-List 𝔡-∞)
  open import Language.Mini-Imp 𝔡-∞ (𝔖-List 𝔡-∞)

  -- src/Evaluation
  open import Evaluation.Termination 𝔡-∞ (𝔖-List 𝔡-∞)
  open import Evaluation.Evaluation 𝔡-∞ (𝔖-List 𝔡-∞)

  -- src/Hoare-Logic
  open import Hoare-Logic.Semantics 𝔡-∞ (𝔖-List 𝔡-∞)
  open import Hoare-Logic.Rules 𝔡-∞ (𝔖-List 𝔡-∞)

  -- Instantiate proof of correctness of swap program with Infinite Arithmetic
  -- data implementation and list state space representation:
  open import Hoare-Logic.SwapExample 𝔡-∞ (𝔖-List 𝔡-∞)






