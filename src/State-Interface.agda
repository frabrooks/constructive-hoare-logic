

-- Lib Imports
open import Data.Maybe using (Maybe ; just ; nothing)
open import Relation.Nullary using ( ¬_ )
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)


-- Local Imports
open import Data-Interface using (Data-Implementation)


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module State-Interface ( 𝔡 : Data-Implementation ) where

  -- Local Dependent Imports
  open Data-Implementation 𝔡

  -- ════════════════════════════════════════════════════════════════════════════
  -- State-Interface:
  --
  -- Abstract out the representation of the state space as while reasoning
  -- within the Hoare-Logic calculus, it is undesirable to have knowledge or use
  -- of the fact that the state space is represented as say, a list of pairs,
  -- as the exact representation shouldn't be relevant.

  -- This interface makes clear just what logical rules a Hoare-Logic calculus
  -- requires a particular state space to satisfy. Instantiation of the interface
  -- is not necessary to allow us to reason about programs and provided we have
  -- confidence in all lemmas given here then we will have confidence in any
  -- proofs of program correctness constructed from this library. If, however,
  -- the formalisation is to be complete, and the proofs to have full
  -- computational meaning, it will need to be instantiated and as so it is
  -- implemented within  𝑆𝑡𝑎𝑡𝑒-𝐴𝑠-𝐿𝑖𝑠𝑡.𝑎𝑔𝑑𝑎 in ./src/Representations/.


  -- ════════════════════════════════════════════════════════════════════════════
  record State-Implementation  : Set₁ where

    ---------------------------------------------------------------------------
    field -- Definitions/Declarations

      -- The set of all States (the State Space)
      S              : Set

      -- Initial/Empty State
      ●              : S


    ---------------------------------------------------------------------------
    field -- Operations upon the state space

      updateState    : Id → Val → S → S
      
      getIdVal      : Id → S → Maybe Val
      
      dropValue      : Id → S → S


    ---------------------------------------------------------------------------
    field -- Predicates/Lemmas upon the state space

      updateGet      : ∀ i v s  → getIdVal i (updateState i v s) ≡ just v
      
      ignoreTop      : ∀ i v x → ¬ i ≡ x → (s : S) →
                       getIdVal x (updateState i v s) ≡ getIdVal x s
                       
      irrelUpdate    : ∀ i x v y → ¬ i ≡ x → (s : S) →
                       getIdVal x (updateState i v s) ≡ y → getIdVal x s ≡ y

      updateState¬●  : (i : Id) → (f : Val) → (s : S )
                       → ( updateState i f s ≡ ● ) → ⊥


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━


