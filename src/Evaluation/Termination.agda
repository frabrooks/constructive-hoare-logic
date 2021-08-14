
-- Lib Imports
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import Data.Maybe using ( Maybe ; just ; Is-just ; to-witness ; map )
open import Data.Maybe.Relation.Unary.Any using (Any)
open import Data.Product using (Σ ; Σ-syntax ; _×_  ; _,_  ; proj₂ )
open import Data.Bool using ( true ; false )
open import Data.Unit using ( tt )
open import Function using ( _∘_ )
open import Data.Nat.Properties using ( +-comm ; +-identityʳ )
open import Data.Nat using (ℕ ; suc ; zero ; _≤″_  )
            renaming (_+_ to _+ᴺ_ ; less-than-or-equal to ≤with )
open _≤″_

-- Local Imports
open import Data-Interface using (Data-Implementation )
open import State-Interface using (State-Implementation)
open import Misc using ( suc≤″ )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Evaluation.Termination (𝔡 : Data-Implementation  )
  (𝔖 : State-Implementation 𝔡 ) where

  -- Local Dependent Imports
  open Data-Implementation 𝔡
  open State-Implementation 𝔖
  open import Language.Expressions 𝔡 𝔖
  open import Language.Mini-Imp 𝔡 𝔖
  open import Language.Assertions 𝔡 𝔖
  open import Evaluation.Evaluation 𝔡 𝔖

  -- ════════════════════════════════════════════════════════════════════════════
  -- Evaluation.Termination :
  --
  -- Definition of what it means for a program - as defined in 𝑀𝑖𝑛𝑖-𝐼𝒎𝑝.𝑎𝑔𝑑𝑎 -
  -- to terminate under the small-step evaluation defined in 𝐸𝑣𝑎𝑙𝑢𝑎𝑡𝑖𝑜𝑛.𝑎𝑔𝑑𝑎, as
  -- well as a series of lemmas to aid in formalising the key rules for
  -- reasoning in Hoare-Logic in 𝑅𝑢𝑙𝑒𝑠.𝑎𝑔𝑑𝑎.


  -- ════════════════════════════════════════════════════════════════════════════  
  -- Key Definitions :

  -- Proof of termination
  Terminates : C → S → Set
  Terminates c s = Σ[ ℱ ∈ ℕ ] ( Is-just (ssEvalwithFuel ℱ c s ))

  -- Proof of termination indexed by the amount of fuel used
  TerminatesWith : ℕ → C → S → Set
  TerminatesWith ℱ c s = Is-just (ssEvalwithFuel ℱ c s)


  -- Alternative condensed syntax
  ⌊ᵗ_⸴_ᵗ⌋ : C → S → Set
  ⌊ᵗ_⸴_ᵗ⌋ = Terminates

  -- Alternative condensed indexed syntax
  ⌊ᵗ_⸴_⸴_ᵗ⌋ : ℕ → C → S → Set
  ⌊ᵗ ℱ ⸴ c ⸴ s ᵗ⌋ = TerminatesWith ℱ c s

  -- Get result of terminating evaluation
  Result : ∀ {c s} → ⌊ᵗ c ⸴ s ᵗ⌋ → S
  Result = to-witness ∘ proj₂
  -- Alternative condensed syntax
  ‵ : ∀ {c s} → ⌊ᵗ c ⸴ s ᵗ⌋ → S
  ‵ = Result

  -- Get result of indexed terminating evaluation
  Result″ = to-witness  
  -- Alternative condensed syntax
  ″ = to-witness

  -- ════════════════════════════════════════════════════════════════════════════  
  -- Simple lemmas

  -- It is trivial to show that 𝑠𝑘𝑖𝑝 terminates with any amount of fuel
  ⌊ᵗ𝑠𝑘𝑖𝑝ᵗ⌋ : ∀ {s} n → ⌊ᵗ n ⸴ 𝑠𝑘𝑖𝑝 ; ⸴ s ᵗ⌋ 
  ⌊ᵗ𝑠𝑘𝑖𝑝ᵗ⌋ zero    = Any.just tt
  ⌊ᵗ𝑠𝑘𝑖𝑝ᵗ⌋ (suc ℱ) = Any.just tt

  -- Also trivially, if exp 𝑒 is a well formed formula then assignment
  -- of 𝑒 to a variable always terminates.
  𝑊𝐹𝐹⦅e⦆→⌊ᵗi:=e;⌋ᵗ : ∀ s i e → 𝑊𝐹𝐹 e s → ⌊ᵗ i := e ; ⸴ s ᵗ⌋
  𝑊𝐹𝐹⦅e⦆→⌊ᵗi:=e;⌋ᵗ  s i e _ = 1 , go
    where
    go : Is-just (map (λ v → updateState i v s) (evalExp e s))
    go with evalExp e s
    ... | (just v) = Any.just tt

  -- Any two proofs of Is-just for the same x are the same
  ∃!IJ : ∀ {x : Maybe S} → ( a b : Is-just x) → a ≡ b
  ∃!IJ .{just _} (Any.just x) (Any.just x₁) = refl
  -- This is only used in the proof of determinism below.



  -- ════════════════════════════════════════════════════════════════════════════
  -- Evaluation is Deterministic:

  -- i.e. any two proofs of termination will have identical resultant states,
  -- adding more fuel doesn't change anything.

  ------------------------------------------------------------------------------- 
  EvalDet : ∀ {s ℱ ℱ'} C
                     → (a : ⌊ᵗ ℱ ⸴ C ⸴ s ᵗ⌋) → (b : ⌊ᵗ ℱ' ⸴ C ⸴ s ᵗ⌋) → ″ a ≡ ″ b
  -------------------------------------------------------------------------------                      
  pattern ⇧ x = suc x
  EvaluationIsDeterministic = EvalDet
  -------------------------------------------------------------------------------  
  EvalDet {s} {0} {0} (_ ;) ij₁ ij₂ rewrite ∃!IJ ij₁ ij₂ = refl
  EvalDet {s} {0} {⇧ _} (𝑠𝑘𝑖𝑝 ;) ij₁ ij₂ rewrite ∃!IJ ij₁ ij₂ = refl
  EvalDet {s} {⇧ _} {0} (𝑠𝑘𝑖𝑝 ;) ij₁ ij₂ rewrite ∃!IJ ij₁ ij₂ = refl
  EvalDet {s} {⇧ _} {⇧ _} (𝑠𝑘𝑖𝑝 ;) ij₁ ij₂ rewrite ∃!IJ ij₁ ij₂ = refl
  EvalDet {s} {⇧ ℱ} {⇧ ℱ'} ((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c) ;) ij₁ ij₂
    with evalExp exp s
  ... | cond@(just _) with toTruthValue {cond} (Any.just tt)
  ... | false rewrite ∃!IJ ij₁ ij₂ = refl
  ... | true = EvalDet {s} {ℱ} {ℱ'} _ ij₁ ij₂
  EvalDet {s} {⇧ ℱ} {⇧ ℱ'} ((𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ;) ij₁ ij₂
    with evalExp exp s
  ... | cond@(just _) with toTruthValue {cond} (Any.just tt)
  ... | false = EvalDet {s} {ℱ} {ℱ'} _ ij₁ ij₂
  ... | true = EvalDet {s} {ℱ} {ℱ'} _ ij₁ ij₂
  EvalDet {s} {⇧ ℱ} {⇧ ℱ'} ((id := exp) ;) ij₁ ij₂
    with evalExp exp s
  ... | (just _) rewrite ∃!IJ ij₁ ij₂ = refl
  EvalDet {s} {⇧ ℱ} {⇧ ℱ'} ((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c₁) ; c₂) ij₁ ij₂
    with evalExp exp s
  ... | cond@(just _) with toTruthValue {cond} (Any.just tt)
  ... | false = EvalDet {s} {ℱ} {ℱ'} _ ij₁ ij₂
  ... | true = EvalDet {s} {ℱ} {ℱ'} _ ij₁ ij₂
  EvalDet {s} {⇧ ℱ} {⇧ ℱ'} ((𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ; c₃) ij₁ ij₂
    with evalExp exp s
  ... | cond@(just _) with toTruthValue {cond} (Any.just tt)
  ... | false = EvalDet {s} {ℱ} {ℱ'} _ ij₁ ij₂
  ... | true = EvalDet {s} {ℱ} {ℱ'} _ ij₁ ij₂
  EvalDet {s} {⇧ ℱ} {⇧ ℱ'} ((id := exp) ; c) ij₁ ij₂
    with evalExp exp s
  ... | (just v) = EvalDet {updateState id v s} {ℱ} {ℱ'} _ ij₁ ij₂
  EvalDet {s} {⇧ ℱ} {⇧ ℱ'} (𝑠𝑘𝑖𝑝 ; c) = EvalDet {s} {⇧ ℱ} {⇧ ℱ'} c
  EvalDet {s} {0} {0} (𝑠𝑘𝑖𝑝 ; c) ij₁ ij₂ rewrite ∃!IJ ij₁ ij₂ = refl
  -- In the clause below, with ℱ = 0 and ℱ' = ⇧ _, the only possibility if we
  -- are still to have two proofs of termination in ij₁ and ij₂ is that the
  -- rest of the mechanisms in c are all 𝑎𝑙𝑠𝑜 `𝑠𝑘𝑖𝑝'. So we take each of the two
  -- cases of either c = (𝑠𝑘𝑖𝑝 ;) or c = (𝑠𝑘𝑖𝑝 ; ... ; (𝑠𝑘𝑖𝑝 ;)) in turn.
  -- Annoyingly we have to do this for both permutations of ℱ/ℱ' = 0/⇧ _
  EvalDet {s} {0} {⇧ ℱ'} (𝑠𝑘𝑖𝑝 ; (𝑠𝑘𝑖𝑝 ;)) ij₁ ij₂ rewrite ∃!IJ ij₁ ij₂ = refl
  EvalDet {s} {0} {⇧ ℱ'} (𝑠𝑘𝑖𝑝 ; (𝑠𝑘𝑖𝑝 ; c)) = EvalDet {s} {0} {⇧ ℱ'} c
  EvalDet {s} {⇧ ℱ} {0} (𝑠𝑘𝑖𝑝 ; (𝑠𝑘𝑖𝑝 ;)) ij₁ ij₂ rewrite ∃!IJ ij₁ ij₂ = refl
  EvalDet {s} {⇧ ℱ} {0} (𝑠𝑘𝑖𝑝 ; (𝑠𝑘𝑖𝑝 ; c)) = EvalDet {s} {⇧ ℱ} {0} c
  -------------------------------------------------------------------------------
  




  -- ════════════════════════════════════════════════════════════════════════════
  -- Adding fuel doesn't change the fact that a program terminates:

  ------------------------------------------------------------------------------- 
  addFuel : ∀ {C} {s} ℱ ℱ' → ⌊ᵗ ℱ ⸴ C ⸴ s ᵗ⌋ → ⌊ᵗ (ℱ +ᴺ ℱ') ⸴ C ⸴ s ᵗ⌋
  ------------------------------------------------------------------------------- 
  addFuel {𝑠𝑘𝑖𝑝 ;}   {s} ℱ ℱ' t₁ = ⌊ᵗ𝑠𝑘𝑖𝑝ᵗ⌋ (ℱ +ᴺ ℱ')
  addFuel {𝑠𝑘𝑖𝑝 ; C} {s} ℱ ℱ' t₁
           rewrite 𝑠𝑘𝑖𝑝Elimₗ (ℱ +ᴺ ℱ') C s | 𝑠𝑘𝑖𝑝Elimₗ ℱ C s
           = addFuel {C} {s} ℱ ℱ' t₁
  ----------------------------------------------------------------   ⇧ skip case
  addFuel {(𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c) ;} {s} (suc ℱ) ℱ' t₁
      with evalExp exp s
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | false = Any.just tt  
  ... | true  = addFuel ℱ ℱ' t₁
  addFuel {(𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c) ; C} {s} (suc ℱ) ℱ' t₁ 
      with evalExp exp s
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | false = addFuel ℱ ℱ' t₁
  ... | true  = addFuel ℱ ℱ' t₁
  ---------------e-----------------------------------------------   ⇧ while case
  addFuel {(𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ;} {s} (suc ℱ) ℱ' t₁
      with evalExp exp s
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | false = addFuel ℱ ℱ' t₁
  ... | true  = addFuel ℱ ℱ' t₁
  addFuel {(𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ; C} {s} (suc ℱ) ℱ' t₁
      with evalExp exp s
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | false = addFuel ℱ ℱ' t₁
  ... | true  = addFuel ℱ ℱ' t₁  
  --------------------------------------------------------------- ⇧ if else case
  addFuel {(id := exp) ;} {s} (suc ℱ) ℱ' t₁ with evalExp exp s
  ... | f@(just _) = t₁
  addFuel {(id := exp) ; C} {s} (suc ℱ) ℱ' t₁ with evalExp exp s
  ... | f@(just _) = addFuel ℱ ℱ' t₁  
 ---------------------------------------------------------------- ⇧ assign. case





  -- ════════════════════════════════════════════════════════════════════════════
  -- Termination Proof Splitting:

  -- A proof of termination of a program of two constituent parts can always be
  -- split into two proofs of termination for the corresponding parts in which
  -- the fuel needed for the second half will be less than the original fuel


  ------------------------------------------------------------------------------- 
  ⌊ᵗ⌋-split' : ∀ ℱ s Q₁ Q₂ → (t₁₂ : ⌊ᵗ ℱ ⸴ Q₁ 𝔱𝔥𝔢𝔫 Q₂ ⸴ s ᵗ⌋)
              → Σ ⌊ᵗ ℱ ⸴ Q₁ ⸴ s ᵗ⌋ (λ t₁
              → Σ ℕ (λ ℱ'
              → ℱ' ≤″ ℱ × Σ ⌊ᵗ ℱ' ⸴ Q₂ ⸴ ″ t₁ ᵗ⌋ (λ t₂
              → ″ t₂ ≡ ″ t₁₂ )))
  ------------------------------------------------------------------------------- 

  --------------------------------------------------------------------
  -- Base case: Q₁ = 𝑠𝑘𝑖𝑝 ;
  ⌊ᵗ⌋-split' ℱ@0 s (𝑠𝑘𝑖𝑝 ;) Q₂ t₁₂ =
          (Any.just tt) , ℱ , ≤with refl  , t₁₂ , refl
  ⌊ᵗ⌋-split' ℱ@(suc _) s (𝑠𝑘𝑖𝑝 ;) Q₂ t₁₂ =
          (Any.just tt) , ℱ , ≤with (+-comm ℱ 0) , t₁₂ , refl          
  -- Q₁ = 𝑠𝑘𝑖𝑝 : Q₁ '
  ⌊ᵗ⌋-split' ℱ@0       s (𝑠𝑘𝑖𝑝 ; Q₁') = ⌊ᵗ⌋-split' ℱ s Q₁'
  ⌊ᵗ⌋-split' ℱ@(suc _) s (𝑠𝑘𝑖𝑝 ; Q₁') = ⌊ᵗ⌋-split' ℱ s Q₁'


  --------------------------------------------------------------------
  -- Most interesting inductive case: 𝔴𝔥𝔦𝔩𝔢 followed by Q₁' 𝔱𝔥𝔢𝔫 Q₂.
  -- All other cases follow a similar recursive mechanism
  ⌊ᵗ⌋-split' (suc ℱ) s Q₁@((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c) ; Q₁') Q₂ t₁₂ = go
    where
    go : Σ ⌊ᵗ suc ℱ ⸴ Q₁ ⸴ s ᵗ⌋ (λ t₁ → Σ ℕ (λ ℱ' → ℱ' ≤″ suc ℱ ×
         Σ ⌊ᵗ ℱ' ⸴ Q₂ ⸴ ″ t₁ ᵗ⌋ (λ t₂ → ″ t₂ ≡ ″ t₁₂ )))             
    go with evalExp exp s
    go | f@(just _) with toTruthValue {f} (Any.just tt)
    -- if false ---------------------------------------
    go | f@(just _) | false with ⌊ᵗ⌋-split' ℱ s Q₁' Q₂ t₁₂
    go | just _     | false |  t₁ , ℱ' , lt       , t₂ , Δ
                            =  t₁ , ℱ' , suc≤″ lt , t₂ , Δ
    -- if true ---------------------------------------- 
    go | f@(just _) | true rewrite
         𝔱𝔥𝔢𝔫-comm ((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c) ;) Q₁' Q₂
       | 𝔱𝔥𝔢𝔫-comm c ((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c) ;  Q₁' ) Q₂ with
         ⌊ᵗ⌋-split' ℱ s (c 𝔱𝔥𝔢𝔫 𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c ; Q₁') Q₂ t₁₂
    go | f@(just _) | true |  t₁ , ℱ' , lt       , t₂ , Δ
                           =  t₁ , ℱ' , suc≤″ lt , t₂ , Δ


  --------------------------------------------------------------------
  -- Q₁ = 𝔴𝔥𝔦𝔩𝔢 ;
  ⌊ᵗ⌋-split' (suc ℱ) s Q₁@((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c) ;) Q₂ t₁₂ = go
    where
    go : Σ ⌊ᵗ suc ℱ ⸴ Q₁ ⸴ s ᵗ⌋ (λ t₁ → Σ ℕ (λ ℱ' → ℱ' ≤″ suc ℱ ×
         Σ ⌊ᵗ ℱ' ⸴ Q₂ ⸴ ″ t₁ ᵗ⌋ (λ t₂ → ″ t₂ ≡ ″ t₁₂ )))             
    go with evalExp exp s
    go | f@(just _) with toTruthValue {f} (Any.just tt)
    -- if false ---------------------------------------
    go | f@(just _) | false
       = (Any.just tt) , ℱ , ≤with (+-comm ℱ 1) , t₁₂ , refl
    -- if true ---------------------------------------- 
    go | f@(just _) | true  rewrite
         𝔱𝔥𝔢𝔫-comm c ((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c) ;) Q₂ with
         ⌊ᵗ⌋-split' ℱ s (c 𝔱𝔥𝔢𝔫 𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c ;) Q₂ t₁₂
    go | f@(just _) | true |  t₁ , ℱ' , lt       , t₂ , Δ
                           =  t₁ , ℱ' , suc≤″ lt , t₂ , Δ
  --------------------------------------------------------------------
  -- Q₁ = if then else ; Q₁'
  ⌊ᵗ⌋-split' (suc ℱ) s Q₁@((𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ; Q₁') Q₂ t₁₂
    = go
    where
    go : Σ ⌊ᵗ suc ℱ ⸴ Q₁ ⸴ s ᵗ⌋ (λ t₁ → Σ ℕ (λ ℱ' → ℱ' ≤″ suc ℱ ×
         Σ ⌊ᵗ ℱ' ⸴ Q₂ ⸴ ″ t₁ ᵗ⌋ (λ t₂ → ″ t₂ ≡ ″ t₁₂ )))             
    go with evalExp exp s
    go | f@(just _) with toTruthValue {f} (Any.just tt)
    -- if false ---------------------------------------
    go | f@(just _) | false rewrite 𝔱𝔥𝔢𝔫-comm c₂ Q₁' Q₂
                      with  ⌊ᵗ⌋-split' ℱ s (c₂ 𝔱𝔥𝔢𝔫 Q₁') Q₂ t₁₂
    go | f@(just _) | false |  t₁ , ℱ' , lt       , t₂ , Δ
                            =  t₁ , ℱ' , suc≤″ lt , t₂ , Δ
    -- if true ---------------------------------------- 
    go | f@(just _) | true  rewrite 𝔱𝔥𝔢𝔫-comm c₁ Q₁' Q₂
                    with  ⌊ᵗ⌋-split' ℱ s (c₁ 𝔱𝔥𝔢𝔫 Q₁') Q₂ t₁₂
    go | f@(just _) | true  |  t₁ , ℱ' , lt       , t₂ , Δ
                            =  t₁ , ℱ' , suc≤″ lt , t₂ , Δ
  --------------------------------------------------------------------
  -- Q₁ = if then else                            
  ⌊ᵗ⌋-split' (suc ℱ) s Q₁@((𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ;) Q₂ t₁₂
    = go
    where
    go : Σ ⌊ᵗ suc ℱ ⸴ Q₁ ⸴ s ᵗ⌋ (λ t₁ → Σ ℕ (λ ℱ' → ℱ' ≤″ suc ℱ ×
         Σ ⌊ᵗ ℱ' ⸴ Q₂ ⸴ ″ t₁ ᵗ⌋ (λ t₂ → ″ t₂ ≡ ″ t₁₂ )))             
    go with evalExp exp s
    go | f@(just _) with toTruthValue {f} (Any.just tt)
    -- if false ---------------------------------------
    go | f@(just _) | false with ⌊ᵗ⌋-split' ℱ s c₂ Q₂ t₁₂
    go | f@(just _) | false |  t₁ , ℱ' , lt       , t₂ , Δ
                            =  t₁ , ℱ' , suc≤″ lt , t₂ , Δ
    -- if true ---------------------------------------- 
    go | f@(just _) | true  with ⌊ᵗ⌋-split' ℱ s c₁ Q₂ t₁₂
    go | f@(just _) | true  |  t₁ , ℱ' , lt       , t₂ , Δ
                            =  t₁ , ℱ' , suc≤″ lt , t₂ , Δ 
  --------------------------------------------------------------------
  -- Q₁ = x := exp ; Q₁'
  ⌊ᵗ⌋-split' (suc ℱ) s Q₁@( id := exp  ; Q₁') Q₂ t₁₂ = go
    where
    go : Σ ⌊ᵗ suc ℱ ⸴ Q₁ ⸴ s ᵗ⌋ (λ t₁ → Σ ℕ (λ ℱ' → ℱ' ≤″ suc ℱ ×
         Σ ⌊ᵗ ℱ' ⸴ Q₂ ⸴ ″ t₁ ᵗ⌋ (λ t₂ → ″ t₂ ≡ ″ t₁₂ )))             
    go with evalExp exp s
    go | f@(just v)
       with ⌊ᵗ⌋-split' ℱ (updateState id v s) Q₁' Q₂ t₁₂
    go | f@(just v) |  t₁ , ℱ' , lt       , t₂ , Δ
                    =  t₁ , ℱ' , suc≤″ lt , t₂ , Δ     
  --------------------------------------------------------------------
  -- Q₁ = id := exp ;
  ⌊ᵗ⌋-split' (suc ℱ) s Q₁@( id := exp ;) Q₂ t₁₂ = go
    where
    go : Σ ⌊ᵗ suc ℱ ⸴ Q₁ ⸴ s ᵗ⌋ (λ t₁ → Σ ℕ (λ ℱ' → ℱ' ≤″ suc ℱ ×
         Σ ⌊ᵗ ℱ' ⸴ Q₂ ⸴ ″ t₁ ᵗ⌋ (λ t₂ → ″ t₂ ≡ ″ t₁₂ )))             
    go with evalExp exp s
    ... | f@(just _)
        = (Any.just tt) , ℱ , ≤with (+-comm ℱ 1) , t₁₂ , refl
  --------------------------------------------------------------------
  
  --------------------------------------------------------------------
  -- Alternative definition with record as output so as to avoid this
  -- `proj₁ proj₂ proj₁ proj₁ ...'-business muddying up the Agda prose
  -- For some reason Agda was unwilling to accept at the type level
  -- a definition making use of record syntax making necessary the
  -- baroque form above.
  
  record Split-⌊ᵗ⌋ s ℱ Q₁ Q₂ (ϕ : ⌊ᵗ ℱ ⸴ Q₁ 𝔱𝔥𝔢𝔫 Q₂ ⸴ s ᵗ⌋) : Set where
    field
      ----- Termination Left
      Lᵗ    : ⌊ᵗ ℱ ⸴  Q₁ ⸴ s ᵗ⌋
      ----- There's an ℱ' s.t.
      ℱ'   : ℕ
      ----- Termination Right
      Rᵗ    : ⌊ᵗ ℱ' ⸴ Q₂  ⸴ (″ Lᵗ) ᵗ⌋
      ----- and:
      lt : ℱ' ≤″ ℱ 
      ----- Output unchanged
      Δ  : ″ Rᵗ ≡ ″ ϕ   
  open Split-⌊ᵗ⌋ public


  ⌊ᵗ⌋-split : ∀ ℱ s Q₁ Q₂ → (t₁₂ : ⌊ᵗ ℱ ⸴ Q₁ 𝔱𝔥𝔢𝔫 Q₂ ⸴ s ᵗ⌋)
             → Split-⌊ᵗ⌋ s ℱ Q₁ Q₂ t₁₂
  ⌊ᵗ⌋-split ℱ s Q₁ Q₂ t₁₂ with ⌊ᵗ⌋-split' ℱ s Q₁ Q₂ t₁₂
  ...| t₁ , ℱ' , lt , t₂ , Δ
     = record { Lᵗ = t₁ ; ℱ' = ℱ' ; Rᵗ = t₂ ; lt = lt ; Δ = Δ }



  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

