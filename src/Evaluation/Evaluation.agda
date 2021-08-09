


-- Lib imports
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; inspect ; [_] )
open import Data.Maybe using ( Maybe ; just ; nothing ; map ; _>>=_ ; Is-just ; to-witness )
open import Data.Maybe.Relation.Unary.Any using (Any)
open import Data.Bool using ( true ; false )
open import Relation.Nullary using (  yes ; no ; ¬_ ) 
open import Data.Product using (Σ ; Σ-syntax ; _×_  ; _,_  ; proj₁ ; proj₂ )
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Nat using (ℕ ; suc ; zero)
open import Data.Integer using (ℤ)
open ℤ
open import Data.Empty
open import Data.Unit using ( ⊤ ; tt )


-- Project imports
open import Data-Interface using (Data-Implementation )
open import State-Interface using (State-Implementation)
open import Misc


module Evaluation.Evaluation (𝔡 : Data-Implementation )
  (𝔖 : State-Implementation 𝔡 ) where

  open Data-Implementation 𝔡
  open State-Implementation 𝔖

  open import Language.Expressions 𝔡 𝔖
  open import Language.Mini-Imp 𝔡 𝔖

  evalAssi : Id → Exp → S → Maybe S
  evalAssi id exp s =  map (λ v → updateState id v s) (evalExp exp s) 
  
  is-JustExp→is-JustAssi : ∀ {i e s}
                         → WFF (evalExp e s) → WFF (evalAssi i e s)
  is-JustExp→is-JustAssi {i} {e} {s} p with (evalExp e s)
  ... | just _ = Any.just tt
  
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  ssEvalwithFuel :  ℕ → C → S → Maybe S
  -----------------------------------------------------------------
  -- Skip ⇒ eval finished successfully
  -- Computation Successful 
  ssEvalwithFuel zero (𝑠𝑘𝑖𝑝 ;) s = just s
  ssEvalwithFuel (suc n) ( 𝑠𝑘𝑖𝑝 ;) s = just s
  -----------------------------------------------------------------
  -- Out of fuel
  -- Need to explicitly give all four cases here so
  -- Agda can see `eval zero C = c , nothing` is always
  -- definitionally true.
  ssEvalwithFuel zero ( 𝔴𝔥𝔦𝔩𝔢 _ 𝒹ℴ _ ;) _ = nothing
  ssEvalwithFuel zero ( 𝔦𝔣 _ 𝔱𝔥𝔢𝔫 _ 𝔢𝔩𝔰𝔢 _ ;) _ = nothing
  ssEvalwithFuel zero ( _ := _ ; ) _ = nothing
  ssEvalwithFuel zero ((𝔴𝔥𝔦𝔩𝔢 _ 𝒹ℴ _) ; _) _ = nothing
  ssEvalwithFuel zero ((𝔦𝔣 _ 𝔱𝔥𝔢𝔫 _ 𝔢𝔩𝔰𝔢 _) ; _) _ = nothing
  ssEvalwithFuel zero ((_ := _) ; _) _ = nothing
  ssEvalwithFuel zero ( 𝑠𝑘𝑖𝑝 ; b ) s = ssEvalwithFuel zero b s
  -----------------------------------------------------------------
  -- SINGLE WHILE 
  ssEvalwithFuel (suc n) ( 𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c ;) s with evalExp exp s
  ... | nothing = nothing -- Computation failed i.e. div by 0
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | true  = ssEvalwithFuel n ( c 𝔱𝔥𝔢𝔫 𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c ;) s
  ... | false = just s
  -----------------------------------------------------------------
  -- SINGLE IF THEN ELSE
  ssEvalwithFuel (suc n) ( 𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂  ;) s
      with evalExp exp s
  ... | nothing = nothing -- Computation failed i.e. div by 0
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | true = ssEvalwithFuel n c₁ s
  ... | false = ssEvalwithFuel n c₂ s
  -----------------------------------------------------------------
  -- SINGLE ASSI
  ssEvalwithFuel (suc n) ( id := exp ;) s = 
    map (λ v → updateState id v s) (evalExp exp s)
  -----------------------------------------------------------------
  -- SINGLE SKIP
  ssEvalwithFuel (suc n) (𝑠𝑘𝑖𝑝 ; c) s = ssEvalwithFuel (suc n) c s
  -----------------------------------------------------------------
  -- WHILE ; THEN C₂
  ssEvalwithFuel (suc n) ((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c₁) ; c₂) s
      with evalExp exp s
  ... | nothing = nothing -- Computation failed i.e. div by 0
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | true = ssEvalwithFuel n (c₁ 𝔱𝔥𝔢𝔫 ((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c₁) ; c₂)) s
  ... | false = ssEvalwithFuel n c₂ s
  -----------------------------------------------------------------
  --- IF THEN ELSE ; THEN C₂
  ssEvalwithFuel (suc n) ((𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ; c₃) s
      with evalExp exp s
  ... | nothing = nothing -- Computation failed i.e. div by 0
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | true = ssEvalwithFuel n (c₁ 𝔱𝔥𝔢𝔫 c₃) s 
  ... | false = ssEvalwithFuel n (c₂ 𝔱𝔥𝔢𝔫 c₃) s
  -----------------------------------------------------------------
  --- ASSI ; THEN C
  ssEvalwithFuel (suc n) ((id := exp) ; c) s with evalExp exp s
  ... | nothing = nothing -- Computation failed i.e. div by 0
  ... | (just v) = ssEvalwithFuel n c (updateState id v s)
  -----------------------------------------------------------------
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  𝑠𝑘𝑖𝑝Elimₗ : ∀ n b s
    → ssEvalwithFuel n ((𝑠𝑘𝑖𝑝 ;) 𝔱𝔥𝔢𝔫 b) s ≡ ssEvalwithFuel n b s
  𝑠𝑘𝑖𝑝Elimₗ zero _ _ = refl
  𝑠𝑘𝑖𝑝Elimₗ (suc _) _ _ = refl
  -----------------------------------------------------------------  

  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  𝑠𝑘𝑖𝑝Elimᵣ : ∀ n b s
    → ssEvalwithFuel n (b 𝔱𝔥𝔢𝔫 𝑠𝑘𝑖𝑝 ; ) s ≡ ssEvalwithFuel n b s
  𝑠𝑘𝑖𝑝Elimᵣ zero (𝑠𝑘𝑖𝑝 ;) _ = refl
  𝑠𝑘𝑖𝑝Elimᵣ zero ((𝔴𝔥𝔦𝔩𝔢 _ 𝒹ℴ _) ;) _ = refl
  𝑠𝑘𝑖𝑝Elimᵣ zero ((𝔦𝔣 _ 𝔱𝔥𝔢𝔫 _ 𝔢𝔩𝔰𝔢 _) ;) s = refl
  𝑠𝑘𝑖𝑝Elimᵣ zero ((_ := _) ;) _ = refl
  𝑠𝑘𝑖𝑝Elimᵣ zero (𝑠𝑘𝑖𝑝 ; c) s = 𝑠𝑘𝑖𝑝Elimᵣ zero c s
  𝑠𝑘𝑖𝑝Elimᵣ zero ((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c₁) ; _) s
    = 𝑠𝑘𝑖𝑝Elimᵣ zero ((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c₁) ;) s
  𝑠𝑘𝑖𝑝Elimᵣ zero ((𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ; c₃) s
    = 𝑠𝑘𝑖𝑝Elimᵣ zero ((𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ;) s
  𝑠𝑘𝑖𝑝Elimᵣ zero ((id := exp) ; c) s
    = 𝑠𝑘𝑖𝑝Elimᵣ zero ((id := exp) ;) s
  𝑠𝑘𝑖𝑝Elimᵣ (suc n) (𝑠𝑘𝑖𝑝 ;) _ = refl
  𝑠𝑘𝑖𝑝Elimᵣ (suc n) ((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c) ;) s
    with evalExp exp s
  ... | nothing = refl
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | true
       rewrite 𝔱𝔥𝔢𝔫-comm c ((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c) ;) (𝑠𝑘𝑖𝑝 ;)
       = 𝑠𝑘𝑖𝑝Elimᵣ n (c 𝔱𝔥𝔢𝔫 ((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c) ;)) s 
  ... | false with n
  ... | zero  = refl
  ... | suc _ = refl
  𝑠𝑘𝑖𝑝Elimᵣ (suc n) ((𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ;) s
    with evalExp exp s
  ... | nothing = refl
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | true  = 𝑠𝑘𝑖𝑝Elimᵣ n c₁ s
  ... | false = 𝑠𝑘𝑖𝑝Elimᵣ n c₂ s
  𝑠𝑘𝑖𝑝Elimᵣ (suc n) ((id := exp) ;) s
    with evalExp exp s | n
  ... | nothing  | _ = refl
  ... | just v | zero  = refl
  ... | just v | suc _ = refl
  𝑠𝑘𝑖𝑝Elimᵣ (suc n) (𝑠𝑘𝑖𝑝 ; c) s = 𝑠𝑘𝑖𝑝Elimᵣ (suc n) c s
  𝑠𝑘𝑖𝑝Elimᵣ (suc n) ((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c₁) ; c₂) s
    with evalExp exp s
  ... | nothing = refl
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | true
     rewrite  
       𝔱𝔥𝔢𝔫-comm c₁ (𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c₁ ;) (c₂ 𝔱𝔥𝔢𝔫 (𝑠𝑘𝑖𝑝 ;))
     | 𝔱𝔥𝔢𝔫-comm (c₁ 𝔱𝔥𝔢𝔫 (𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c₁ ;)) c₂ (𝑠𝑘𝑖𝑝 ;)
     | 𝔱𝔥𝔢𝔫-comm  c₁ (𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c₁ ;) c₂
     =  𝑠𝑘𝑖𝑝Elimᵣ n ((c₁ 𝔱𝔥𝔢𝔫 ((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c₁) ;)) 𝔱𝔥𝔢𝔫 c₂) s
  ... | false = 𝑠𝑘𝑖𝑝Elimᵣ n c₂ s 
  𝑠𝑘𝑖𝑝Elimᵣ (suc n) ((𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ; c₃) s
    with evalExp exp s
  ... | nothing = refl
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | true
     rewrite
       𝔱𝔥𝔢𝔫-comm c₁ c₃ (𝑠𝑘𝑖𝑝 ;)
       = 𝑠𝑘𝑖𝑝Elimᵣ n (c₁ 𝔱𝔥𝔢𝔫 c₃) s
  ... | false
     rewrite
       𝔱𝔥𝔢𝔫-comm c₂ c₃ (𝑠𝑘𝑖𝑝 ;)
       = 𝑠𝑘𝑖𝑝Elimᵣ n (c₂ 𝔱𝔥𝔢𝔫 c₃) s
  𝑠𝑘𝑖𝑝Elimᵣ (suc n) ((id := exp) ; c) s
    with evalExp exp s
  ... | nothing = refl
  ... | (just v) = 𝑠𝑘𝑖𝑝Elimᵣ n c (updateState id v s)
  -----------------------------------------------------------------

