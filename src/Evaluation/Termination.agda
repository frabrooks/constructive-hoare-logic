{-# OPTIONS --allow-unsolved-metas #-}

-- Lib imports
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; inspect ; [_] ; cong ; subst )
open import Data.Maybe using ( Maybe ; just ; nothing ; _>>=_ ; Is-just ; to-witness ; map ; maybe )
open import Data.Maybe.Relation.Unary.Any using (Any)
open import Data.Product using (Σ ; Σ-syntax ; _×_  ; _,_  ; proj₁ ; proj₂ )
open import Data.Nat using (ℕ ; suc ; zero ; _≤″_  ) renaming (_+_ to _+ᴺ_ ; less-than-or-equal to ≤with )
open _≤″_
open import Data.Nat.Properties using ( +-comm ; +-identityʳ )

open import Data.Bool using ( true ; false )
open import Data.Unit using ( ⊤ ; tt )
open import Relation.Unary using (Pred)
open import Data.Empty
open import Function using ( _∘_  ; _∋_ ; id )
open import Function.Equivalence hiding (sym ; _∘_ ; map ; id )
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

-- Project imports
open import Data-Interface using (Data-Implementation )
open import State-Interface using (State-Implementation)
open import Misc


module Evaluation.Termination (𝔡 : Data-Implementation  )
  (𝔖 : State-Implementation 𝔡 ) where

  open Data-Implementation 𝔡
  open State-Implementation 𝔖

  open import Language.Expressions 𝔡 𝔖
  open import Language.Mini-Imp 𝔡 𝔖
  open import Evaluation.Evaluation 𝔡 𝔖


  -- Proof of termination
  Terminates : C → S → Set
  Terminates c s = Σ[ ℱ ∈ ℕ ] ( Is-just (ssEvalwithFuel ℱ c s ))

  -- Alternative condensed syntax
  ⌊ᵗ_⸴_ᵗ⌋ : C → S → Set
  ⌊ᵗ_⸴_ᵗ⌋ = Terminates

  assiProg-WFF[Exp]-Terminates : ∀ i exp s
    → Is-just (evalExp exp s)
    → Terminates ( i := exp ; ) s
  assiProg-WFF[Exp]-Terminates i e s p
   = 1 , (is-JustExp→is-JustAssi {i}{e} p)

  -- Get Result of Evaluation
  Result : ∀ {c s} → ⌊ᵗ c ⸴ s ᵗ⌋ → S
  Result = to-witness ∘ proj₂
  
  -- Alternative condensed syntax
  ‵ : ∀ {c s} → ⌊ᵗ c ⸴ s ᵗ⌋ → S
  ‵ = Result

  -- Alternative definition indexed by fuel
  ⌊ᵗ_⸴_⸴_ᵗ⌋ : ℕ → C → S → Set
  ⌊ᵗ ℱ ⸴ c ⸴ s ᵗ⌋ = Is-just (ssEvalwithFuel ℱ c s)

  -- Get Result of Evaluation
  Result″ = to-witness
  
  -- Alternative condensed syntax
  ″ = to-witness


  -- Simple lemmas

  -- 𝑠𝑘𝑖𝑝 terminates with any amount of fuel
  ⌊ᵗ𝑠𝑘𝑖𝑝ᵗ⌋ : ∀ {s} n → ⌊ᵗ n ⸴ 𝑠𝑘𝑖𝑝 ; ⸴ s ᵗ⌋ 
  ⌊ᵗ𝑠𝑘𝑖𝑝ᵗ⌋ {s} zero    = Any.just tt
  ⌊ᵗ𝑠𝑘𝑖𝑝ᵗ⌋ {s} (suc ℱ) = Any.just tt


  uniqueIJ : ∀ (x : Maybe S) → ( a b : Is-just x) → a ≡ b
  uniqueIJ .(just _) (Any.just x) (Any.just x₁) = refl

  EvaluationIsDeterministic : ∀ {s} {fuel₁ fuel₂} (C : C) 
    → (a b : ⌊ᵗ C ⸴ s ᵗ⌋ ) → proj₁ a ≡ fuel₁ → proj₁ b ≡ fuel₂ → Result a ≡ Result b
  EvaluationIsDeterministic {s} (↪s ;) (0 , ij₁) (0 , ij₂) _ _
    rewrite uniqueIJ (ssEvalwithFuel 0 (↪s ;) s) ij₁ ij₂ = refl
  EvaluationIsDeterministic {s} (𝑠𝑘𝑖𝑝 ;) (0 , ij₁) ((suc f₂) , ij₂) _ _
    rewrite uniqueIJ (just s) ij₁ ij₂ = refl
  EvaluationIsDeterministic {s} (𝑠𝑘𝑖𝑝 ;) ((suc f₁) , ij₁) (0 , ij₂) _ _ 
    rewrite uniqueIJ (just s) ij₁ ij₂ = refl
  EvaluationIsDeterministic {s} (𝑠𝑘𝑖𝑝 ;) ((suc f₁) , ij₁) ((suc f₂) , ij₂) _ _ 
    rewrite uniqueIJ (just s) ij₁ ij₂ = refl
  EvaluationIsDeterministic {s} ((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c) ;) ((suc f₁) , ij₁) ((suc f₂) , ij₂) refl refl
    with evalExp exp s
  ... | cond@(just _) with toTruthValue {cond} (Any.just tt)
  ... | false rewrite uniqueIJ (just s) ij₁ ij₂ = refl
  ... | true  = EvaluationIsDeterministic _ (f₁ , ij₁) (f₂ , ij₂) refl refl
  EvaluationIsDeterministic {s} ((𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ;) ((suc f₁) , ij₁) ((suc f₂) , ij₂) refl refl
    with evalExp exp s
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | true = EvaluationIsDeterministic _ (f₁ , ij₁) (f₂ , ij₂) refl refl
  ... | false = EvaluationIsDeterministic _ (f₁ , ij₁) (f₂ , ij₂) refl refl
  EvaluationIsDeterministic {s} ((id := exp) ;) ((suc f₁) , ij₁) ((suc f₂) , ij₂) refl refl
    with evalExp exp s
  ... | (just v) rewrite uniqueIJ (just (updateState id v s)) ij₁ ij₂ = refl
  EvaluationIsDeterministic {s} (𝑠𝑘𝑖𝑝 ; c) (0 , ij₁) (0 , ij₂) refl refl
    rewrite uniqueIJ (ssEvalwithFuel zero c s) ij₁ ij₂ = refl
  EvaluationIsDeterministic {s} (𝑠𝑘𝑖𝑝 ; (𝑠𝑘𝑖𝑝 ;)) (0 , ij₁) ((suc f₂) , ij₂) refl refl
    rewrite uniqueIJ (just s) ij₁ ij₂ = refl
  EvaluationIsDeterministic {s} (𝑠𝑘𝑖𝑝 ; (𝑠𝑘𝑖𝑝 ; c)) (0 , ij₁) ((suc f₂) , ij₂) refl refl
    = EvaluationIsDeterministic c ( zero  , ij₁ ) ((suc f₂) , ij₂) refl refl
  EvaluationIsDeterministic {s} (𝑠𝑘𝑖𝑝 ; c) ((suc f₁) , ij₁) (0 , ij₂) refl refl
    = EvaluationIsDeterministic c ((suc f₁) , ij₁) (zero , ij₂) refl refl
  EvaluationIsDeterministic {s} (𝑠𝑘𝑖𝑝 ; (↪s ;)) ((suc f₁) , ij₁) ((suc f₂) , ij₂) refl refl
      = EvaluationIsDeterministic (↪s ;) ((suc f₁) , ij₁) ((suc f₂) , ij₂) refl refl
  EvaluationIsDeterministic {s} (𝑠𝑘𝑖𝑝 ; (↪s ; c)) ((suc f₁) , ij₁) ((suc f₂) , ij₂) refl refl
    = EvaluationIsDeterministic (↪s ; c) ((suc f₁) , ij₁) ((suc f₂) , ij₂) refl refl
  EvaluationIsDeterministic {s} ((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c₁) ; c₂) ((suc f₁) , ij₁) ((suc f₂) , ij₂) refl refl
    with evalExp exp s
  ... | cond@(just _) with toTruthValue {cond} (Any.just tt)
  ... | false = EvaluationIsDeterministic _ (f₁ , ij₁) (f₂ , ij₂) refl refl
  ... | true  = EvaluationIsDeterministic _ (f₁ , ij₁) (f₂ , ij₂) refl refl
  EvaluationIsDeterministic {s} ((𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ; c₃) ((suc f₁) , ij₁) ((suc f₂) , ij₂) refl refl
    with evalExp exp s
  ... | cond@(just _) with toTruthValue {cond} (Any.just tt)
  ... | false = EvaluationIsDeterministic _ (f₁ , ij₁) (f₂ , ij₂) refl refl
  ... | true  = EvaluationIsDeterministic _ (f₁ , ij₁) (f₂ , ij₂) refl refl
  EvaluationIsDeterministic {s} ((id := exp) ; c) ((suc f₁) , ij₁) ((suc f₂) , ij₂) refl refl
    with evalExp exp s
  ... | (just v) = EvaluationIsDeterministic _ (f₁ , ij₁) (f₂ , ij₂) refl refl 

  ij0⇒ijn : ∀ {c} {s} n
    → Is-just (ssEvalwithFuel zero c s)
    → Is-just (ssEvalwithFuel n c s)
  ij0⇒ijn {𝑠𝑘𝑖𝑝 ;} {s} zero ij = Any.just tt
  ij0⇒ijn {𝑠𝑘𝑖𝑝 ;} {s} (suc n) ij = Any.just tt
  ij0⇒ijn {𝑠𝑘𝑖𝑝 ; c} {s} n ij rewrite
    𝑠𝑘𝑖𝑝Elimₗ zero c s | 𝑠𝑘𝑖𝑝Elimₗ n c s = ij0⇒ijn n ij

  ijn⇒ijsucn : ∀ {c} {s} n
    → Is-just (ssEvalwithFuel n c s)
    → Is-just (ssEvalwithFuel (suc n) c s)
  ijn⇒ijsucn {𝑠𝑘𝑖𝑝 ;} {s} zero ij = Any.just tt
  ijn⇒ijsucn {𝑠𝑘𝑖𝑝 ;} {s} (suc n) ij = Any.just tt
  ijn⇒ijsucn {(𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c) ;} {s} (suc n) ij
    with evalExp exp s
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | true = ijn⇒ijsucn n ij
  ... | false = Any.just tt
  ijn⇒ijsucn {(𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ;} {s} (suc n) ij
    with evalExp exp s
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | true = ijn⇒ijsucn n ij
  ... | false = ijn⇒ijsucn n ij
  ijn⇒ijsucn {(id := exp) ;} {s} (suc n) ij
    with evalExp exp s
  ... | (just _) = Any.just tt
  ijn⇒ijsucn {𝑠𝑘𝑖𝑝 ; c} {s} zero ij
    = ijn⇒ijsucn {c} zero ij
  ijn⇒ijsucn {𝑠𝑘𝑖𝑝 ; c} {s} (suc n) ij
      = ijn⇒ijsucn {c} (suc n) ij
  ijn⇒ijsucn {(𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c₁) ; c₂} {s} (suc n) ij
    with evalExp exp s
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | true = ijn⇒ijsucn n ij
  ... | false = ijn⇒ijsucn n ij
  ijn⇒ijsucn {(𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ; c₃} {s} (suc n) ij
    with evalExp exp s
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | true = ijn⇒ijsucn n ij
  ... | false = ijn⇒ijsucn n ij
  ijn⇒ijsucn {(id := exp) ; c} {s} (suc n) ij
   with evalExp exp s
  ... | (just _) = ijn⇒ijsucn n ij
 
  sucᵣ : ∀ x y → x +ᴺ suc y ≡ suc x +ᴺ y
  sucᵣ zero y = refl
  sucᵣ (suc x) y rewrite sucᵣ x y = refl

{-
+-identityˡ : LeftIdentity 0 _+_
+-identityˡ _ = refl

+-identityʳ : RightIdentity 0 _+_
+-identityʳ zero    = refl
+-identityʳ (suc n) = cong suc (+-identityʳ n)

+-identity : Identity 0 _+_
+-identity = +-identityˡ , +-identityʳ

-}


  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━  
  -- Adding fuel still terminates
  addFuel' : ∀ {C} {s} ℱ ℱ' → ⌊ᵗ ℱ ⸴ C ⸴ s ᵗ⌋ → ⌊ᵗ (ℱ +ᴺ ℱ') ⸴ C ⸴ s ᵗ⌋
  ----------------------------------------------------------------
  addFuel' {𝑠𝑘𝑖𝑝 ;}   {s} ℱ ℱ' t₁ = ⌊ᵗ𝑠𝑘𝑖𝑝ᵗ⌋ (ℱ +ᴺ ℱ')
  addFuel' {𝑠𝑘𝑖𝑝 ; C} {s} ℱ ℱ' t₁
           rewrite 𝑠𝑘𝑖𝑝Elimₗ (ℱ +ᴺ ℱ') C s | 𝑠𝑘𝑖𝑝Elimₗ ℱ C s
           = addFuel' {C} {s} ℱ ℱ' t₁
  ----------------------------------------------------------------           
  addFuel' {(𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c) ;} {s} (suc ℱ) ℱ' t₁
      with evalExp exp s
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | false = Any.just tt  
  ... | true  = addFuel' ℱ ℱ' t₁
  addFuel' {(𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c) ; C} {s} (suc ℱ) ℱ' t₁ 
      with evalExp exp s
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | false = addFuel' ℱ ℱ' t₁
  ... | true  = addFuel' ℱ ℱ' t₁
  ---------------e-------------------------------------------------
  addFuel' {(𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ;} {s} (suc ℱ) ℱ' t₁
      with evalExp exp s
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | false = addFuel' ℱ ℱ' t₁
  ... | true  = addFuel' ℱ ℱ' t₁
  addFuel' {(𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ; C} {s} (suc ℱ) ℱ' t₁
      with evalExp exp s
  ... | f@(just _) with toTruthValue {f} (Any.just tt)
  ... | false = addFuel' ℱ ℱ' t₁
  ... | true  = addFuel' ℱ ℱ' t₁  
  ----------------------------------------------------------------  
  addFuel' {(id := exp) ;} {s} (suc ℱ) ℱ' t₁ with evalExp exp s
  ... | f@(just _) = t₁
  addFuel' {(id := exp) ; C} {s} (suc ℱ) ℱ' t₁ with evalExp exp s
  ... | f@(just _) = addFuel' ℱ ℱ' t₁  



{-
  -- Adding fuel still terminates
  addFuel : ∀ {C} {s} fuel → ( t : ⌊ᵗ C ⸴ s ᵗ⌋ ) → Σ ⌊ᵗ C ⸴ s ᵗ⌋ (λ t' → proj₁ t' ≡ fuel +ᴺ (proj₁ t))
  addFuel {C} {s} zero t = ((zero +ᴺ (proj₁ t) ) , proj₂ t) , refl
  addFuel {𝑠𝑘𝑖𝑝 ;} {s} (suc fuel) (fuel₁ , snd) = ((suc (fuel +ᴺ fuel₁)) , Any.just tt) , refl
  addFuel {(𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c) ;} {s} (suc fuel) (suc fuel₁ , snd) = (((suc (fuel +ᴺ suc fuel₁))) , go ) , refl
    where
    go : Is-just (ssEvalwithFuel (suc (fuel +ᴺ suc fuel₁)) ((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c) ;) s )
    go with evalExp exp s
    go | f@(just _) with toTruthValue {f} (Any.just tt)
    go |  _ | true rewrite sucᵣ fuel fuel₁ with addFuel {c 𝔱𝔥𝔢𝔫 ((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c) ;)} {s} (fuel) (fuel₁ , snd)
    go |  _ | true | (.(fuel +ᴺ fuel₁) , ij) , refl = ijn⇒ijsucn (fuel +ᴺ fuel₁) ij
    go |  _ | false = Any.just tt
  addFuel {(𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ;} {s} (suc fuel) (suc fuel₁ , snd) = (((suc (fuel +ᴺ suc fuel₁))) , go ) , refl
    where
    go : Is-just (ssEvalwithFuel (suc (fuel +ᴺ suc fuel₁)) ((𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ;) s )
    go with evalExp exp s    
    go | f@(just _) with toTruthValue {f} (Any.just tt)
    go |  _ | true  rewrite sucᵣ fuel fuel₁ with addFuel {c₁} {s} (fuel) (fuel₁ , snd)
    go |  _ | true  | (.(fuel +ᴺ fuel₁) , ij) , refl = ijn⇒ijsucn (fuel +ᴺ fuel₁) ij
    go |  _ | false rewrite sucᵣ fuel fuel₁ with addFuel {c₂} {s} (fuel) (fuel₁ , snd)
    go |  _ | false | (.(fuel +ᴺ fuel₁) , ij) , refl = ijn⇒ijsucn (fuel +ᴺ fuel₁) ij
  addFuel {(_ := _) ;} {s} (suc fuel) (suc fuel₁ , snd) = (((suc (fuel +ᴺ suc fuel₁))) , snd), refl
  addFuel {𝑠𝑘𝑖𝑝 ; c} {s} (suc fuel) (zero , snd) = (suc (fuel +ᴺ zero) , go ) , refl
    where
    go : Is-just (ssEvalwithFuel (suc (fuel +ᴺ zero)) c s)
    go with addFuel {c} {s} (fuel) (zero , snd)
    ... | (.(fuel +ᴺ zero) , ij) , refl = ijn⇒ijsucn (fuel +ᴺ 0) ij
  addFuel {𝑠𝑘𝑖𝑝 ; c} {s} (suc fuel) (suc fuel₁ , snd) = (suc (fuel +ᴺ suc fuel₁) , go ) , refl
    where
    go : Is-just (ssEvalwithFuel (suc (fuel +ᴺ suc fuel₁)) c s)
    go with addFuel {c} {s} (fuel) (suc fuel₁ , snd)
    ... | (.(fuel +ᴺ suc fuel₁) , ij) , refl = ijn⇒ijsucn (fuel +ᴺ suc fuel₁)ij
  addFuel {(𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c₁) ; c₂} {s} (suc fuel) (suc fuel₁ , snd) = (((suc (fuel +ᴺ suc fuel₁))) , go ) , refl
    where
    go : Is-just (ssEvalwithFuel (suc (fuel +ᴺ suc fuel₁)) ((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c₁) ; c₂) s )
    go with evalExp exp s
    go | f@(just _) with toTruthValue {f} (Any.just tt)
    go |  _ | true  rewrite sucᵣ fuel fuel₁ with addFuel {c₁ 𝔱𝔥𝔢𝔫 ((𝔴𝔥𝔦𝔩𝔢 exp 𝒹ℴ c₁) ; 𝔱𝔥𝔢𝔫 c₂)} {s} (fuel) (fuel₁ , snd)
    go |  _ | true  | (.(fuel +ᴺ fuel₁) , ij) , refl = ijn⇒ijsucn (fuel +ᴺ fuel₁) ij
    go |  _ | false rewrite sucᵣ fuel fuel₁ with addFuel {c₂} {s} (fuel) (fuel₁ , snd)
    go |  _ | false | (.(fuel +ᴺ fuel₁) , ij) , refl = ijn⇒ijsucn (fuel +ᴺ fuel₁) ij
  addFuel {(𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ; c₃} {s} (suc fuel) (suc fuel₁ , snd) = (((suc (fuel +ᴺ suc fuel₁))) , go ) , refl
    where
    go : Is-just (ssEvalwithFuel (suc (fuel +ᴺ suc fuel₁)) ((𝔦𝔣 exp 𝔱𝔥𝔢𝔫 c₁ 𝔢𝔩𝔰𝔢 c₂) ; c₃) s )
    go with evalExp exp s    
    go | f@(just _) with toTruthValue {f} (Any.just tt)
    go |  _ | true  rewrite sucᵣ fuel fuel₁ with addFuel {c₁ 𝔱𝔥𝔢𝔫 c₃} {s} (fuel) (fuel₁ , snd)
    go |  _ | true  | (.(fuel +ᴺ fuel₁) , ij) , refl = ijn⇒ijsucn (fuel +ᴺ fuel₁) ij
    go |  _ | false rewrite sucᵣ fuel fuel₁ with addFuel {c₂ 𝔱𝔥𝔢𝔫 c₃} {s} (fuel) (fuel₁ , snd)
    go |  _ | false | (.(fuel +ᴺ fuel₁) , ij) , refl = ijn⇒ijsucn (fuel +ᴺ fuel₁) ij
  addFuel {(id := exp) ; c} {s} (suc fuel) (suc fuel₁ , snd) = (((suc (fuel +ᴺ suc fuel₁))) , go), refl
    where
    go : Is-just (ssEvalwithFuel (suc (fuel +ᴺ suc fuel₁)) ((id := exp) ; c) s)
    go with evalExp exp s
    ... | just v rewrite sucᵣ fuel fuel₁ with addFuel {c} fuel (fuel₁ , snd)
    ... | (.(fuel +ᴺ fuel₁) , ij) , refl = ijn⇒ijsucn (fuel +ᴺ fuel₁) ij
-}

  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  ⌊ᵗ⌋-split' : ∀ ℱ s Q₁ Q₂ → (t₁₂ : ⌊ᵗ ℱ ⸴ Q₁ 𝔱𝔥𝔢𝔫 Q₂ ⸴ s ᵗ⌋)
              → Σ ⌊ᵗ ℱ ⸴ Q₁ ⸴ s ᵗ⌋ (λ t₁
              → Σ ℕ (λ ℱ'
              → ℱ' ≤″ ℱ × Σ ⌊ᵗ ℱ' ⸴ Q₂ ⸴ ″ t₁ ᵗ⌋ (λ t₂
              → ″ t₂ ≡ ″ t₁₂ )))
              
  -----------------------------------------------------------------
  -- Base case: Q₁ = 𝑠𝑘𝑖𝑝 ;
  ⌊ᵗ⌋-split' ℱ@0 s (𝑠𝑘𝑖𝑝 ;) Q₂ t₁₂ =
          (Any.just tt) , ℱ , ≤with refl  , t₁₂ , refl
  ⌊ᵗ⌋-split' ℱ@(suc _) s (𝑠𝑘𝑖𝑝 ;) Q₂ t₁₂ =
          (Any.just tt) , ℱ , ≤with (+-comm ℱ 0) , t₁₂ , refl          
  -- Q₁ = 𝑠𝑘𝑖𝑝 : Q₁ '
  ⌊ᵗ⌋-split' ℱ@0       s (𝑠𝑘𝑖𝑝 ; Q₁') = ⌊ᵗ⌋-split' ℱ s Q₁'
  ⌊ᵗ⌋-split' ℱ@(suc _) s (𝑠𝑘𝑖𝑝 ; Q₁') = ⌊ᵗ⌋-split' ℱ s Q₁'
  
  -----------------------------------------------------------------
  -- Most interesting case: 𝔴𝔥𝔦𝔩𝔢 followed by blocks Q₁' 𝔱𝔥𝔢𝔫 Q₂
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
                           
  -----------------------------------------------------------------
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
  -----------------------------------------------------------------
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
  -----------------------------------------------------------------
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
  -----------------------------------------------------------------
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
  ----------------------------------------------------------------- 
  -- Q₁ = id := exp ;
  ⌊ᵗ⌋-split' (suc ℱ) s Q₁@( id := exp ;) Q₂ t₁₂ = go
    where
    go : Σ ⌊ᵗ suc ℱ ⸴ Q₁ ⸴ s ᵗ⌋ (λ t₁ → Σ ℕ (λ ℱ' → ℱ' ≤″ suc ℱ ×
         Σ ⌊ᵗ ℱ' ⸴ Q₂ ⸴ ″ t₁ ᵗ⌋ (λ t₂ → ″ t₂ ≡ ″ t₁₂ )))             
    go with evalExp exp s
    ... | f@(just _)
        = (Any.just tt) , ℱ , ≤with (+-comm ℱ 1) , t₁₂ , refl
  -----------------------------------------------------------------
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  -- Alternative definition with record as output
  
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
     
  -----------------------------------------------------------------     
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━




