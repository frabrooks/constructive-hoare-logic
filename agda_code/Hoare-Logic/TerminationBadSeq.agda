{-# OPTIONS --allow-unsolved-metas #-}

-- Lib imports
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; inspect ; [_] ; cong ; subst )
open import Data.Maybe using ( Maybe ; just ; nothing ; _>>=_ ; Is-just ; to-witness ; map ; maybe )
open import Data.Maybe.Relation.Unary.Any using (Any)
open import Data.Product using (Σ ; Σ-syntax ; _×_  ; _,_  ; proj₁ ; proj₂ )
open import Data.Nat using (ℕ ; suc ; zero ; _≤_  ) renaming (_+_ to _+ᴺ_ )
open import Data.Bool using ( true ; false )
open import Data.Unit using ( ⊤ ; tt )
open import Relation.Unary using (Pred)
open import Data.Empty
open import Function using ( _∘_  ; _∋_ )
open import Function.Equivalence hiding (sym ; _∘_ ; map )


-- Project imports
open import Representation.Data using (Data-Implementation )
open import Representation.State using (S-Representation)
open import Misc


module Hoare-Logic.Termination (𝔡 : Data-Implementation  )
  (sRep : S-Representation 𝔡 ) where

  open Data-Implementation 𝔡
  open S-Representation sRep

  open import Mini-C.Expressions 𝔡 sRep
  open import Mini-C.Lang 𝔡 sRep
  open import Mini-C.Evaluation 𝔡 sRep


  -- Proof of termination
  Terminates : C → S → Set
  Terminates c s = Σ[ n ∈ ℕ ] ( Is-just (ssEvalwithFuel n c s ))

  -- Alternative condensed syntax
  ⌊ᵗ_⸴_ᵗ⌋ : C → S → Set
  ⌊ᵗ_⸴_ᵗ⌋ = Terminates

  skipTerminates : ∀ s → Terminates (𝑠𝑘𝑖𝑝 ;) s
  skipTerminates s = 2 , Any.just tt  


  assiProg-WFF[Exp]-Terminates : ∀ i exp s
    → Is-just (evalExp exp s)
    → Terminates ( i := exp ; ) s
  assiProg-WFF[Exp]-Terminates i e s p
   = 1 , (is-JustExp→is-JustAssi {i}{e} p)

  Result : ∀ {C s} → ⌊ᵗ C ⸴ s ᵗ⌋ → S
  Result = to-witness ∘ proj₂

  -- Alternative condensed syntax
  ‵ : ∀ {C s} → ⌊ᵗ C ⸴ s ᵗ⌋ → S
  ‵ = Result

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

  {-
  -- Not used
  lemm-π : ∀ n b s → ssEvalwithFuel n (𝑠𝑘𝑖𝑝 ; b) s ≡ ssEvalwithFuel n b s
  lemm-π zero b s = refl
  lemm-π (suc n) b s = refl

  -- Not used
  lemm-ψ : ∀ ↪s₁ ↪s₂ c → c 𝔱𝔥𝔢𝔫 ↪s₁ ; (↪s₂ ;) ≡ c 𝔱𝔥𝔢𝔫 ↪s₁ ; 𝔱𝔥𝔢𝔫 ↪s₂ ;
  lemm-ψ ↪s₁ ↪s₂ (↪s ;) = refl
  lemm-ψ ↪s₁ ↪s₂ (↪s ; c) rewrite ψ ↪s₁ ↪s₂ c = refl

  -- Not used
  lemm-φ : ∀ ↪s c₁ c₂ → ↪s ; c₁ 𝔱𝔥𝔢𝔫 c₂ ≡ ↪s ; (c₁ 𝔱𝔥𝔢𝔫 c₂)
  lemm-φ ↪s c₁ c₂ = refl

  -- Not used
  lemm-ι : ∀ ↪s c → ↪s ; c ≡ (↪s ;) 𝔱𝔥𝔢𝔫 c
  lemm-ι ↪s c = refl
  -}

  𝑠𝑘𝑖𝑝Elimₗ : ∀ n b s
    → ssEvalwithFuel n ((𝑠𝑘𝑖𝑝 ;) 𝔱𝔥𝔢𝔫 b) s ≡ ssEvalwithFuel n b s
  𝑠𝑘𝑖𝑝Elimₗ zero _ _ = refl
  𝑠𝑘𝑖𝑝Elimₗ (suc _) _ _ = refl

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



{-
  EvaluationIsDeterministic : ∀ {s} (C : C) (fuel₁ fuel₂ : ℕ)
                              → (a b : ⌊ᵗ C ⸴ s ᵗ⌋ )
                              → proj₁ a ≡ fuel₁
                              → proj₁ b ≡ fuel₂
                              → Result a ≡ Result b                              
  EvaluationIsDeterministic {s} 𝑠𝑘𝑖𝑝 zero zero (zero , ij₁) (zero , ij₂) _ _ 
    rewrite uniqueIJ (just s) ij₁ ij₂ = refl
  EvaluationIsDeterministic {s} 𝑠𝑘𝑖𝑝 zero (suc fuel₂) (zero , ij₁) (.(suc fuel₂) , ij₂) _ refl 
    rewrite uniqueIJ (just s) ij₁ ij₂ = refl
  EvaluationIsDeterministic {s} 𝑠𝑘𝑖𝑝 (suc fuel₁) zero (.(suc fuel₁) , ij₁) (zero , ij₂) refl _ 
    rewrite uniqueIJ (just s) ij₁ ij₂ = refl  
  EvaluationIsDeterministic {s} 𝑠𝑘𝑖𝑝 (suc fuel₁) (suc fuel₂) (.(suc fuel₁) , ij₁) (.(suc fuel₂) , ij₂) refl refl
    rewrite uniqueIJ (just s) ij₁ ij₂ = refl

  EvaluationIsDeterministic {s} (𝑎𝑠𝑠𝑖꞉ (id ꞉= exp)) _ _ (suc _ , ij₁) (suc _ , ij₂) _ _ 
    rewrite uniqueIJ (map (λ v → updateState id v s) (evalExp exp s)) ij₁ ij₂ = refl
    
  EvaluationIsDeterministic {s} (𝑠𝑒𝑞꞉ (𝑠𝑒𝑞꞉ (_ ﹔ _) ﹔ _)) (suc fuel₁) (suc fuel₂) (.(suc fuel₁) , ij₁) (.(suc fuel₂) , ij₂) refl refl
    = EvaluationIsDeterministic _ fuel₁ fuel₂ (fuel₁ , ij₁) (fuel₂ , ij₂) refl refl
  
  EvaluationIsDeterministic {s} (𝑠𝑒𝑞꞉ (𝑐𝑡𝑟𝑙꞉ (𝑖𝑓 exp 𝑡ℎ𝑒𝑛 _ 𝑒𝑙𝑠𝑒 _) ﹔ _)) (suc fuel₁) (suc fuel₂) (.(suc fuel₁) , ij₁) (.(suc fuel₂) , ij₂) refl refl
    with evalExp exp s
  ... | cond@(just _) with toTruthValue {cond} (Any.just tt)
  ... | false = EvaluationIsDeterministic _ fuel₁ fuel₂ (fuel₁ , ij₁) (fuel₂ , ij₂) refl refl
  ... | true  = EvaluationIsDeterministic _ fuel₁ fuel₂ (fuel₁ , ij₁) (fuel₂ , ij₂) refl refl
  
  EvaluationIsDeterministic {s} (𝑠𝑒𝑞꞉ (𝑙𝑜𝑜𝑝꞉ (𝑤ℎ𝑖𝑙𝑒 exp 𝑑𝑜 _) ﹔ _)) (suc fuel₁) (suc fuel₂) (.(suc fuel₁) , ij₁) (.(suc fuel₂) , ij₂) refl refl
    with evalExp exp s
  ... | cond@(just _) with toTruthValue {cond} (Any.just tt)
  ... | false = EvaluationIsDeterministic _ fuel₁ fuel₂ (fuel₁ , ij₁) (fuel₂ , ij₂) refl refl
  ... | true  = EvaluationIsDeterministic _ fuel₁ fuel₂ (fuel₁ , ij₁) (fuel₂ , ij₂) refl refl
  
  EvaluationIsDeterministic {s} (𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ c@(𝑠𝑒𝑞꞉ _))) (suc fuel₁) (suc fuel₂) (.(suc fuel₁) , ij₁) (.(suc fuel₂) , ij₂) refl refl
    = EvaluationIsDeterministic {s} c (suc fuel₁) (suc fuel₂) ((suc fuel₁) , ij₁) ((suc fuel₂) , ij₂) refl refl
  EvaluationIsDeterministic {s} (𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ c@(𝑎𝑠𝑠𝑖꞉ (_ ꞉= _)))) (suc fuel₁) (suc fuel₂) (.(suc fuel₁) , ij₁) (.(suc fuel₂) , ij₂) refl refl
    = EvaluationIsDeterministic {s} (c) 1 1  ( 1 , ij₁) ( 1  , ij₂) refl refl
    
  EvaluationIsDeterministic {s} (𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ 𝑐𝑡𝑟𝑙꞉ (𝑖𝑓 exp 𝑡ℎ𝑒𝑛 _ 𝑒𝑙𝑠𝑒 _))) (suc fuel₁) (suc fuel₂) (.(suc fuel₁) , ij₁) (.(suc fuel₂) , ij₂) refl refl
    with evalExp exp s
  ... | cond@(just _) with toTruthValue {cond} (Any.just tt)
  ... | false = EvaluationIsDeterministic _ fuel₁ fuel₂ (fuel₁ , ij₁) (fuel₂ , ij₂) refl refl
  ... | true  = EvaluationIsDeterministic _ fuel₁ fuel₂ (fuel₁ , ij₁) (fuel₂ , ij₂) refl refl
  EvaluationIsDeterministic {s} (𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ 𝑙𝑜𝑜𝑝꞉ (𝑤ℎ𝑖𝑙𝑒 exp 𝑑𝑜 _))) (suc fuel₁) (suc fuel₂) (.(suc fuel₁) , ij₁) (.(suc fuel₂) , ij₂) refl refl
    with evalExp exp s
  ... | cond@(just _) with toTruthValue {cond} (Any.just tt)
  ... | false = EvaluationIsDeterministic _ fuel₁ fuel₂ (fuel₁ , ij₁) (fuel₂ , ij₂) refl refl
  ... | true  = EvaluationIsDeterministic _ fuel₁ fuel₂ (fuel₁ , ij₁) (fuel₂ , ij₂) refl refl

  EvaluationIsDeterministic {s} (𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ 𝑠𝑘𝑖𝑝)) (suc fuel₁) (suc fuel₂) (.(suc fuel₁) , ij₁) (.(suc fuel₂) , ij₂) refl refl
    rewrite uniqueIJ (just s) ij₁ ij₂ = refl
    
  EvaluationIsDeterministic {s} (𝑐𝑡𝑟𝑙꞉ (𝑖𝑓 exp 𝑡ℎ𝑒𝑛 _ 𝑒𝑙𝑠𝑒 _)) (suc fuel₁) (suc fuel₂) (.(suc fuel₁) , ij₁) (.(suc fuel₂) , ij₂) refl refl
    with evalExp exp s
  ... | cond@(just _) with toTruthValue {cond} (Any.just tt)
  ... | false = EvaluationIsDeterministic _ fuel₁ fuel₂ (fuel₁ , ij₁) (fuel₂ , ij₂) refl refl
  ... | true  = EvaluationIsDeterministic _ fuel₁ fuel₂ (fuel₁ , ij₁) (fuel₂ , ij₂) refl refl

  EvaluationIsDeterministic {s} 𝑙@(𝑙𝑜𝑜𝑝꞉ (𝑤ℎ𝑖𝑙𝑒 exp 𝑑𝑜 _)) (suc fuel₁) (suc fuel₂) (.(suc fuel₁) , ij₁) (.(suc fuel₂) , ij₂) refl refl
    with evalExp exp s
  ... | cond@(just _) with toTruthValue {cond} (Any.just tt)
  ... | false = EvaluationIsDeterministic _ fuel₁ fuel₂ (fuel₁ , ij₁) (fuel₂ , ij₂) refl refl
  ... | true  = EvaluationIsDeterministic _ fuel₁ fuel₂ (fuel₁ , ij₁) (fuel₂ , ij₂) refl refl

  EvaluationIsDeterministic {s} (𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ x ﹔ c₂)) (suc fuel₁) (suc fuel₂) (.(suc fuel₁) , ij₁) (.(suc fuel₂) , ij₂) refl refl
    with evalAssi s x 
  ... | just _ = EvaluationIsDeterministic  _ fuel₁ fuel₂ (fuel₁ , ij₁) (fuel₂ , ij₂) refl refl
  ... | nothing = ⊥-elim (Ij⊥ (subst Is-just (δ fuel₁ c₂) ij₁)) 
    where
    δ : ∀ n c → ssEvalwithFuel n (c , nothing) ≡ nothing
    δ zero (𝑎𝑠𝑠𝑖꞉ (_ ꞉= _)) = refl
    δ (suc n) (𝑎𝑠𝑠𝑖꞉ (_ ꞉= _)) = refl
    δ zero (𝑠𝑒𝑞꞉ x) = refl
    δ (suc n) (𝑠𝑒𝑞꞉ (_ ﹔ _)) = refl
    δ zero (𝑐𝑡𝑟𝑙꞉ (𝑖𝑓 _ 𝑡ℎ𝑒𝑛 _ 𝑒𝑙𝑠𝑒 _)) = refl
    δ (suc n) (𝑐𝑡𝑟𝑙꞉ (𝑖𝑓 _ 𝑡ℎ𝑒𝑛 _ 𝑒𝑙𝑠𝑒 _)) = refl
    δ zero (𝑙𝑜𝑜𝑝꞉ (𝑤ℎ𝑖𝑙𝑒 _ 𝑑𝑜 _)) = refl
    δ (suc n) (𝑙𝑜𝑜𝑝꞉ (𝑤ℎ𝑖𝑙𝑒 _ 𝑑𝑜 _)) = refl
    δ zero 𝑠𝑘𝑖𝑝 = refl
    δ (suc n) 𝑠𝑘𝑖𝑝 = refl
-}    

  {-
  Alt proof

  assiProgW/ValidExpTerminates'' : ∀ i exp s → ( a : i := exp ) → Is-just (evalExp exp s) → Terminates ( 𝑎𝑠𝑠𝑖꞉ a ) s
  assiProgW/ValidExpTerminates'' i e s (.i ꞉= .e) p = 1 , (lem i e s (i ꞉= e) p)
    where
    lem : ∀ i exp s → ( a : i := exp ) → Is-just (evalExp exp s) → Is-just ((Data.Maybe.map (λ v → updateState i v s) (evalExp exp s)))
    lem i e s (.i ꞉= .e) p with (evalExp e s)
    ... | just x = Any.just tt
  -}
  

  {-
  assiProgW/ValidExpTerminates' : ∀ i exp s → ( a : i := exp ) → Is-just (evalExp exp s) → Terminates ( 𝑎𝑠𝑠𝑖꞉ a ) s
  assiProgW/ValidExpTerminates' i e s (.i ꞉= .e) p with (evalExp e s)
  ... | just x = 1 , {!!}


  assiProgW/ValidExpTerminates'' : ∀ i exp s → ( a : i := exp ) → Is-just (evalExp exp s) → Terminates' ( 𝑎𝑠𝑠𝑖꞉ a ) s
  assiProgW/ValidExpTerminates'' i e s (.i ꞉= .e) p with (evalExp e s) | (ssEvalwithFuel 1 (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) , just s))
  ... | just x | fst , snd = t 1 {!!}
  -}


{-


  assiProgW/ValidExpTerminates' : ∀ i exp s → ( a : i := exp ) → Is-just (evalExp exp s) → Terminates ( 𝑎𝑠𝑠𝑖꞉ a ) s
  assiProgW/ValidExpTerminates' i e s (.i ꞉= .e) p  with (evalExp e s)
  ... | just x = 1 , {!!}

  data 𝟚 : Set where
    l : 𝟚
    r : 𝟚

  ssplitl : Maybe Val
  ssplitl = getVarVal 𝔁 ●

  ssplitr : Maybe Val
  ssplitr = getVarVal 𝔁 (updateState 𝔁 ➋ ●)

  split : 𝟚 → Maybe Val
  split a with a
  ... | l = (ssplitl)
  ... | r = (ssplitr)

  bar : ℕ → Maybe Val → Maybe Val
  bar zero _ = nothing
  bar (suc _) a = a

  wraps : Maybe Val → Maybe S
  wraps m = Data.Maybe.map (λ v → updateState 𝔁 v ● ) m


  nonProduct : ℕ → 𝟚 → Set
  nonProduct n a =  Is-just ( wraps ( bar n (split a)))

  

  usingProduct :  𝟚 → Set
  usingProduct a = Σ[ n ∈ ℕ ]  ( Is-just ( wraps (bar n (split a)) ))

  worksFine : ∀ {n} (a : 𝟚) → (n ≡ zero → ⊥) → Is-just (split a) → nonProduct n a
  worksFine {zero} a p q = ⊥-elim (p refl)
  worksFine {suc n} a p q with (split a)
  worksFine {suc n} a p q | just x = Any.just tt
  
  problem : ∀  (a : 𝟚) → Is-just (split a) → usingProduct a
  problem a p with (split a)
  ... | just x = 1 , Any.just tt

  -}


