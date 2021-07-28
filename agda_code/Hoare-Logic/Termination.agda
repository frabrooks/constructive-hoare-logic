
-- Lib imports
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; inspect ; [_] ; cong ; subst )
open import Data.Maybe using ( Maybe ; just ; nothing ; _>>=_ ; Is-just ; to-witness ; map ; maybe )
open import Data.Maybe.Relation.Unary.Any using (Any)
open import Data.Product using (Σ ; Σ-syntax ; _×_  ; _,_  ; proj₁ ; proj₂ )
open import Data.Nat using (ℕ ; suc ; zero ; _≤_ )
open import Data.Bool using ( true ; false )
open import Data.Unit using ( ⊤ ; tt )
open import Relation.Unary using (Pred)
open import Data.Empty
open import Function using ( _∘_ )

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
  Terminates : 𝐶 → S → Set
  Terminates c s = Σ[ n ∈ ℕ ] ( Is-just (ssEvalwithFuel n ( c , just s )))

  -- Alternative condensed syntax
  ⟦_⸴_⟧ : 𝐶 → S → Set
  ⟦_⸴_⟧ = Terminates

--  data Terminates' :  𝐶 → S → Set where
--    t : ∀ {c} {s} (n : ℕ) → Is-just (ssEvalwithFuel n ( c , just s ))) → Terminates' c s


  skipTerminates : ∀ s → Terminates 𝑠𝑘𝑖𝑝 s
  skipTerminates s = 2 , Any.just tt  

  Result : ∀ {C s} → ⟦ C ⸴ s ⟧ → S
  Result = to-witness ∘ proj₂

  -- Alternative condensed syntax
  ‵ : ∀ {C s} → ⟦ C ⸴ s ⟧ → S
  ‵ = Result

  uniqueIJ : ∀ (x : Maybe S) → ( a b : Is-just x) → a ≡ b
  uniqueIJ .(just _) (Any.just x) (Any.just x₁) = refl

  EvaluationIsDeterministic : ∀ {s} (C : 𝐶) (fuel₁ fuel₂ : ℕ)
                              → (a b : ⟦ C ⸴ s ⟧)
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
    

  {-
  Alt proof

  assiProgW/ValidExpTerminates'' : ∀ i exp s → ( a : i := exp ) → Is-just (evalExp exp s) → Terminates ( 𝑎𝑠𝑠𝑖꞉ a ) s
  assiProgW/ValidExpTerminates'' i e s (.i ꞉= .e) p = 1 , (lem i e s (i ꞉= e) p)
    where
    lem : ∀ i exp s → ( a : i := exp ) → Is-just (evalExp exp s) → Is-just ((Data.Maybe.map (λ v → updateState i v s) (evalExp exp s)))
    lem i e s (.i ꞉= .e) p with (evalExp e s)
    ... | just x = Any.just tt
  -}
  
  assiProgW/ValidExpTerminates : ∀ i exp s → ( a : i := exp ) → Is-just (evalExp exp s) → Terminates ( 𝑎𝑠𝑠𝑖꞉ a ) s
  assiProgW/ValidExpTerminates i e s (.i ꞉= .e) p  = 1 , (is-JustExp→is-JustAssi {i} {e} {s} p)


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


