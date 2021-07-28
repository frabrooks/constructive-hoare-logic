{-# OPTIONS --allow-unsolved-metas #-}

-- Lib Imports
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; subst ; sym ; cong ; inspect ; [_] )
open import Data.Maybe.Relation.Unary.Any renaming ( just to any-just )
open import Data.Product using (Σ ; Σ-syntax ; _×_  ; _,_  ; proj₁ ; proj₂ )
open import Data.Maybe using ( Maybe ; just ; nothing ; _>>=_ ; Is-just ; to-witness )
import Data.Maybe.Relation.Unary.Any 
open Data.Maybe.Relation.Unary.Any.Any renaming ( just to any-just )
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using ( ⊥ ; ⊥-elim )
open import Data.Bool
open import Function using (_$_ ; _∘_)
open import Function.Equivalence hiding (sym)


-- Project Imports
open import Representation.Data using (Data-Implementation)
open import Representation.State using (S-Representation)

open import Misc

module Hoare-Logic.Semantics ( 𝔡 : Data-Implementation )
  (sRep : S-Representation 𝔡 ) where

  open Data-Implementation 𝔡
  open S-Representation sRep

  open import Mini-C.Expressions 𝔡 sRep
  open import Assertions.Props 𝔡 sRep

  open import Mini-C.Lang 𝔡 sRep

  open import Hoare-Logic.Termination 𝔡 sRep

--  data Π (A : Set) (B : A → Set) : Set where
--    Λ : ((a : A) → B a) → Π A B


  


  --data WP : 𝐶 → 𝐴 → Set
  --  ω : ∀ {c} {p} Σ Exp (λ e → (s s' : S) → ifEval s c s' → (s' ← p) → WP c p
  -- WP is an expression s.t. for all S satisfying it, evaluation of 
  -- C starting in that State evaluates to S, that S satisfies P
  -- wp C R = Σ 𝐴 (λ P → (s s' : S) → ifEval s c s' → 

  -- This is an Exp 
  -- The weakest predicate that guarantees termination of C in P
  --  WP s C Q = ( s' : S ) →  Eval s C s' → ( Q ← s' )
  --  WP C Q = Σ[ s ∈ S ] Π S (λ s' → Eval s C s' → ( Q ← s' ))

  -- ⇓This actually defines the set of ALL preconditions, not the weakest
  -- WP : 𝐶 → 𝐴 → Set
  -- WP C Q = Σ Exp (λ e → (s s' : S) → (e ← s) → ifEval s C s' → ( Q ← s'))


  ⊢ₚᵣₒₚ : 𝐴 → S → Set
  ⊢ₚᵣₒₚ a₁ s = Σ (𝑃 a₁ s) (⊢ {s} {a₁})

  
  -- (P : 𝑨) is a precondition of C,Q at s
  precondition_ₐₜ_⊨_ₛₜ_ : (P : 𝐴)
    → (s : S) → (C : 𝐶) → (Q : 𝐴) → Set
  precondition a₁ ₐₜ s ⊨ C ₛₜ a₂ =
               Σ[ P ∈ 𝑃 a₁ s ]
               ( ⊢ {s} {a₁} P
                 ×
                 Σ[ output ∈ ⟦ C ⸴ s ⟧ ]
                 (⊢ₚᵣₒₚ a₂ (‵ output) ))

  -- triple : ∀ {P Q} → 𝐶 → (s : S) → (P ← s) → (Q ← s) → Set
  -- triple C s TP TQ = (s' : S) → Evals s C s' → 
  -- precon : 𝐴 → 𝐶 → 𝐴 → Set
  -- precon P C Q = (s : S) → (P ← s) → (s' : S) → Evals s C s' → Q ← s'

  ′ = proj₁

  WP : ∀ s → 𝐶 → 𝐴 → Set
  WP s C R = Σ[ Q ∈ 𝐴 ] (
   Σ[ 𝔔 ∈ (precondition Q ₐₜ s ⊨ C ₛₜ R ) ]
    ( 
     ( P : 𝐴 ) → 
     (
      (precondition P ₐₜ s ⊨ C ₛₜ R )
      ≃
      (Σ[ 𝒫 ∈ 𝑃 P s ] (ₐₜ P ⸴ Q ⸴ s ∶ 𝒫 ⇒ (′ 𝔔)))
     )
    )
   )


  record 𝑃𝑟𝑒𝐶𝑜𝑛𝑑_𝑓𝑜𝑟⟪_⸴_⸴_⟫ (preC : 𝐴) (s : S) (PROG : 𝐶) (postC : 𝐴) : Set where
    field
     𝑤𝑓𝑓-𝑝𝑟𝑒    : 𝑃 preC s
     ⊢𝑝𝑟𝑒       : ⊢ {s} {preC} 𝑤𝑓𝑓-𝑝𝑟𝑒
     𝑤𝑓𝑓-𝑝𝑜𝑠𝑡   : (ϕ : Terminates PROG s) 
                → 𝑃 postC (Result ϕ) 
     ⊢𝑝𝑜𝑠𝑡      : (ϕ : Terminates PROG s)
                → ⊢ {(Result ϕ)} {postC} (𝑤𝑓𝑓-𝑝𝑜𝑠𝑡 ϕ)

  open 𝑃𝑟𝑒𝐶𝑜𝑛𝑑_𝑓𝑜𝑟⟪_⸴_⸴_⟫

  record 𝑃𝑟𝑒𝐶𝑜𝑛𝑑_𝑓𝑜𝑟⟦_⸴_⸴_⟧ (preC : 𝐴) (s : S) (PROG : 𝐶) (postC : 𝐴) : Set where
    field
     ⟪⟫         : 𝑃𝑟𝑒𝐶𝑜𝑛𝑑 preC 𝑓𝑜𝑟⟪ s ⸴ PROG ⸴ postC ⟫
     ℎ𝑎𝑙𝑡𝑠      : Terminates PROG s


  open 𝑃𝑟𝑒𝐶𝑜𝑛𝑑_𝑓𝑜𝑟⟦_⸴_⸴_⟧

  record 𝑊𝑃 (s : S) (PROG : 𝐶) (postC : 𝐴) : Set where
    field
      𝓌𝓅         : 𝐴
      isPreCond  : 𝑃𝑟𝑒𝐶𝑜𝑛𝑑 𝓌𝓅 𝑓𝑜𝑟⟦ s ⸴ PROG ⸴ postC ⟧
      isWeakest  : ∀ ( C : 𝐴)
                 → 𝑃𝑟𝑒𝐶𝑜𝑛𝑑 C 𝑓𝑜𝑟⟦ s ⸴ PROG ⸴ postC ⟧
                 → C ⇒ 𝓌𝓅
  open 𝑊𝑃

  {-
  record ⟪𝑊𝑃⟫𝑓𝑜𝑟 (s : S) (PROG : 𝐶) (postC : 𝐴) : Set where
    field
      𝓌𝓅         : 𝐴    
      isPreCond  : 𝑃𝑟𝑒𝐶𝑜𝑛𝑑 𝓌𝓅 𝑓𝑜𝑟⟪ s ⸴ PROG ⸴ postC ⟫
      isWeakest  : ∀ (C : 𝐴)
                 → 𝑃𝑟𝑒𝐶𝑜𝑛𝑑 C 𝑓𝑜𝑟⟪ s ⸴ PROG ⸴ postC ⟫
                 → C ⇒ 𝓌𝓅
  open ⟪𝑊𝑃⟫𝑓𝑜𝑟
  -}

  -------------------------------------------------
  -- Prop1. Law of Excluded Miracle
  
  property1 : ∀ s C → 𝑊𝑃 s C ∅ₛ → ⊥
  property1 s C 𝑤𝑝 = go {s} {𝓌𝓅 𝑤𝑝} (isPreCond 𝑤𝑝)
    where
    go : ∀ {s P C} → 𝑃𝑟𝑒𝐶𝑜𝑛𝑑 P 𝑓𝑜𝑟⟦ s ⸴ C ⸴ ∅ₛ ⟧ → ⊥ 
    go Γ =
     let ⟪⟫ = ⟪⟫ Γ in let ⟦⟧ = ℎ𝑎𝑙𝑡𝑠 Γ in
     subst T (𝑭is𝑭 (𝑤𝑓𝑓-𝑝𝑜𝑠𝑡 ⟪⟫ ⟦⟧)) (⊢𝑝𝑜𝑠𝑡 ⟪⟫ ⟦⟧)

  -------------------------------------------------
  --  Prop2.  Q ⇒ R → wp(S , Q) ⇒ wp(S , R) 

  property2 : ∀ s C Q R → (Q ⇒ R)
         → (wpq : 𝑊𝑃 s C Q ) → ( wpr : 𝑊𝑃 s C R )
                              → (𝓌𝓅 wpq ⇒ 𝓌𝓅 wpr)
  property2 _ _ _ _ Q⇒R wpq wpr s' ⊢wpq = let
     -- ϕ = given that Q⇒R, if the output state
     -- s', serving as evidence that C terminates 
     -- ₛₜ (Q ← s'), then we also have (R ← s')
     Γ = (Q⇒R
             (Result (ℎ𝑎𝑙𝑡𝑠 (isPreCond wpq)))
               ((𝑤𝑓𝑓-𝑝𝑜𝑠𝑡 (⟪⟫ (isPreCond wpq))
               (ℎ𝑎𝑙𝑡𝑠 (isPreCond wpq)))
               ,
               (⊢𝑝𝑜𝑠𝑡 (⟪⟫ (isPreCond wpq))
               (ℎ𝑎𝑙𝑡𝑠 (isPreCond wpq))))
               ,
               ⊢wpq )
     in let -- Ω = 𝓌𝓅(C,Q) is valid preCond of R
     Ω = record {
       ⟪⟫ = record {
            𝑤𝑓𝑓-𝑝𝑟𝑒 =  𝑤𝑓𝑓-𝑝𝑟𝑒 (⟪⟫ (isPreCond wpq));
            ⊢𝑝𝑟𝑒 =    ⊢𝑝𝑟𝑒 (⟪⟫ (isPreCond wpq))    ;
            𝑤𝑓𝑓-𝑝𝑜𝑠𝑡 = λ ϕ →
                 𝑤𝑓𝑓-𝑝𝑜𝑠𝑡 (⟪⟫ (isPreCond wpr)) ϕ   ;
            ⊢𝑝𝑜𝑠𝑡 = λ ϕ →
                    ⊢𝑝𝑜𝑠𝑡 (⟪⟫ (isPreCond wpr)) ϕ   }
       ; ℎ𝑎𝑙𝑡𝑠 = ℎ𝑎𝑙𝑡𝑠 (isPreCond wpq) }
     in (isWeakest wpr) (𝓌𝓅 wpq) Ω s' ⊢wpq

  -------------------------------------------------
  -- Prop3.

  _𝑎𝑛𝑑_ : 𝐴 → 𝐴 → 𝐴
  P 𝑎𝑛𝑑 Q = (op₂ P && Q)

  lemm : ∀ s C 𝑄 𝑅
       → (𝑊𝑃 s C 𝑄) → (𝑊𝑃 s C 𝑅)
       → (𝑊𝑃 s C (𝑄 𝑎𝑛𝑑 𝑅))
  lemm s C Q R 𝓌𝓅Q 𝓌𝓅R =
    let Σ⊢Q&R = ConjunctionIntro
                (evalExp (𝓌𝓅 𝓌𝓅Q) s)
                (evalExp (𝓌𝓅 𝓌𝓅R) s)
                ((𝑤𝑓𝑓-𝑝𝑟𝑒 (⟪⟫ (isPreCond 𝓌𝓅Q))) ,
                (⊢𝑝𝑟𝑒 (⟪⟫ (isPreCond 𝓌𝓅Q))))
                ((𝑤𝑓𝑓-𝑝𝑟𝑒 (⟪⟫ (isPreCond 𝓌𝓅R))) ,
                (⊢𝑝𝑟𝑒 (⟪⟫ (isPreCond 𝓌𝓅R))))  in
    record {
      𝓌𝓅 = (𝓌𝓅 𝓌𝓅Q) 𝑎𝑛𝑑 (𝓌𝓅 𝓌𝓅R) ;
      isPreCond =
        let wffQ = 𝑤𝑓𝑓-𝑝𝑜𝑠𝑡 (⟪⟫ (isPreCond 𝓌𝓅Q)) in
        let wffR = 𝑤𝑓𝑓-𝑝𝑜𝑠𝑡 (⟪⟫ (isPreCond 𝓌𝓅R)) in
        let haltsQ = ℎ𝑎𝑙𝑡𝑠 (isPreCond 𝓌𝓅Q) in
        let haltsR = ℎ𝑎𝑙𝑡𝑠 (isPreCond 𝓌𝓅R) in
        let ⊢Q   = ⊢𝑝𝑜𝑠𝑡  (⟪⟫ (isPreCond 𝓌𝓅Q)) in
        let ⊢R = ⊢𝑝𝑜𝑠𝑡 (⟪⟫ (isPreCond 𝓌𝓅R)) in
        let foo = ConjunctionIntro _ _ ? in
        let rw =  EvaluationIsDeterministic {s} C
                  (proj₁ (ℎ𝑎𝑙𝑡𝑠 (isPreCond 𝓌𝓅Q)))
                  (proj₁ (ℎ𝑎𝑙𝑡𝑠 (isPreCond 𝓌𝓅R)))
                  (ℎ𝑎𝑙𝑡𝑠 (isPreCond 𝓌𝓅Q))
                  (ℎ𝑎𝑙𝑡𝑠 (isPreCond 𝓌𝓅R))
                  refl refl in
        let ϕ = subst (λ s →
                ⊨ (evalExp Q (Result (ℎ𝑎𝑙𝑡𝑠 (isPreCond 𝓌𝓅Q)))
                   &&𝓿
                   evalExp R s)) (sym rw)
                   (ConjunctionIntro _ _ (wffQ haltsQ , ⊢Q haltsQ) (wffR haltsR , ⊢R haltsR))
        in
        record {
          ⟪⟫ = record {
            𝑤𝑓𝑓-𝑝𝑟𝑒 = proj₁ Σ⊢Q&R ;
            ⊢𝑝𝑟𝑒 = proj₂ Σ⊢Q&R ;
            𝑤𝑓𝑓-𝑝𝑜𝑠𝑡 =  ?  ;
            ⊢𝑝𝑜𝑠𝑡 = ? }
          ; ℎ𝑎𝑙𝑡𝑠 = ℎ𝑎𝑙𝑡𝑠 (isPreCond 𝓌𝓅Q) } ;
      isWeakest = λ CONDϕ ϕisPre s ⊢ϕ
           → let ⊢𝓌𝓅Q = (isWeakest 𝓌𝓅Q) CONDϕ (
                   record {
                     ⟪⟫ = record {
                       𝑤𝑓𝑓-𝑝𝑟𝑒 = 𝑤𝑓𝑓-𝑝𝑟𝑒 ϕisPre 
                       ; ⊢𝑝𝑟𝑒 = ⊢𝑝𝑟𝑒 ϕisPre
                       ; 𝑤𝑓𝑓-𝑝𝑜𝑠𝑡 = proj₁
                         (ConjunctionElim₁ _ _
                           ((𝑤𝑓𝑓-𝑝𝑜𝑠𝑡 ϕisPre) ,
                           (⊢𝑝𝑜𝑠𝑡 ϕisPre)))
                       ; ⊢𝑝𝑜𝑠𝑡 = proj₂
                         (ConjunctionElim₁ _ _
                           ((𝑤𝑓𝑓-𝑝𝑜𝑠𝑡 ϕisPre) ,
                           (⊢𝑝𝑜𝑠𝑡 ϕisPre))) }
                     ; ℎ𝑎𝑙𝑡𝑠 = ℎ𝑎𝑙𝑡𝑠 ϕisPre

                   }) s ⊢ϕ
             in             
             let ⊢𝓌𝓅R = (isWeakest 𝓌𝓅R) CONDϕ (
                   record {
                     𝑤𝑓𝑓-𝑝𝑟𝑒 = 𝑤𝑓𝑓-𝑝𝑟𝑒 ϕisPre 
                     ; ⊢𝑝𝑟𝑒 = ⊢𝑝𝑟𝑒 ϕisPre
                     ; ℎ𝑎𝑙𝑡𝑠 = ℎ𝑎𝑙𝑡𝑠 ϕisPre
                     ; 𝑤𝑓𝑓-𝑝𝑜𝑠𝑡 = proj₁
                       (ConjunctionElim₂ _ _
                         ((𝑤𝑓𝑓-𝑝𝑜𝑠𝑡 ϕisPre) ,
                         (⊢𝑝𝑜𝑠𝑡 ϕisPre)))
                     ; ⊢𝑝𝑜𝑠𝑡 = proj₂
                       (ConjunctionElim₂ _ _
                         ((𝑤𝑓𝑓-𝑝𝑜𝑠𝑡 ϕisPre) ,
                         (⊢𝑝𝑜𝑠𝑡 ϕisPre)))
                   }) s ⊢ϕ
            in ConjunctionIntro _ _ ⊢𝓌𝓅Q ⊢𝓌𝓅R }

  property3 : ∀ s C 𝑄 𝑅 →
    ( Σ[ Q ∈ 𝑊𝑃 s C 𝑄 ]
    ( Σ[ R ∈ 𝑊𝑃 s C 𝑅 ]
    ( Σ⊢ s (𝓌𝓅 Q 𝑎𝑛𝑑 𝓌𝓅 R) )))
    ⇔
    (Σ[ Q&R ∈ 𝑊𝑃 s C (𝑄 𝑎𝑛𝑑 𝑅) ]
    (Σ⊢ s (𝓌𝓅 Q&R)))
  property3 s C Q R =
    record {
      to =
        record {
          _⟨$⟩_ = {!!} ;
          cong = {!!} } ;
          from = {!!} }

{-
  record {
    to = (λ Σ⊢𝑤𝑝Q&𝑤𝑝R →
            -- We have: ⊢ 𝓌𝓅Q  and  ⊢𝓌𝓅R
           (isWeakest Q&R)
           (𝓌𝓅 Q 𝑎𝑛𝑑 𝓌𝓅 R)
           (record
            { 𝑤𝑓𝑓-𝑝𝑟𝑒 = proj₁ Σ⊢𝑤𝑝Q&𝑤𝑝R
            ; ⊢𝑝𝑟𝑒 = proj₂ Σ⊢𝑤𝑝Q&𝑤𝑝R
            ; ℎ𝑎𝑙𝑡𝑠 = ℎ𝑎𝑙𝑡𝑠 (isPreCond Q&R)
            ; 𝑤𝑓𝑓-𝑝𝑜𝑠𝑡 = 𝑤𝑓𝑓-𝑝𝑜𝑠𝑡 (isPreCond Q&R)
            ; ⊢𝑝𝑜𝑠𝑡 = ⊢𝑝𝑜𝑠𝑡 (isPreCond Q&R) })
           s
           Σ⊢𝑤𝑝Q&𝑤𝑝R )
    ; from = λ Σ⊢𝓌𝓅Q&R → let
             wffQ&R = 𝑤𝑓𝑓-𝑝𝑜𝑠𝑡 (isPreCond Q&R)
             in let ⊢Q&R = ⊢𝑝𝑜𝑠𝑡 (isPreCond Q&R)
             in let ⊢𝓌𝓅Q = (isWeakest Q)
                     (𝓌𝓅 Q&R)
                     (record
                      { 𝑤𝑓𝑓-𝑝𝑟𝑒 = proj₁ Σ⊢𝓌𝓅Q&R
                      ; ⊢𝑝𝑟𝑒 = proj₂ Σ⊢𝓌𝓅Q&R
                      ; ℎ𝑎𝑙𝑡𝑠 = ℎ𝑎𝑙𝑡𝑠 (isPreCond Q&R)
                      ; 𝑤𝑓𝑓-𝑝𝑜𝑠𝑡 = proj₁ (ConjunctionElim₁ _ _ (wffQ&R , ⊢Q&R)) 
                      ; ⊢𝑝𝑜𝑠𝑡 =  proj₂ (ConjunctionElim₁ _ _ (wffQ&R , ⊢Q&R)) })
                      s
                      Σ⊢𝓌𝓅Q&R
             in let ⊢𝓌𝓅R = (isWeakest R)
                     (𝓌𝓅 Q&R)
                     (record
                      { 𝑤𝑓𝑓-𝑝𝑟𝑒 = proj₁ Σ⊢𝓌𝓅Q&R
                      ; ⊢𝑝𝑟𝑒 = proj₂ Σ⊢𝓌𝓅Q&R
                      ; ℎ𝑎𝑙𝑡𝑠 = ℎ𝑎𝑙𝑡𝑠 (isPreCond Q&R)
                      ; 𝑤𝑓𝑓-𝑝𝑜𝑠𝑡 = proj₁ (ConjunctionElim₂ _ _ (wffQ&R , ⊢Q&R)) 
                      ; ⊢𝑝𝑜𝑠𝑡 =  proj₂ (ConjunctionElim₂ _ _ (wffQ&R , ⊢Q&R)) })
                      s
                      Σ⊢𝓌𝓅Q&R
             in ConjunctionIntro _ _ ⊢𝓌𝓅Q ⊢𝓌𝓅R  }
-}

{-  
           (λ _ → ConjunctionIntro
           (evalExp (𝓌𝓅 Q) s) (evalExp (𝓌𝓅 R) s)
           (𝑤𝑓𝑓-𝑝𝑟𝑒 (isPreCond Q)) (𝑤𝑓𝑓-𝑝𝑟𝑒 (isPreCond R))
           (⊢𝑝𝑟𝑒 (isPreCond Q)) (⊢𝑝𝑟𝑒 (isPreCond R)) )
-}


  {-
  lemm : ∀ P C → precond P C ∅ₛ → P ≡ ∅ₛ
  lemm (op₂ l ∙ r) C isPre = {!!}
  lemm (op₁ ∙ e) C isPre = {!!}
  lemm (term (Const x)) C isPre = {!!}
  lemm (term (Var x)) C isPre = {!!}
  lemm (term 𝒕) C isPre with isPre ● ( 𝑻isWFF , subst T (sym (𝑻is𝑻 𝑻isWFF)) tt)
  ... | _ , WFF𝑭 , 𝑭is𝑻 = ⊥-elim (subst T (𝑭is𝑭 WFF𝑭) 𝑭is𝑻 )
  lemm (term 𝒇) C isPre = refl

  property1 : ∀ (C : 𝐶) → (wp : (WP C ∅ₛ)) → ′ wp ≡ ∅ₛ
  property1 C ( exp , fst₂ , snd) = {!!}
  -}




{-
  WP : 𝐶 → 𝐴 → Set
  WP C Q = Σ[ P ∈ 𝐴 ] ((A : 𝐴) → ((s s' : S) →
           (A ← s) → ifEval s C s' → ( Q ← s')) → (A ⇒ P))
-}


-- (P : 𝐴) → Σ[ wp ∈ precon C Q P ] (prec : precon C Q P) → prec ⇒ 


-- ( P' : 𝐴 ) → precondition C Q P' → P' ⇒ P


  -- proj₁ (WP' C Q)


  -- Do we want the Exp that is the WP to be in a Sigma type or do we want
  -- to capture it at the type level?
  -- Do we ever need to reason about a 𝑠𝑝𝑒𝑐𝑖𝑓𝑐 WP? Or do we only ever reason about
  -- all WP at once? Netiher maybe?? I think we want it as a function of 𝐶 & Q


  -- Need to prove:
  -- prop1. wp(S, F) ≡ F  (→ ⊥ ?)  -- Law of excluded miracle

  -- prop2.  Q ⇒ R → wp(S , Q) ⇒ wp(S , R) 


  -- Start with prop.3:

  --  prop3 : ∀ (s : S) (c : 𝐶) (Q R : 𝐴) → (proj₁ wp( c , Q) ← s) × (proj₁ wp( c , R ) ← s) ≅ (proj₁ wp( c , (op₂ Q (&&𝓿 :𝔹) R)) ← s)
  -- prop3. (wp(S , Q) ∧ wp(S , R)) ≡ wp(s, Q ∧ R)
  --           (×)






  -- prop4. (wp(S, Q) ∨ wp(S, R)) ≡ wp(S, Q ∨ R)

{-
  -- Hoare's Notation: {P}C{Q}   P → wp C P   ( Partial Correctness )
  ⟪_⟫_⟪_⟫ :  𝐴 → 𝐶 → 𝐴 → Set
  ⟪ P ⟫ C ⟪ Q ⟫ = Σ[ s ∈ S ] ((𝓌𝓅POST : 𝑊𝑃 s C Q) → P ⇒ (𝓌𝓅 𝓌𝓅POST))


  -- P ⇒ (proj₁ (wp ( C , Q )))


  -- Total Correctness 
  ⟦_⟧_⟦_⟧ :  𝐴 → 𝐶 → 𝐴 → Set
  ⟦ P ⟧ C ⟦ Q ⟧ = Σ[ s ∈ S ] Σ[ 𝓌𝓅POST ∈ 𝑊𝑃 s C Q ]
                ( ⟦ C ⸴ s ⟧ × ⟪ P ⟫ C ⟪ Q ⟫)

  -- ⟦𝑃𝑟𝑒𝐶𝑜𝑛𝑑⟧ P 𝑓𝑜𝑟 s C Q -- Σ[ s ∈ S ] Terminates C s ×  ⟪ P ⟫ C ⟪ Q ⟫ 

  Υ : ∀ P C Q → (γ : ⟦ P ⟧ C ⟦ Q ⟧)
    → (wpQ : 𝑊𝑃 (′ γ) C Q) → P ⇒ (𝓌𝓅 wpQ)
  Υ P C Q ( s , isPre) wpq = isWeakest wpq P isPre

-}


{-
  ( s : S ) → ( P ← s ) → WP s C Q
  -- WANT THIS TO BE:    P ⇒ wp( C , Q )
  --  maybe has to be:   P ⇒ (proj₁ (wp( C , Q)))
-}


  -- Π S (λ(s : S) → ( P ← s ) × Terminates C s s' → ( Q ← s' ) )


  --              P ⇒ wp( C , Q ) 
  --              i.e. P = X = 6
  --                   wp = X != 0
  --                 ∴  P → wp 
  --
  --              Terminates → eval C P s = s' → Q s'











