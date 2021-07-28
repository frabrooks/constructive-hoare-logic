

-- Lib imports
open import Data.Maybe using (Maybe ; just ; nothing ; is-just )
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl ; sym ; inspect ; Reveal_·_is_ ; cong ; subst ) 
open import Data.Product using (Σ ; Σ-syntax ; _×_  ; _,_  ; proj₁ ; proj₂ )
open import Data.Bool using (true ; false)
open import Relation.Nullary using ( ¬_  ; yes ; no )
open import Data.Empty using ( ⊥ ; ⊥-elim )

open import Representation.Data using (Data-Implementation)
open import Representation.State using (S-Representation)


module Hoare-Logic.Axioms (𝔡 : Data-Implementation )
  (sRep : S-Representation 𝔡 ) where

  open Data-Implementation 𝔡
  open S-Representation sRep

  open import Mini-C.Expressions 𝔡 sRep
  open import Assertions.Props 𝔡 sRep

  open import Mini-C.Lang 𝔡 sRep
  open import Mini-C.Evaluation 𝔡 sRep

  open import Hoare-Logic.Semantics 𝔡 sRep


  {-
  subRecᶻ : ∀ {i} {v} {s} e → getVarVal i s ≡ just v → evalℤExp (subℤExp v i e) s ≡ evalℤExp e s
  subRecᶻ {i} {v} {s} (⇉ᶻ l α r) p rewrite sub-helpᶻ l r v i α | subRecᶻ l p | subRecᶻ r p = refl
  subRecᶻ {i} {v} {s} (Const x) p = refl
  subRecᶻ {i} {v} {s} (Var x) p with i ?id= x
  ... | yes q rewrite q = sym p
  ... | no ¬q = refl
  

  subRecᵇ : ∀ {i} {v} {s} p → getVarVal i s ≡ just v → eval𝔹Exp (sub v i p) s ≡ eval𝔹Exp p s
  subRecᵇ {i} {v} (ᶻ⇉ᵇ l α r) q rewrite sub-helpᶻᵇ l r v i α | subRecᶻ l q | subRecᶻ r q = refl
  subRecᵇ {i} {v} (⇉ᵇ  l α r) q rewrite sub-helpᵇ l r v i α | subRecᵇ l q | subRecᵇ r q = refl
  subRecᵇ {i} {v} (⇾ᵇ ¬ᵇ p) q rewrite subRecᵇ p q = refl
  subRecᵇ {i} {v} 𝒕 q = refl
  subRecᵇ {i} {v} 𝒇 q = refl

  s⇔ᶻu : ∀ i v s e → evalℤExp e (updateState i v s) ≡ evalℤExp (subℤExp v i e) s
  s⇔ᶻu i v s (⇉ᶻ l α r) rewrite sub-helpᶻ l r v i α | s⇔ᶻu i v s l | s⇔ᶻu i v s r = refl
  s⇔ᶻu i v s (Const x) = refl
  s⇔ᶻu i v s (Var x) with i ?id= x
  ... | yes p rewrite p = updateGet x v s
  ... | no ¬p rewrite irrelUpdate i x v (getVarVal x (updateState i v s)) ¬p s refl = refl

  s⇔u : ∀ i v s p → eval𝔹Exp p (updateState i v s) ≡ eval𝔹Exp (sub v i p) s
  s⇔u i v s (ᶻ⇉ᵇ l α r) rewrite sub-helpᶻᵇ l r v i α | s⇔ᶻu i v s l | s⇔ᶻu i v s r = refl
  s⇔u i v s (⇉ᵇ l α r) rewrite sub-helpᵇ l r v i α | s⇔u i v s l | s⇔u i v s r = refl
  s⇔u i v s (⇾ᵇ ¬ᵇ p) rewrite s⇔u i v s p = refl
  s⇔u i v s 𝒕 = refl
  s⇔u i v s 𝒇 = refl
  

  
  private sub-helpᶻ : ∀ l r e i α → subℤExp e i  (⇉ᶻ l α r) ≡ (⇉ᶻ (subℤExp e i l) α (subℤExp e i r))
  sub-helpᶻ l r e i +ᶻ = refl
  sub-helpᶻ l r e i -ᶻ = refl
  sub-helpᶻ l r e i *ᶻ = refl
  sub-helpᶻ l r e i /ᶻ = refl
  sub-helpᶻ l r e i %ᶻ = refl
  private sub-helpᵇ : ∀ l r e i α → sub e i (⇉ᵇ l α r) ≡ (⇉ᵇ (sub e i l) α (sub e i r))
  sub-helpᵇ l r e i && = refl
  sub-helpᵇ l r e i || = refl
  sub-helpᵇ l r e i ⇔ = refl
  private sub-helpᶻᵇ : ∀ l r e i α → sub e i (ᶻ⇉ᵇ l α r) ≡ (ᶻ⇉ᵇ (subℤExp e i l) α (subℤExp e i r))
  sub-helpᶻᵇ l r e i ≤  = refl
  sub-helpᶻᵇ l r e i <  = refl
  sub-helpᶻᵇ l r e i == = refl
  sub-helpᶻᵇ l r e i ≥  = refl
  sub-helpᶻᵇ l r e i >  = refl
  

  private const-help : ∀ {x} ( s : S ) → evalTerm (Const x) s ≡ just x
  const-help _ = refl

  private 𝒕-help : ∀ ( s : S ) → evalTerm 𝒕 s ≡ just 𝑻
  𝒕-help _ = refl

  private 𝒇-help : ∀ ( s : S ) → evalTerm 𝒇 s ≡ just 𝑭
  𝒇-help _ = refl

  
  private const-helpᶻ : ∀ {x} ( s : S ) → evalℤExp (termℤ (Const x)) s ≡ just x
  const-helpᶻ s = refl

  private const-helpᵇ : ∀ {x} ( s : S ) → eval𝔹Exp (term𝔹 (Const x)) s ≡ just x
  const-helpᵇ s = refl

  private 𝒕-help : ∀ ( s : S ) → evalℤExp (termℤ 𝒕) s ≡ just 𝑻
  𝒕-help s = refl

  private 𝒕-help' : ∀ ( s : S ) → evalExp (termℤ 𝒕) s ≡ just 𝑻
  𝒕-help s = refl

  private 𝒇-help : ∀ ( s : S ) → evalℤExp (termℤ 𝒇) s ≡ just 𝑭
  𝒇-help s = refl
    

  private sub-𝔹Exp-id : ∀ x → ( e : 𝔹Exp ) →  subℤExp (𝔹: e) x (termℤ (Var x)) ≡ 𝔹Exp-ℤExp e
  sub-𝔹Exp-id x e with inspect (subℤExp (𝔹: e) x ) (termℤ (Var x))
  sub-𝔹Exp-id x e | Eq.[ eq ] with x ?id= x
  sub-𝔹Exp-id x e | Eq.[ eq ] | yes p  = eq
  sub-𝔹Exp-id x e | Eq.[ eq ] | no ¬p  = ⊥-elim (¬p refl)

  private sub-ℤExp-id : ∀ x → ( e : ℤExp ) →  subℤExp (ℤ: e) x (termℤ (Var x)) ≡  e
  sub-ℤExp-id x e with inspect (subℤExp (ℤ: e) x ) (termℤ (Var x))
  sub-ℤExp-id x e | Eq.[ eq ] with x ?id= x
  sub-ℤExp-id x e | Eq.[ eq ] | yes p  = eq
  sub-ℤExp-id x e | Eq.[ eq ] | no ¬p  = ⊥-elim (¬p refl)



    with subℤExp (𝔹: e) x (termℤ (Var x)) | inspect (subℤExp (𝔹: e) x ) (termℤ (Var x))
  foo x e | (𝔹Exp-ℤExp x₁)  | Eq.[ eq ] rewrite eq with x ?id= x
  foo x e | (𝔹Exp-ℤExp x₁)  | Eq.[ eq ] | yes p = sym eq
  foo x e | ⇉ᶻ l α r | Eq.[ eq ] with x ?id= x
  foo x e | ⇉ᶻ l α r | Eq.[ eq ] | yes p = sym eq
  foo x e | termℤ x₁ | Eq.[ eq ] = {!!}
 

  private ExpVar-help : ∀ {x} {s} ( e : Exp ) → evalℤExp (subℤExp e x (termℤ (Var x))) s ≡ evalExp e s
  ExpVar-help {x} {s} (𝔹: e) rewrite sub-𝔹Exp-id x e = refl
  ExpVar-help {x} {s} (ℤ: e) rewrite sub-ℤExp-id x e = refl
  -}


  {-
  sub⇔updateᶻ : ∀ i e' v s e → evalExp e' s ≡ just v → evalℤExp e (updateState i v s) ≡ evalℤExp (subℤExp e' i e) s
  sub⇔updateᵇ : ∀ i e' v s e → evalExp e' s ≡ just v → eval𝔹Exp e (updateState i v s) ≡ eval𝔹Exp (sub e' i e) s

  sub⇔updateᶻ i e' v s (𝔹Exp-ℤExp e) pr rewrite  sub⇔updateᵇ i e' v s e pr = refl
  sub⇔updateᶻ i e' v s (⇉ᶻ l α r) pr rewrite sub-helpᶻ l r e' i α | sub⇔updateᶻ i e' v s l pr |  sub⇔updateᶻ i e' v s r pr = refl
  sub⇔updateᶻ i e' v s (termℤ (Const x)) pr = ? -- rewrite const-helpᶻ {x} (updateState i v s) = refl
  sub⇔updateᶻ i e' v s (termℤ 𝒕) pr = ? -- rewrite 𝒕-help (updateState i v s) = refl
  sub⇔updateᶻ i e' v s (termℤ 𝒇) pr = ? -- rewrite 𝒇-help (updateState i v s) = refl
  sub⇔updateᶻ i e' v s (termℤ (Var x)) pr with i ?id= x 
  sub⇔updateᶻ i e'      v s (termℤ (Var x)) pr  | no  ¬p = ignoreTop i x v ¬p s
  sub⇔updateᶻ i (𝔹: e') v s (termℤ (Var x)) pr  | yes p rewrite p | pr  = updateGet x v s
  sub⇔updateᶻ i (ℤ: e') v s (termℤ (Var x)) pr  | yes p rewrite p | pr  = updateGet x v s
  
  sub⇔updateᵇ i e' v s (ᶻ⇉ᵇ l α r) pr rewrite sub-helpᶻᵇ l r e' i α | sub⇔updateᶻ i e' v s l pr | sub⇔updateᶻ i e' v s r pr =  refl
  sub⇔updateᵇ i e' v s (⇉ᵇ l α r) pr rewrite sub-helpᵇ l r e' i α | sub⇔updateᵇ i e' v s l pr | sub⇔updateᵇ i e' v s r pr =  refl
  sub⇔updateᵇ i e' v s (⇾ᵇ ¬ᵇ e) pr rewrite sub⇔updateᵇ i e' v s e pr = refl
  sub⇔updateᵇ i e' v s (term𝔹 (Const x)) pr rewrite const-helpᵇ {x} (updateState i v s)  = refl
  sub⇔updateᵇ i e' v s (term𝔹 (Var x)) pr = {!!}
  sub⇔updateᵇ i e' v s (term𝔹 𝒕) pr = {!!}
  sub⇔updateᵇ i e' v s (term𝔹 𝒇) pr = {!!}
  -}


  -- for all i e P, in all states, the Axiom of assignment holds
  axiomOfAssignment : ∀ i e P → S → ⟪ (sub e i P) ⟫ ( 𝑎𝑠𝑠𝑖꞉ ( i ꞉= e ) ) ⟪ P ⟫
  axiomOfAssignment i e (op₂ P x P₁) s = λ s₁ x ϕ → {!!}
  axiomOfAssignment i e (op₁ x P) s = λ s₁ x ϕ → {!!}
  axiomOfAssignment i e (term (Const x)) s = λ s₁ p ϕ → {!!}
  axiomOfAssignment i e (term 𝒕) s = λ s₁ p ϕ → p
  axiomOfAssignment i e (term 𝒇) s = λ s₁ p ϕ → {!!}
  axiomOfAssignment i e (term (Var x)) s with i ?id= x
  ... | yes 𝑝 = λ s₁ p ϕ → {!!} , {!!}
  ... | no ¬𝑝 = {!!}

  {-
  axiomOfAssignment : ∀ {i} {v} {e} (p  :  𝑃) → ( a :  i := e )
                        → ( ( s : S ) →  evalExp e s ≡ (just v))
                        → ⟪ (sub v i p) ⟫ ( 𝑎𝑠𝑠𝑖꞉ a ) ⟪ p ⟫
  axiomOfAssignment {i} {v} {e} p (.i ꞉= .e) pr s pre s' eval =  {!!}
  
 
  axiomOfAssignment : ∀ {i} {e}  (p  :  𝑃) → ( a :  i := e )
                        → ⟪ (sub e i  p) ⟫ ( 𝑎𝑠𝑠𝑖꞉ a ) ⟪ p ⟫
  axiomOfAssignment {i} {e} p (.i ꞉= .e) s pre s' eval with p | (sub e i p)
  ... | ᶻ⇉ᵇ x x₁ x₂     | ᶻ⇉ᵇ x₃ x₄ x₅ = {!!}
  ... | ᶻ⇉ᵇ x x₁ x₂     | ⇉ᵇ bar x₃ bar₁ = {!!}
  ... | ᶻ⇉ᵇ x x₁ x₂     | ⇾ᵇ x₃ bar = {!!}
  ... | ᶻ⇉ᵇ x x₁ x₂     | term𝔹 x₃ = {!!}
  ... | ⇉ᵇ foo x foo₁  | ᶻ⇉ᵇ x₁ x₂ x₃ = {!!}
  ... | ⇉ᵇ foo x foo₁  | ⇉ᵇ bar x₁ bar₁ = {!!}
  ... | ⇉ᵇ foo x foo₁  | ⇾ᵇ x₁ bar = {!!}
  ... | ⇉ᵇ foo x foo₁  | term𝔹 x₁ = {!!}
  ... | ⇾ᵇ x foo       | ᶻ⇉ᵇ x₁ x₂ x₃ = {!!}
  ... | ⇾ᵇ x foo       | ⇉ᵇ bar x₁ bar₁ = {!!}
  ... | ⇾ᵇ x foo       | ⇾ᵇ x₁ bar = {!!}
  ... | ⇾ᵇ x foo       | term𝔹 x₁ = {!!}
  ... | term𝔹 x        | ᶻ⇉ᵇ x₁ x₂ x₃ = {!!}
  ... | term𝔹 x        | ⇉ᵇ bar x₁ bar₁ = {!!}
  ... | term𝔹 x        | ⇾ᵇ x₁ bar = {!!}
  ... | term𝔹 x        | term𝔹 x₁ = {!!}
-}


{-
  -- Axioms
  axiom-of-assignment : ∀ {i} {v} {p} {s s'} {e}
                        → ((sub v i p) ← s)
                        -- Proof that assignment terminates
                        → (i := e |evalExp= v USING s GIVES s') 
                        → ( p ← s' ) 
  axiom-of-assignment {i} {v} {p} {s} {.(updateState i v s)}
                          (holdsBecause eval→𝑻)
                          ((.i :=' _ w/ .s andPExp) x)
                          rewrite sym (s⇔u i v s p)
                          = holdsBecause eval→𝑻



   -- R⊃S → P{Q}R → P{Q}S
  
   -- {Q} S {R}

  


  -- Not sure about these, probs need to have Hoare triple (i.e.  ⊢P{Q}R ) for these to make sense 

  rule-of-consequence1 : ∀ {i} {v} {p q r} {s s'} {e}

                         → ((Assert q ∵ s') → (Assert r ∵ s' ))          --       R ⊃ S
                         
                         → (Assert p ∵ s')                                --        P
                         
                         -- Proof that program terminates
                         -- TODO: All program kinds need to go here, not just
                         -- assignment (i.e. while, block, ifelse etc.)
                         → (i := e |evalExp= v USING s GIVES s')                  -- {Q}

                         → (Assert q ∵ s')                                    -- R

                         → (Assert r ∵ s')
  rule-of-consequence1 {i} {v} {p} {q} {r} {s} {s'} q⊃r a prog b = q⊃r b



  rule-of-consequence2 : ∀ {i} {v} {p q r} {s s'} {e}

                         → ((Assert p ∵ s) → (Assert r ∵ s' ))
                         
                         → (Assert p ∵ s)
                         
                         -- Proof that program terminates
                         -- TODO: All program kinds need to go here, not just
                         -- assignment (i.e. while, block, ifelse etc.)
                         → (i := e |evalExp= v USING s GIVES s')

                         → (Assert q ∵ s')

                         → (Assert r ∵ s)
  rule-of-consequence2 {i} {v} {p} {q} {r} {s} {s'} q⊃r a prog b = {!!}

-}




