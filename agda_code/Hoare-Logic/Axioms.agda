

-- Lib imports
open import Data.Maybe using (Maybe ; just ; nothing ; is-just )
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl ; sym ; inspect ; Reveal_·_is_ ; cong ; subst ) 
open import Data.Bool using (true ; false)
open import Relation.Nullary using ( ¬_  ; yes ; no )
open import Data.Empty using ( ⊥ ; ⊥-elim )

open import Representation.Data using (D-Representation)
open import Representation.State using (S-Representation)


module Hoare-Logic.Axioms (dRep : D-Representation )
  (sRep : S-Representation dRep ) where

  open D-Representation dRep
  open S-Representation sRep

  open import Mini-C.Expressions dRep sRep
  open import Assertions.Props dRep sRep

  open import Mini-C.Lang dRep sRep
  open import Mini-C.Evaluation dRep sRep

  open import Hoare-Logic.Semantics dRep sRep
  
  private sub-helpᶻ : ∀ l r v i α → subℤExp v i  (⇉ᶻ l α r) ≡ (⇉ᶻ (subℤExp v i l) α (subℤExp v i r))
  sub-helpᶻ l r v i +ᶻ = refl
  sub-helpᶻ l r v i -ᶻ = refl
  sub-helpᶻ l r v i *ᶻ = refl
  sub-helpᶻ l r v i /ᶻ = refl
  sub-helpᶻ l r v i %ᶻ = refl
  private sub-helpᵇ : ∀ l r v i α → sub v i (⇉ᵇ l α r) ≡ (⇉ᵇ (sub v i l) α (sub v i r))
  sub-helpᵇ l r v i && = refl
  sub-helpᵇ l r v i || = refl
  sub-helpᵇ l r v i ⇔ = refl
  private sub-helpᶻᵇ : ∀ l r v i α → sub v i (ᶻ⇉ᵇ l α r) ≡ (ᶻ⇉ᵇ (subℤExp v i l) α (subℤExp v i r))
  sub-helpᶻᵇ l r v i ≤  = refl
  sub-helpᶻᵇ l r v i <  = refl
  sub-helpᶻᵇ l r v i == = refl
  sub-helpᶻᵇ l r v i ≥  = refl
  sub-helpᶻᵇ l r v i >  = refl


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

  vExp : Val → Exp
  vExp v = ℤ: (Const v)

  {-
  axiomOfAssignment : ∀ {i} {v} {e} (p  :  𝑃) → ( a :  i := e )
                        → ( ( s : S ) →  evalExp e s ≡ (just v))
                        → ⟪ (sub v i p) ⟫ ( 𝑎𝑠𝑠𝑖꞉ a ) ⟪ p ⟫
  axiomOfAssignment {i} {v} {e} p (.i ꞉= .e) pr s pre s' eval =  {!!}
  -}                          
 
  axiomOfAssignment : ∀ {i} {v}  (p  :  𝑃) → ( a :  i := (vExp v) )
                        → ⟪ (sub v i p) ⟫ ( 𝑎𝑠𝑠𝑖꞉ a ) ⟪ p ⟫
  axiomOfAssignment {i} {v} p (.i ꞉= .(ℤ: (Const v))) s pre s' eval = {!!}
 



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




