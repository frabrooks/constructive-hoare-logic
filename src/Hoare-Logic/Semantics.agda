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
open import Data.Bool hiding (_∧_)
open import Function using (_$_ ; _∘_)
open import Function.Equivalence hiding (sym)


-- Project Imports
open import Data using (Data-Implementation)
open import State using (State-Implementation)

open import Misc

module Hoare-Logic.Semantics ( 𝔡 : Data-Implementation )
  (𝔖 : State-Implementation 𝔡 ) where

  open Data-Implementation 𝔡
  open State-Implementation 𝔖

  open import Language.Expressions 𝔡 𝔖
  open import Language.Assertions 𝔡 𝔖

  open import Language.Mini-Imp 𝔡 𝔖

  open import Evaluation.Termination 𝔡 𝔖

  -- Hoare's Notation: {P}C{Q}   P → wp C P   ( Partial Correctness )
  ⟪_⟫_⟪_⟫ :  𝐴 → C → 𝐴 → Set
  ⟪ P ⟫ C ⟪ Q ⟫ = ( s : S ) → Σ⊢ s P → (ϕ : ⌊ᵗ C ⸴ s ᵗ⌋) → Σ⊢ (‵ ϕ) Q
  
  -- This is wrong, as it would suggest that 𝑭 is a precondition of
  -- all programs that guarantees termination in all states
  -- No, it is write, as 𝑭 IS a precondition of all programs
  -- I.e. if you have a state satisfying 𝑭 then... (bluff!)
  -- 

  -- Total Correctness 
  ⟦_⟧_⟦_⟧ :  𝐴 → C → 𝐴 → Set
  ⟦ P ⟧ C ⟦ Q ⟧ = (s : S) → ⌊ᵗ C ⸴ s ᵗ⌋ × ⟪ P ⟫ C ⟪ Q ⟫


{-
  '⟪_⟫_⟪_⟫ :  𝐴 → C → 𝐴 → Set
  '⟪ P ⟫ C ⟪ Q ⟫ = Σ S (λ s → Σ⊢ s P × (ϕ : ⌊ᵗ C ⸴ s ᵗ⌋) → Σ⊢ (‵ ϕ) Q)
-}

  -- Fixing a P is the same as fixing an S, this is what we want
  -- as P, as the precondition, defines the acceptable starting states.

  -- the type ℕ is supposed to capture all possible natural numbers
  -- the type ⟪_⟫_⟪_⟫ :  𝐴 → C → 𝐴 → Set is supposed to caputer
  -- the set of all Hoare triples. What is a Hoare triple?
  -- Well, it is a Predicate P, that guarantees termination
  -- of.... IT IS THE SET OF ALL P THAT GUARANTEE TERMINATION OF S IN Q
  -- So the definitions above more or less capture the notion of the WP


  ------- THIS PAR MIGHT NEED RETHINK
  -- * NO DUHHHH, triple = P ⇒ 𝑤𝑝(S,R)
  -- Syntacticly this is not quite the WP * as outlined in Dijkstra as
  -- Dijkstra identifies the WP as the singular predicate that
  -- identifies the possible starting states (with two predicates
  -- that both identify the same starting state being taken
  -- as identical, a luxury not given for free in Agda where
  -- the equivalence of 'x == 1 ^ y == 1' and 'y == 1 ^ x == 1'
  -- with respect to the state spaces they both capture would
  -- have to be proved; fortunately there is no need within the
  -- current scope of the project for us to do so.

  -- So the P in ⟪ P ⟫ x := y / x ⟪ Q ⟫ could be 'x != 0' the true
  -- WP, but it could also be 'x == 7', which only implies the WP.

  -- Nonetheless we can see that semantically the notion of WP is
  -- captured within our definition of hoare triples if we look
  -- at '( s : S ) → Σ⊢ s P' as one semantic unit that defines
  -- a subset of S.
  
  -- * n.b. that 'Σ⊢ s P' unpacks to 'P is a proposition (all variables
  -- are defined and no div by zero error, i.e. P is WFF) and that
  -- proposition is true'

  -- And, P ⇒ wp(S,Q) when seen as predicates specifying
  -- sets of states, is equivalent to P ⊆ wp(C,Q)
  -- e.g. if S = 'x ≔ 2/x'
  -- then wp(S,Q) = `Σ x. x != 0` (i.e. all S where that is the case)
  -- P might be `Σ x. x = 7` which of course implies wp(S,Q)
  -- The set of all states that satisfy P, will of course be a subset
  -- of the states that satisfy wp(C,Q)



  -- THIS ISN'T AN IMPORTANT QUESTION. THIS IS WAY OFF SCOPE
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

{- NOT SURE WHERE TO PLACE THIS
  THE POINT OF THE 𝑤𝑝 PROPERTIES, OVER ALL S (mechanism), IS TO
  KEEP US HONEST AND MAKE SURE THAT OUR PREDICATE TRANSFORMERS
  THAT MAKE UP OUR LANGUAGE ALWAYS SATISFY PROPERTIES 1-4 IN
  DIJKSTRA, IF THEY DID NOT THEN WE WOULD SIMPLY BE 'MASSAGING
  PREDICATES' IN A WAY THAT DIDN'T PRESERVE THE NOTION OF 
  PRE/POST-CONDITION-NESS
-}

  -- !!!!!
  -- We might want to ask if we can also formalise the properties of the 𝑤𝑝
  -- as outlined in Dijkstra and Gries, but doing so will prove difficult
  -- as while ⟦ P ⟧ S ⟦ Q ⟧ is semantically equivalent to P ⇒ 𝑤𝑝(S,Q), we
  -- have not actually formalised the notion of 𝑤𝑝 for all possible S.
  
  -- In fact we only have it formalised for the assignment mechanism in
  -- the form of the sub function. 𝑤𝑝( i := e ； , R ) = sub e i R.
  -- For the rest of the mechanisms we have skipped formalising
  -- 𝒘𝑝 for them and gone straight to formalising the theorems/rules that
  -- make reasoning about the mechanisms easier.
  
  -- Formalising --- read, explicitly constructing --- 𝑤𝑝(S,R) for all S,R
  -- would likely, as Dijkstra puts it, 'defy the size of our
  -- sheet of paper, our patience, or our (analytical) ingenuity' with our
  -- 'sheet of paper' in this case being agda; this is not to say that it
  -- could not be done, but it would be exceedingly cumbersome.
  -- !!!!!

  -- As an example of this difficulty we could examine the first
  -- propert, the so called, law of the excluded miracle:

  -------------------------------------------------------
  -- Law of the Excluded Miracle

  -- A first attempt to formalise this may result in
  -- the following signature:

  P1 : ∀ M P → ⟦ P ⟧ M ⟦ 𝐹 ⟧ → P ≡ 𝐹
  P1 s P h = {!!}

  -- This isn't quite right however and wouldn't be
  -- provable as 𝐹 in [Dijkstra] is shorthand for
  -- both 'the predicate that is always 𝐹' and
  -- therefore the ∅ when considered as a state space.

  -- This handwaving isn't available to us
  -- with our deep embedding however as 𝐹 isn't the
  -- only 𝐴 that fails to capture any states.
  -- Any 𝐴 that is an ill-formed formula
  -- also corresponds to the ∅. This is a
  -- consequence of not including domain(P) etc.
  -- in our embedding.
  --
  -- So we need a mechanism to relate all P
  -- that define ∅.
  -- i.e. 'x == 1/0' ≃ 𝐹 ≃ 'x ≤ y ^ x ∉ S'

  -- We can do this with the following:
  record _=𝐹 (P : 𝐴) : Set where
    field
      is𝐹  : (s : S) → Σ⊢ s P → ⊥
  open _=𝐹 public

  record _=𝑇 (P : 𝐴) : Set where
    field
      is𝑇  : (s : S) → Σ⊢ s P
  open _=𝑇 public

  -- And now we can fairly tivially formalise the
  -- law of the excluded miracle like so:
  P1' : ∀ C P Q → (Q =𝐹) → ⟦ P ⟧ C ⟦ Q ⟧ → (P =𝐹)
  P1' C P Q Q=𝐹 tc = record { is𝐹 = λ s ⊢P  →
     let t = proj₁ (tc s)  in
     let pc = proj₂ (tc s) in
     let ⊢Q = pc s ⊢P t    in
     is𝐹 Q=𝐹 (‵ (proj₁ (tc s))) ⊢Q }

  -- Monotonicity
  -- The difficulties continue however as there's no
  -- discernable way to prove the following.
  P2 : ∀ {C} {P} {P'} {Q} {R}
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ --  
     → Q ⇒ R → ⟦ P ⟧ C ⟦ Q ⟧ → ⟦ P' ⟧ C ⟦ R ⟧
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ --
                                     → P ⇒ P'
  P2 Q⇒R h₁ h₂ = {!!}
  -- Again we find that our first attempt at a formulation
  -- isn't quite right as if we take `P' == 𝐹` and P and Q
  -- to be such that P captures any non-empty statespace
  -- then we have a contradiction in P ⇒ P' (P ⇒ 𝐹)

  -- The problem is that at the type level, P in
  -- ⟦ P ⟧ S ⟦ Q ⟧ doesn't represent 𝑤𝑝(S,Q) but
  -- rather all P s.t. P ⊆ 𝑤𝑝(S,Q).
  
  -- Under the current formalisation, we have no way
  -- of grapling with 𝑤𝑝 as an object in and
  -- of itself except in the case of the single assignment
  -- operator. 

  -- Formalising all 𝑤𝑝 in an even more comprehensive deep embedding
  -- of propositional logic  would take us one step removed from the
  -- scope of the project
  -- as we would then be formalising the consistency of the 𝑤𝑝 as a means
  -- by which to describe programming constructs, rather than formalising
  -- the rules/theorems by which pre and post conditions are manipulated
  -- within the Hoare Logic proof calculus.

  -- The further properties may or may not be within reach of our
  -- formalisation but are left alone for now for future work.

  -- property 3:

  P3 : ∀ {C} {P} {P'} {Q} {R}
         →  ( ⟦ P ⟧ C ⟦ Q ⟧ × ⟦ P' ⟧ C ⟦ R ⟧ )
         ⇔  ⟦ P ∧ P' ⟧ C ⟦ Q ∧ R ⟧
  P3 {C} {P} {P'} {Q} {R} = {!!}
