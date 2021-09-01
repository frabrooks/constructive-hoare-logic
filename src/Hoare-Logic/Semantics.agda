
-- Lib Imports
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl ; sym)
open import Data.Product using (Σ)

-- Local Imports
open import Data-Interface using (Data-Implementation)
open import State-Interface using (State-Implementation)

open import Misc

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Hoare-Logic.Semantics ( 𝔡 : Data-Implementation )
  (𝔖 : State-Implementation 𝔡 ) where

  -- Local Dependent Imports
  open Data-Implementation 𝔡
  open State-Implementation 𝔖
  open import Language.Expressions 𝔡 𝔖
  open import Language.Assertions 𝔡 𝔖
  open import Language.Mini-Imp 𝔡 𝔖
  open import Evaluation.Termination 𝔡 𝔖

  -- ════════════════════════════════════════════════════════════════════════════
  -- Hoare Triples
  --
  -- Partial Correctness:
  ⟪_⟫_⟪_⟫ :  Assertion → C → Assertion → Set
  ⟪ P ⟫ C ⟪ Q ⟫ = ( s : S ) → s ⊨ P → (ϕ : ⌊ᵗ C ⸴ s ᵗ⌋) → (‵ ϕ) ⊨ Q
  -- For all states s, if s satisfies P, and if we have a constructive proof of
  -- termination of C in state s, then Q will be true for the resultant state.
  
  -- n.b.  This type signature admits 𝐹 as a valid precondition of all programs
  --       and postconditions a la the absurd function.
  
  -- n.b.  `⊨ s 𝐴' unpacks to `Σ (𝑃 𝐴 s) (T ∘ toTruthValue)', or in prose:   
  --       `The assertion 𝐴 at s denotes a valid proposition/𝑊𝐹𝐹 (i.e. all
  --       variables are defined in s and no there is no divide by zero error)
  --       and the truth value of that proposition/𝑊𝐹𝐹 is True'


  -- Total Correctness which is partial correctness + a proof of termination.
  ⟦_⟧_⟦_⟧ :  Assertion → C → Assertion → Set
  ⟦ P ⟧ C ⟦ Q ⟧ = ( s : S ) → s ⊨ P → Σ ⌊ᵗ C ⸴ s ᵗ⌋ (λ ϕ → (‵ ϕ) ⊨ Q)

  -- n.b. that the above definitions relate to the notions of the Weakest
  --      Precondition and the Weakest Liberal Precondtion of a program 𝐶
  --      for postcondition 𝑄, as described in [1] and [2]*, as follows:
  --
  --                  ⟦ 𝑃 ⟧ 𝐶 ⟦ 𝑄 ⟧   ⇔   𝑃 ⇒ 𝑤𝑝(𝐶,𝑄)
  --                  ⟪ 𝑃 ⟫ 𝐶 ⟪ 𝑄 ⟫   ⇔   𝑃 ⇒ 𝑤𝑙𝑝(𝐶,𝑄)
  --                                                                *(see below)

  -- A note on notation:
    -- Hoare's original notation was 𝑃 { 𝐶 } 𝑄 to denote partial correctness but
    -- { 𝑃 } 𝐶 { 𝑄 } is now more common; however, no standard notation exits.
    -- The notation in Gries[2] actually reserves { 𝑃 } 𝐶 { 𝑄 } to denote 𝑡𝑜𝑡𝑎𝑙
    -- correctness and 𝑃 {𝐶} 𝑄 to denote partial correctness. Here then, as '{}'
    -- is reserved for Agda's syntax, I introduce the use of ⟪⟫ and ⟦⟧ bracketed
    -- triples for partial and total correctness respectively.

  -- ════════════════════════════════════════════════════════════════════════════
  -- Relation to Weakest Precondition / Weakest Liberal Precondition:

  -- In Dijkstra[1], the notion of a 𝑤𝑒𝑎𝑘𝑒𝑠𝑡 𝑝𝑟𝑒𝑐𝑜𝑛𝑑𝑖𝑡𝑖𝑜𝑛 (𝑤𝑝) and a weakest
  -- 𝑙𝑖𝑏𝑒𝑟𝑎𝑙 precondition (𝑤𝑙𝑝) are defined as a means of giving semantics to
  -- programming language constructs. Each is characterised as a predicate
  -- transformer that, for a given construct, transforms a desired postcondition
  -- into the corresponding precondition that in the case of:
  --
  --         𝑤𝑝: is the condition that captures all states from which we can
  --             guarantee termination of the mechanism 𝑎𝑛𝑑 that the resultant
  --             state satisfies the postcondition.
  --
  --        𝑤𝑙𝑝: alternatively, is the condition the input state must satisfy
  --             to guarantee that the resultant state satisfies the
  --             postcondition, but only 𝑖𝑓 the mechanism terminates.
  --             
  -- Hoare triples 'under the hood' can be seen as statements in the underlying
  -- predicate calculus. A precondition for a mechanism 𝐶 and postcondition 𝑄
  -- is actually a predicate 𝑃 s.t. 𝑃 ⇒ 𝑤𝑝(𝐶,𝑄) , or 𝑃 ⇒ 𝑤𝑙𝑝(𝐶,𝑄) depending
  -- on whether or not the precondition is a partial-precondition (⟪⟫) or a
  -- total-precondition (⟦⟧).
  --
  -- Speaking of the 'underlying predicate calculus', predicates/assertions can
  -- be viewed in two ways; as predicates or as the subset of the state space
  -- that they capture: e.g `𝑃 ⇒ 𝑤𝑝(𝐶,𝑄) ⇒ 𝑇' ⇔ `𝑃 ⊆ 𝑤𝑝(𝐶,𝑄) ⊆ S'.
  --
  -- Normally there would be no need to distinguish between the two different
  -- views and both could be kept in mind and used interchangeably a la [1].
  -- However, in a syntax driven, constructive formalisation, this absence of
  -- specificity is not an option nor desirable.
  -- 
  -- This means that, as far as pre and post conditions are concerned, the
  -- predicates `𝓍 && 𝓎' and `𝓎 && 𝓍' are distinguishable from one another.
  -- Their equivalence with respect to the states spaces they describe is
  -- something we would need to prove; which in this case would ammount to
  -- proving the commutativity of the && operator as it has been defined.
  
  -- ════════════════════════════════════════════════════════════════════════════
  -- Properties of 𝑤𝑝 and 𝑤𝑙𝑝:
  --
  -- In [1] Dijkstra outlines some properties that the notion of 𝑤𝑝 and 𝑤𝑙𝑝
  -- must satisfy for them to make sense as a means of giving semantics to a
  -- mechanism and or programming construct. Failure to satisfy these properties
  -- would mean we were no longer manipulating pre/post-conditions but
  -- instead were just 'massaging predicates' as Dijkstra puts it.
  --
  -- These properties are proved classically in [1] but given the scope of this
  -- project, it seemed natural to consider including these properties in the
  -- formalisation as well as a means of sanity checking the formalisations
  -- of the Mini-Imp mechanisms that have been defined.
  --
  -- However, the constructs/mechanisms that have been formalised (:=,
  -- 𝔦𝔣_𝔱𝔥𝔢𝔫_𝔢𝔩𝔰𝔢_, 𝔴𝔥𝔦𝔩𝔢_𝔡𝔬 ⋯) have been formalised in terms of how they are to
  -- be executed, which is precisely the approach to defining programming
  -- constructs that the notion of 𝑤𝑝  and 𝑤𝑙𝑝 were trying to avoid by instead
  -- defining them in terms of their 𝑤𝑝/𝑤𝑙𝑝. So there is an incongruency there.
  -- 
  -- The only mechanism for which the 𝑤𝑝/𝑤𝑙𝑝 has been formalised is the
  -- assignment (`:=') mechanism via the `sub' function in 𝐴𝑠𝑠𝑒𝑟𝑡𝑖𝑜𝑛𝑠.𝑎𝑔𝑑𝑎.
  -- e.g.
  --                 𝑤𝑝( 𝑖 := 𝑒 , 𝑅 ) = sub 𝑒 𝑖 𝑅
  --
  -- n.b. the equality above has not been formalised itself but the weaker fact
  -- that 𝑠𝑢𝑏 𝑒 𝑖 𝑅 ⇒ 𝑤𝑝( 𝑖 := 𝑒 , 𝑅 ) ℎ𝑎𝑠 been formalised in the form of
  -- D0-Axiom-of-Assignment in 𝑅𝑢𝑙𝑒𝑠.𝑎𝑔𝑑𝑎 and after some thought we can convince
  -- ourselves that 𝑠𝑢𝑏 𝑒 𝑖 𝑅 doesn't just 𝑖𝑚𝑝𝑙𝑦, but actually 𝑖𝑠 the 𝑤𝑝.
  -- One step towards this conviction comes from inspecting the type signature
  -- of D0 where it is clear that the definition depends on nothing other than
  -- the mechanism itself (𝑒, 𝑖), and the postcondition (𝑅):
  --
  --   D0-Axiom-of-assignment : ∀ 𝑖 𝑒 𝑅 → ⟪ 𝑠𝑢𝑏 𝑒 𝑖 𝑅 ⟫ 𝑖 := 𝑒 ⟪ 𝑅 ⟫
  --
  -- For the rest of the mechanisms, however, no attempt has been made to
  -- formalise their corresponding 𝑤𝑝/𝑤𝑙𝑝 as defined in [1]. The reason
  -- being that formalising --- read, explicitly constructing --- 𝑤𝑝(S,R)
  -- for all S,R would likely, as Dijkstra puts it, 'defy the size of our
  -- sheet of paper, our patience, or our (analytical) ingenuity' with our
  -- 'sheet of paper' in this case being Agda; this is not to say that it
  -- could not be done, but it would be exceedingly cumbersome.

  -- Nonetheless, it may be within reach to formalise the 𝑤𝑝-properties for
  -- just the 𝑤𝑝 that has been defined, viz the sub function. This turns out
  -- to be pretty trivial, taking property 1, the so called `Law of the
  -- Excluded Miracle' as a start:

  LawOfExcludedMiracle-𝑤𝑝⦅:=,-⦆ : ∀ {i e} → sub e i 𝐹 ≡ 𝐹
  LawOfExcludedMiracle-𝑤𝑝⦅:=,-⦆ = refl

  -- And for Property 2, Monotonicity:
  Monotonicity-𝑤𝑝⦅:=,-⦆ : ∀ P P' Q R i e
  
     → Q ⇒ R → sub i e R ≡ P → sub i e R ≡ P'
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ --
                                     → P ⇒ P'
                                     
  Monotonicity-𝑤𝑝⦅:=,-⦆ P P' Q R i e Q⇒R eq₁ eq₂  s x = go
    where
    go : s ⊨ P'
    go rewrite (sym eq₂) | (sym eq₁) = x

  -- The further properties may or may not be within reach of our formalisation
  -- but by this point it is clear that what is being formalised here is very
  -- far off scope for the project and not adding value to the project, so
  -- the exploration of formalising facets of weakest preconditions ends here.

  -- Refs
    -- [1] - E. W. Dijkstra, A Discipline of Programming, 1976
    -- [2] - D. Gries, The Science of Programming, 1981
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

