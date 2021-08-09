
-- Lib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_  ; _≢_ ; inspect ; Reveal_·_is_ ; refl ; subst ; sym )
open import Data.Maybe using ( Maybe ; just ; nothing ; Is-just )
open import Relation.Nullary using ( yes ;  no )
open import Data.Sum
open import Data.Unit using ( ⊤ ; tt )
open import Data.Empty using ( ⊥ ; ⊥-elim )
open import Data.Bool hiding ( _∧_ )
open import Data.Product using (Σ ; Σ-syntax ; _×_  ; _,_  ; proj₁ ; proj₂ )
open import Function using ( _∋_ ; _∘_ ; _$_ )

-- Local imports
open import Data-Interface using (Data-Implementation)
open import State-Interface using (State-Implementation)
open import Misc

module Language.Assertions
  ( 𝔡 : Data-Implementation )
  ( 𝔖 : State-Implementation 𝔡 ) where

  open Data-Implementation 𝔡
  open State-Implementation 𝔖
  
  open import Language.Expressions 𝔡 𝔖
  
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  -- Assertions(𝐴)/Conditions are just expressions from our Mini-Imp language.
  
  Assertion = Exp

  -- These assertions are to be manipulated using the deeply embedded logical
  -- rules defined in the 𝐷𝑎𝑡𝑎-𝐼𝑛𝑡𝑒𝑟𝑓𝑎𝑐𝑒.𝑎𝑔𝑑𝑎 and potentially implemented in 𝔡.
  -- For example, all data implementations 𝔡 must prove De Morgan's laws.
  --
  -- The limitation of this methodology, of having a deep embedding of not just
  -- the Mini-Imp language but also of the expression language itself, is that
  -- all the logical rules through which assertions are to be manipulated need
  -- be declared. This is why 𝐷𝑎𝑡𝑎-𝐼𝑛𝑡𝑒𝑟𝑓𝑎𝑐𝑒.𝑎𝑔𝑑𝑎 exists, to allow the use of
  -- logical manipulations such as De Morgan's laws, or the commutativity of
  -- the && operator, while allowing one to forestall - perhaps indefinitely
  -- depending on the scope of the user's current formalisation - the burden
  -- of proving these rules.


  -- Assertions as Mini-Imp Expressions does allow for some unusual assertions
  -- that may raise an eyebrow. What do the assertions (2 + 1) or (𝑥 * 5) mean?
  -- The problem is that there needs to be a one-to-one correspondence between
  -- the way the expressions are interpreted in a program, and in an assertion.
  --
  -- An incredibly baroque solution to this problem would be enforcing a type
  -- system, that distinguishes between Boolean variables and Integer variables,
  -- within the deep embedding of Mini-Imp and 𝐸𝑥𝑝𝑟𝑒𝑠𝑠𝑖𝑜𝑛𝑠.𝑎𝑔𝑑𝑎. The alternative
  -- much simpler solution is to assume implicit casting between Ints and Bools
  -- within both the language and the assertions, drastically simplifying both.
  --
  -- A la C, C++, and many other languages with implicit casting, any non-zero
  -- integer is taken to have truth-value 𝑇, and zero, a truth-value of 𝐹. Thus
  -- the expressions (2 + 4) and (4 * 0) are valid assertions having constant
  -- values 𝑇 and 𝐹 respectively.




  -- The next complication involves the handling of stuck expressions. Is the
  -- assertion (𝑥 == (𝑦 / 0)) equal to 𝐹? Is it even an Assertion?
  --
  -- The assertions in Hoare Logic (or assertions in general) are understood to
  -- be boolean-valued functions over the state space, but with the present deep
  -- embedding of the expression language 
  -- we have lost this understanding as each assertion/expression is only
  -- a partial function of the state space.
  --
  -- This is a problem often brushed aside casually - if mentioned at all - in
  -- typical expositions of the subject. 
  --
  -- One can see why --- any sensible programmer will avoid writing code where     
  -- the non-zero-ness of a divisor is not obvious. Indeed, it is non-trivial       
  -- to even intentionally design a program that would be likely to fall afoul     
  -- of an erroneous proof while reasoning about it using this library.
  -- Nonetheless, in a constructive formalisation such as this one,
  -- sweaping things under the table is not an option nor desirable so the
  -- complication must be addressed.
  --
  -- The source of this complication is that not all the assertions we can form
  -- 𝑠𝑦𝑛𝑡𝑎𝑐𝑡𝑖𝑐𝑎𝑙𝑙𝑦 make sense 𝑠𝑒𝑚𝑎𝑛𝑡𝑖𝑐𝑎𝑙𝑙𝑦 - that is, not all expressions are
  -- 𝑊𝑒𝑙𝑙-𝐹𝑜𝑟𝑚𝑒𝑑-𝐹𝑜𝑟𝑚𝑢𝑙𝑎; (1 / 0) is an assertion we can write that has no
  -- meaning, even with implicit casting to boolean values, it is `stuck' - just
  -- as the C expression `𝑥++;' is a valid C expression 𝑠𝑦𝑛𝑡𝑎𝑐𝑡𝑖𝑐𝑎𝑙𝑙𝑦, but has
  -- no meaning 𝑠𝑒𝑚𝑎𝑛𝑡𝑖𝑐𝑎𝑙𝑙𝑦 if 𝑥 is a float.
  --
  -- Semantically, this problem is resolved in [1] by introducing a predicate
  -- into the expression/assertion language of the form 𝐷(𝐸) which returns true
  -- when the given state lies within the domain of the expression/assertion 𝐸.
  -- The weakest precondition of the assignment mechanism is then written as:
  --
  --             𝑤𝑝( 𝑥 := 𝐸 , 𝑅 ) = { 𝐷(𝐸) 𝒄𝒂𝒏𝒅* (sub 𝐸 𝑥 𝑅) } 
  --
  --                                                            * conditional &&
  --
  -- In essence, the semantics are changed so that any stuck assertion
  -- will be rendered as false.
  --
  -- From the perspective of Hoare logic - from outside the deep embedding -
  -- this simple solution of treating stuck expressions as equal to 𝐹 seems
  -- reasonable, we only care that assertions/pre-post-conditions are true
  -- - not the conditions under which they fail to be so. The assertion
  -- (𝑥 == (𝑦 / 0)) doesn't capture any non-empty subset of the state space
  -- just as 𝐹 doesn't. Indeed, equating 𝐹 and all stuck expressions does not
  -- break any of the properties of 𝑤𝑝 outlined in [1]/[2] that ensure 𝑤𝑝 is
  -- `well-behaved.'
  --
  -- So the question of how stuck expressions are to be treated 𝑠𝑒𝑚𝑎𝑛𝑡𝑖𝑐𝑎𝑙𝑙𝑦 has
  -- been answered, but this doesn't answer the question of how to handle the
  -- issue 𝑠𝑦𝑛𝑡𝑎𝑐𝑡𝑖𝑐𝑎𝑙𝑙𝑦 within this formalisation.
  --
  -- 𝐷(𝐸) could well be formalised for the expression language in its current
  -- form: it would be a conceptually simple, yet fiddly to implement, function
  -- that produces for input 𝐸 the expression/assertion of form:
  --
  --                            `𝑇 ∧ 𝑋₁ ∧ 𝑋₂ ∧ 𝑋₃ ⋯ 𝑋ₙ'
  --
  -- where for all variables 𝑥 in 𝐸 there is a 𝑋ᵢ of form `Σ. 𝑥' (𝑥 is defined
  -- in S), and for each `𝐸′ / 𝐸″' / `𝐸′ % 𝐸″' in 𝐸 there is an 𝑋ᵢ of form
  -- `¬ (𝐸″ == 0)', such a function would be baroque but computable.
  --
  -- However, all functions in Agda must be total and the introduction of 𝐷(𝐸)
  -- does nothing to restrict someone using this library from forming assertions
  -- that are only partial functions of the state space. To prevent this the
  -- definition of Expression/Assertion would have to change to have an implicit
  -- 𝐷(𝐸) at the beginning of each expression and then each expression would
  -- also form a valid assertion that defines a total function of state space to
  -- bool (S → Bool) - but doing so would also change the semantics of the
  -- Mini-Imp language.
  --
  -- It is undesirable to have `(𝑥 == (𝑦 / 0)) = 𝐹' to be true 𝑤𝑖𝑡ℎ𝑖𝑛
  -- the deep embedding of the expression language, as this would also make
  -- it true within the Mini-Imp language with which users of the library
  -- are to form the programs they want to reason about and no sensible
  -- language should allow `𝔦𝔣 ( ¬ (𝑥 == (𝑦 / 0))) ⋯ ' to evaluate* - not to
  -- mention the fact that this would be a deviation from the intent outlined
  -- in the specification for the Mini-Imp language to closely mirror C**.


  -- * what on earth would it even evaluate to?
  -- ** C has no ability to to check if a variable has been defined as 𝐷(𝐸) does

  -- So we want a system that looks something like the following:

  -- insert picture of:

  --                        (𝑥 == (𝑦 / 0)) = 𝐹 = ∅ = 0
  --                  ↓                                              ↑
  --        ----------↓---- 𝐷𝑎𝑡𝑎-𝐼𝑛𝑡𝑒𝑟𝑓𝑎𝑐𝑒.𝑎𝑔𝑑𝑎 / Deep Embedding ----↑--------- 
  --
  --                       (𝑥 == (𝑦 / 0)) = ⊥ = nothing
  --                          𝐹 = 0 = 4 * 0 ⋯



  -- That is, `under the hood', we should only be dealing and reasoning about
  -- expressions that are WFF (non-stuck) and some expressions are allowed to
  -- have no meaning.
  -- Meanwhile, outside of the deep embedding while using Hoare Logic, we assign
  -- all stuck expressions with the meaning 𝐹. We just need a way of determining
  -- whether a given assertion 𝐴, is a 𝑊𝐹𝐹 at a given state s (`𝑊𝐹𝐹ₛ(𝐴)').
  -- Rather than any baroque solution involving some modification of the
  -- Expression Language or some function that 𝑖𝑛𝑠𝑝𝑒𝑐𝑡𝑠 a given expression to
  -- determine well-formed-ness, a much simpler implementation is available.
  --
  -- As evaluation of expressions is also to be formalised within the deep
  -- embedding - an expression will be `well-formed' so long as it evaluates.
  -- So long as the evalExp function has the option to return nothing, then
  -- the predicate `𝑊𝐹𝐹ₛ(𝐸)', can be implemented as `Is-just (evalExp 𝐸 s)'.
  -- Thus, all 𝑊𝐹𝐹 in the expression language, can be cast to a boolean value,
  -- and are therefore propositions that can direct the flow of computation.

  
  𝑊𝐹𝐹 : Assertion → S → Set
  𝑊𝐹𝐹 a s = Is-just (evalExp a s)


  -- While reasoning with Hoare-Logic now --- i.e. outside of our deep embedding
  -- using Agda's logical apparatus --- we can now represent an assertion proper
  -- as:

  Assert : ∀ s A → Set
  Assert s A = Σ (𝑊𝐹𝐹 A s) (T ∘ toTruthValue)

  -- Alternative, condensed syntax*
  _⊨_ : ∀ s A → Set
  _⊨_ = Assert

  -- The use of `⊨' to represent here and `⊢' in 𝐷𝑎𝑡𝑎-𝐼𝑛𝑡𝑒𝑟𝑓𝑎𝑐𝑒.𝑎𝑔𝑑𝑎 may be a
  -- little different to standard practice, semantic and syntactic entailment :
  -- distinction between WFF and 𝑊𝐹𝐹


  -- We can now encode what it means for one Assertion to imply another like so:
  
  _⇒_ : Assertion → Assertion → Set
  P ⇒ Q = (s : S) → s ⊨ P → s ⊨ Q


  -- Allowing reasoning/manipulation of assertions like so:

  -- 𝑥 == 2 ∧ 𝑦 == 1
  private a₁ : Assertion
  a₁ = ((𝑣𝑎𝑙 𝒙) == (𝑐𝑜𝑛𝑠𝑡 ②))
       ∧
       ((𝑣𝑎𝑙 𝒚) == (𝑐𝑜𝑛𝑠𝑡 ①))

  -- x == 2
  private a₂ : Assertion
  a₂ = (𝑣𝑎𝑙 𝒙) == (𝑐𝑜𝑛𝑠𝑡 ②)

  inferenceExample : a₁ ⇒ a₂
  inferenceExample  s ⊨x&y = let x = getVarVal 𝒙 s ==𝓿 (just ②) in
                             let y = getVarVal 𝒚 s ==𝓿 (just ①)  in
                             ConjunctionElim₁ x y ⊨x&y


 -- Refs
    -- [1] - E. W. Dijkstra, A Discipline of Programming, 1976
    -- [2] - D. Gries, The Science of Programming, 1981
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━


