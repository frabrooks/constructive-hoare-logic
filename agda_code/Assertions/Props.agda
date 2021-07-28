


-- Lib imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_  ; inspect ; Reveal_·_is_ ; refl ; subst ; sym )
open import Data.Maybe using ( Maybe ; just ; nothing ; Is-just )
open import Relation.Nullary using ( yes ;  no )
open import Data.Sum
open import Data.Unit using ( ⊤ ; tt )
open import Data.Empty using ( ⊥ ; ⊥-elim )
open import Data.Bool
open import Data.Product using (Σ ; Σ-syntax ; _×_  ; _,_  ; proj₁ ; proj₂ )
open import Function using ( _∋_ ; _∘_ ; _$_ )

-- Local imports
open import Representation.Data using (Data-Implementation)
open import Representation.State using (S-Representation)
open import Misc

module Assertions.Props ( 𝔡 : Data-Implementation )
  (sRep : S-Representation 𝔡 ) where

  open Data-Implementation 𝔡
  open S-Representation sRep
  
  -- Using the same expression language as the
  -- Mini-C language itself at the moment,
  -- This may need to change later
  open import Mini-C.Expressions 𝔡 sRep 


  -- Assertions (𝐴) are a synonym for expressions.
  𝐴 = Exp
  -- This does allow for some assertions that we
  -- would not normally perhaps consider as
  -- assertions such as (2 + 1) or (x * 5).
  -- But as per in C, C++, and many other
  -- languages with implicit casting from Ints
  -- to truth values / booleans: (2 + 1),
  -- rendered as an exp as:
  --    (op₂ (𝑐𝑜𝑛𝑠𝑡 ➋) (+𝓿 :𝕍) (𝑐𝑜𝑛𝑠𝑡 ➊)),
  -- is a perfectly valid truth value and could
  -- be used as a conditional (one that always
  -- evaluates to true)

  -- The next question we can ask is:
  -- What is the relationship between assertions,
  -- predicates and propositions?

  -- A predicate is an assertion 𝐴 for which there exists
  -- some state S s.t. 𝐴 is a WFF. In other words it
  -- is a subset of states.
  -- e.g. (op₂ (𝑣𝑎𝑟 𝔁) (/𝓿 :𝕍) (𝑐𝑜𝑛𝑠𝑡 0)) is not a valid
  -- predicate as no state exists in which that is a WFF,
  -- but (op₂ (𝑣𝑎𝑟 𝔁) (/𝓿 :𝕍) (𝑣𝑎𝑟 𝔂)) is a predicate even
  -- it will not be a WFF in any state in which 𝔂 := 0 
  𝑃𝑟𝑒𝑑𝑖𝑐𝑎𝑡𝑒 : 𝐴 → Set
  𝑃𝑟𝑒𝑑𝑖𝑐𝑎𝑡𝑒 p = Σ S (WFF ∘ evalExp p)
  -- This type represents the set of all predicates
  -- which isn't very practical to work with

  -- 𝑃 can be read as 'proposition'
  -- an assertion is only valid as a
  -- proposition in the states in
  -- which it is a WFF. i.e.
  -- every WFF is a Proposition with
  -- truth value defined by 'toTruthValue'
  𝑃𝑟𝑜𝑝𝑜𝑠𝑡𝑖𝑜𝑛 : 𝐴 → S → Set
  𝑃𝑟𝑜𝑝𝑜𝑠𝑡𝑖𝑜𝑛 e s = WFF (evalExp e s)
  -- This type actually represents 𝑃𝑟𝑒𝑑𝑖𝑐𝑎𝑡𝑒s!!

  -- Alternative condensed syntax
  𝑃 : 𝐴 → S → Set
  𝑃 e s = 𝑃𝑟𝑜𝑝𝑜𝑠𝑡𝑖𝑜𝑛 e s


  -- Assertion
  -- Wrong: (that proposition is true)
  -- Actually, this asserts that an
  -- assertion IS a proposition and that
  -- that proposition is true
  -- Assert : 𝐴 → S → Set
  -- Assert A s = Σ (𝑃 A s) (λ prop
  --        → T $ toTruthValue prop )

  Assert : ∀ {s} {A} → 𝑃 A s → Set
  Assert = T ∘ toTruthValue


  -- Alternative syntax
  ⊢ : ∀ {s A} → 𝑃 A s → Set
  ⊢ {s} {A} = Assert {s} {A}

  
  -- This terminolgy is necessary due to the
  -- fact that propositions are only a
  -- subset of (Assertions × States)
  -- i.e. `Assertion → States → TruthValue` is
  -- a partial function.
  AssertΣ : ∀ s A → Set
  AssertΣ s A = Σ (𝑃 A s) (T ∘ toTruthValue)

  Σ⊢ : ∀ s A → Set
  Σ⊢ = AssertΣ

  -- Alternative syntax
  -- Not sure this syntax is necessary anymore!
  -- _←_ : ∀ {s A} → 𝑃 A s → Set
  -- A ← s = Σ (𝑃 A s) (Assert {s} {A})


  -- What it means for one assertion to imply another
  -- The alternative way this can be read is: 'the
  -- subset of the state space S defined by P, is
  -- itself a subset of the subset defined by Q.'
  --_⇒_ : ∀ {p q : 𝐴} → 𝑃𝑟𝑒𝑑𝑖𝑐𝑎𝑡𝑒 p → 𝑃𝑟𝑒𝑑𝑖𝑐𝑎𝑡𝑒 q → Set
  --_⇒_ {p} {q} P Q =  Assert {p} P → Assert {q} Q
  -- THIS IS nonsense


  ₐₜ_⸴_⸴_∶_⇒_ : (a₁ a₂ : 𝐴) → (s : S) → 𝑃 a₁ s → 𝑃 a₂ s → Set
  ₐₜ a₁ ⸴ a₂ ⸴ s ∶ P ⇒ Q = Assert {s} {a₁} P → Assert {s} {a₂} Q


  -- P ⇒ Q : For all states, if P
  -- is a WFF at that state that is
  -- true then, Q is also a WFF at that
  -- state that is true.
  _⇒_ : (a₁ a₂ : 𝐴) → Set
  P ⇒ Q = (s : S)
          → Σ[ 𝒫 ∈ 𝑃 P s ] ⊢ {s} {P} 𝒫
          → Σ[ 𝒬 ∈ 𝑃 Q s ] ⊢ {s} {Q} 𝒬


  -- _⇒_ : 𝐴 → 𝐴 → Set
  -- P ⇒ Q = (s : S) → Assert P s → Assert Q s

  a₁ : 𝐴
  a₁ = (op₂
       (op₂ (𝑣𝑎𝑟 𝔁) ==  (𝑐𝑜𝑛𝑠𝑡 ➋))
                    &&
       (op₂ (𝑐𝑜𝑛𝑠𝑡 ➊) == (𝑐𝑜𝑛𝑠𝑡 ➊)))

  a₂ : 𝐴
  a₂ = (op₂ (𝑣𝑎𝑟 𝔁) == (𝑐𝑜𝑛𝑠𝑡 ➋))

  --𝒫 : 𝑃 e1
  --𝒫 = (updateState 𝔁 _ ●) , subst (λ a → WFF (( a ==𝓿 just ➋) &&𝓿 (just ➊ ==𝓿 just ➊)) ) (sym (updateGet 𝔁 ➊ ●)) {!!}


  --𝒬 : 𝑃 e2
  --𝒬 = {!!}


  test : a₁ ⇒ a₂
  test  s ⊢x&y = let x = getVarVal 𝔁 s ==𝓿 (just ➋) in
                 let y = just ➊ ==𝓿 just ➊  in
                 ConjunctionElim₁ x y ⊢x&y

{-
λ P=T → let lhs = getVarVal 𝔁 s ==𝓿 (just ➋) in
               let rhs = just ➊ ==𝓿 just ➊  in
               {!!}
               -- proj₂ (ConjunctionElim₁ lhs rhs ? )
-}
  {-   getVarVal 𝔁 (updateState 𝔁 _52 ●)
  test : 𝒫 ⇒ 𝒬
  test s (wffe1 , isT) =
    let lhs = getVarVal 𝔁 s ==𝓿 (just ➋) in
    let rhs = just ➊ ==𝓿 just ➊  in
    let wffe2 = (proj₁ (wffₒᵤₜ⇒wffᵢₙ  lhs &&𝓿₂ rhs wffe1))
    in ( wffe2 , ConjunctionElim₁ lhs rhs wffe1 isT wffe2 )
  -}

  sub : Exp → Id → Exp → Exp
  sub e' id (op₂ l ∙ r) = let lhs = sub e' id l in
                             let rhs = sub e' id r in
                             (op₂ lhs ∙ rhs)
  sub e' id (op₁ ∙ e) = op₁ ∙ (sub e' id e)
  sub e' id e@(term (Const x)) = e
  sub e' id e@(term 𝒕) = e
  sub e' id e@(term 𝒇) = e
  -- This is where the substitution happens:
  sub e' id e@(term (Var id')) with id ?id= id'
  ... | yes _ = e'
  ... | no  _ = e




