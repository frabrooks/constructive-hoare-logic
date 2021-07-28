


-- Lib imports
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; inspect ; [_] )
open import Data.Maybe using ( Maybe ; just ; nothing ; map ; _>>=_ ; Is-just ; to-witness )
open import Data.Maybe.Relation.Unary.Any using (Any)
open import Data.Bool using ( true ; false )
open import Relation.Nullary using (  yes ; no ; ¬_ ) 
open import Data.Product using (Σ ; Σ-syntax ; _×_  ; _,_  ; proj₁ ; proj₂ )
open import Data.Nat using (ℕ ; suc ; zero)
open import Data.Integer using (ℤ)
open ℤ
open import Data.Empty
open import Data.Unit using ( ⊤ ; tt )


-- Project imports
open import Representation.Data using (Data-Implementation )
open import Representation.State using (S-Representation)
open import Misc


module Mini-C.Evaluation (𝔡 : Data-Implementation )
  (sRep : S-Representation 𝔡 ) where

  open Data-Implementation 𝔡
  open S-Representation sRep

  open import Mini-C.Expressions 𝔡 sRep
  open import Mini-C.Lang 𝔡 sRep

  {-
  data _:=_|evalExp=_USING_GIVES_ : Id → Exp → Val → S → S →  Set where
    _:='_w/_andPExp : ∀ {v : Val} (id : Id) → (exp : Exp) → (s : S )
                        → (evalExp exp s) ≡ just v
                        → id := exp |evalExp= v USING s GIVES (updateState id v s)
  -}

  

  evalAssiVal : ∀ (id : Id ) ( v : Maybe Val ) → S → Maybe S
  -- Computation fail (e.g. S = nothing after ÷ by 0 error)
  evalAssiVal id nothing _ = nothing
  -- Computation success
  evalAssiVal id (just v) s = just (updateState id v s )

  {-
  Alt definitions 

  evalAssi'' : ∀ {i e} → S → (p : i := e) → Maybe S
  evalAssi'' s (id ꞉= exp) = evalAssiVal id (evalExp exp s) s

  evalAssiff : ∀ {i e} → S → (p : i := e) → Maybe S
  evalAssiff s (id ꞉= exp) with (evalExp exp s)
  ... | nothing = nothing
  ... | just x = just (updateState id x s)

  evalAssi' : ∀ {i e} → S → (p : i := e) → Maybe S
  evalAssi' s (id ꞉= exp) with evalExp exp s
  ... | nothing = nothing -- Comp failed. i.e. ÷ by 0 error
  ... | just v = just (updateState id v s) -- Comp success

  evalAssi' : ∀ {i e} → S → (p : i := e) → Maybe S
  evalAssi' s (id ꞉= exp) with evalExp exp s
  ... | nothing = nothing -- Comp failed. i.e. ÷ by 0 error
  ... | just v = just (updateState id v s) -- Comp success
  -}

  evalAssi : ∀ {i e} → S → (p : i := e) → Maybe S
  evalAssi s (id ꞉= exp) = map (λ v → updateState id v s) (evalExp exp s) 
  
-- 
  
  is-JustExp→is-JustAssi : ∀ {i e s} → WFF (evalExp e s) → WFF (evalAssi s (i ꞉= e))
  is-JustExp→is-JustAssi {i} {e} {s} p with (evalExp e s)
  ... | just _ = Any.just tt
  

  
  ssEvalwithFuel :  ℕ → 𝐶 × Maybe S → Maybe S
  -- Skip ⇒ eval finished successfully
  ssEvalwithFuel  zero     (𝑠𝑘𝑖𝑝 , s@(just _)) = s   
  ssEvalwithFuel  (suc _)  (𝑠𝑘𝑖𝑝 , s@(just _)) = s
  -- Skip fails on empty state
  ssEvalwithFuel  zero        (𝑠𝑘𝑖𝑝 , nothing) = nothing
  ssEvalwithFuel  (suc _)     (𝑠𝑘𝑖𝑝 , nothing) = nothing   

  -- Need to explicitly give all four cases here so
  -- Agda can see `eval zero C = c , nothing` is always
  -- definitionally true.
  ssEvalwithFuel zero (c@(𝑎𝑠𝑠𝑖꞉ x) , s) = nothing         -- ran out of fuel
  ssEvalwithFuel zero (c@(𝑠𝑒𝑞꞉ x) , s)  = nothing         -- ran out of fuel
  ssEvalwithFuel zero (c@(𝑐𝑡𝑟𝑙꞉ x) , s) = nothing         -- ran out of fuel
  ssEvalwithFuel zero (c@(𝑙𝑜𝑜𝑝꞉ x) , s) = nothing         -- ran out of fuel

  -- Assignment
  ssEvalwithFuel (suc n) (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) , nothing) = nothing 
  ssEvalwithFuel (suc n) (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) , (just s)) = evalAssi s (i ꞉= e)

  -- If then Else
  ssEvalwithFuel (suc n) ( c@(𝑐𝑡𝑟𝑙꞉ (𝑖𝑓 b 𝑡ℎ𝑒𝑛 c₁ 𝑒𝑙𝑠𝑒 c₂)) , nothing ) = nothing
  ssEvalwithFuel (suc n) ( c@(𝑐𝑡𝑟𝑙꞉ (𝑖𝑓 b 𝑡ℎ𝑒𝑛 c₁ 𝑒𝑙𝑠𝑒 c₂)) , s'@(just s) ) with evalExp b s
  ... | nothing = nothing -- Computation fail (i.e div by zero)
  ... | exp@(just v) with toTruthValue {exp} (Any.just tt)
  ... | true     = ssEvalwithFuel n ( c₁ , s' )
  ... | false    = ssEvalwithFuel n ( c₂ , s')

  -- Loops
  ssEvalwithFuel (suc n) (𝑙𝑜𝑜𝑝꞉ (𝑤ℎ𝑖𝑙𝑒 b 𝑑𝑜 c) , nothing ) = nothing
  ssEvalwithFuel (suc n) ( loop@(𝑙𝑜𝑜𝑝꞉ (𝑤ℎ𝑖𝑙𝑒 b 𝑑𝑜 c)) , s'@(just s)) with evalExp b s
  ... | nothing = nothing -- Computation fail (i.e div by zero)
  ... | exp@(just v) with toTruthValue {exp} (Any.just tt)
  ... | true     = ssEvalwithFuel n ( 𝑠𝑒𝑞꞉ (c ﹔ loop) , s' )
  ... | false    = ssEvalwithFuel n (𝑠𝑘𝑖𝑝 , s')

  -- Sequence: (skip ; C)
  ssEvalwithFuel (suc n) (𝑠𝑒𝑞꞉ (_ ﹔ _) , nothing )  = nothing
  ssEvalwithFuel (suc n) (𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ c@(𝑎𝑠𝑠𝑖꞉ x)) , s@(just _)) = ssEvalwithFuel (suc n) (c , s)
  ssEvalwithFuel (suc n) (𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ c@(𝑠𝑒𝑞꞉ x)) ,  s@(just _)) = ssEvalwithFuel (suc n) (c , s)
  ssEvalwithFuel (suc n) (𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ c@(𝑐𝑡𝑟𝑙꞉ x)) , s@(just _)) = ssEvalwithFuel (suc n) (c , s)
  ssEvalwithFuel (suc n) (𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ c@(𝑙𝑜𝑜𝑝꞉ x)) , s@(just _)) = ssEvalwithFuel (suc n) (c , s)
  ssEvalwithFuel (suc n) (𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ c@(𝑠𝑘𝑖𝑝))  ,  s@(just _)) = ssEvalwithFuel (suc n) (c , s)

  -- Sequence: (Assignment ; C)
  ssEvalwithFuel (suc n) (𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ c₁ ﹔ c₂) , (just s)) =  ssEvalwithFuel n ( c₂ , ( evalAssi s c₁ )) 

  -- Sequence: (Sequence ; C)
  ssEvalwithFuel (suc n) (𝑠𝑒𝑞꞉ c@(𝑠𝑒𝑞꞉ (c₁ ﹔ c₂) ﹔ c₃) , s@(just _)) = ssEvalwithFuel (n) (𝑠𝑒𝑞꞉ (c₁ ﹔ (𝑠𝑒𝑞꞉ (c₂ ﹔ c₃))) ,  s)

  -- Sequence: (If then Else ; C)
  ssEvalwithFuel (suc n) ( (𝑠𝑒𝑞꞉ (c@(𝑐𝑡𝑟𝑙꞉ (𝑖𝑓 b 𝑡ℎ𝑒𝑛 c₁ 𝑒𝑙𝑠𝑒 c₂)) ﹔ c₃ ) ) , s'@(just s) ) with evalExp b s
  ... | nothing = nothing
  ... | exp@(just v) with toTruthValue {exp} (Any.just tt)
  ... | true     = ssEvalwithFuel n ( (𝑠𝑒𝑞꞉ (c₁ ﹔ c₃) ) , s' )
  ... | false    = ssEvalwithFuel n ( (𝑠𝑒𝑞꞉ (c₂ ﹔ c₃) ) , s' )

  -- Sequence: (Loop : C)
  ssEvalwithFuel (suc n) ( (𝑠𝑒𝑞꞉ (loop@(𝑙𝑜𝑜𝑝꞉ (𝑤ℎ𝑖𝑙𝑒 b 𝑑𝑜 c₁)) ﹔ c₂ ) ) , s'@(just s)) with evalExp b s
  ... | nothing = nothing
  ... | exp@(just v) with toTruthValue {exp} (Any.just tt)
  ... | true     = ssEvalwithFuel n ( 𝑠𝑒𝑞꞉ (𝑠𝑒𝑞꞉ (c₁ ﹔ loop) ﹔ c₂) , s' )
  ... | false    = ssEvalwithFuel n ( c₂ , s')

  
  

  {-
  evalAssi : ∀ {i e} → S → (p : i := e) → Maybe S
  evalAssi s (id ꞉= exp) = map (λ v → updateState id v s) (evalExp exp s)

  is-JustExp→is-JustAssi : ∀ {i e s} → Is-just (evalExp e s) → Is-just (evalAssi s (i ꞉= e))
  is-JustExp→is-JustAssi {i} {e} {s} p with (evalExp e s)
  ... | just x = Any.just tt

  ssEvalwithFuel :  ℕ → 𝐶 × Maybe S → 𝐶 × Maybe S 
  ssEvalwithFuel zero (fst , s) = fst , nothing   -- ran out of fuel
  ssEvalwithFuel (suc n) (𝑠𝑘𝑖𝑝 , s) = 𝑠𝑘𝑖𝑝 , s -- eval finished successfully


  ssEvalwithFuel (suc n) (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) , (just s)) = 𝑠𝑘𝑖𝑝 , evalAssi s (i ꞉= e)
  ssEvalwithFuel (suc n) (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) , nothing) = 𝑠𝑘𝑖𝑝 , nothing 

  ssEvalwithFuel (suc n) ( c@(𝑐𝑡𝑟𝑙꞉ (𝑖𝑓 b 𝑡ℎ𝑒𝑛 c₁ 𝑒𝑙𝑠𝑒 c₂)) , nothing ) = c , nothing
  ssEvalwithFuel (suc n) ( c@(𝑐𝑡𝑟𝑙꞉ (𝑖𝑓 b 𝑡ℎ𝑒𝑛 c₁ 𝑒𝑙𝑠𝑒 c₂)) , s'@(just s) ) with evalExp b s
  ... | nothing = c , nothing -- Computation fail (i.e div by zero)
  ... | (just v) with v ?val= 𝑻 | v ?val= 𝑭
  ... | yes _ | _     = ssEvalwithFuel n ( c₁ , s' )
  ... | no  _ | yes _ = ssEvalwithFuel n ( c₂ , s')
  ... | no _  | no _  = c , nothing -- Should not happen: TODO: refactor to eliminate this case

  ssEvalwithFuel (suc n) (𝑙𝑜𝑜𝑝꞉ (𝑤ℎ𝑖𝑙𝑒 b 𝑑𝑜 c) , nothing ) = c , nothing
  ssEvalwithFuel (suc n) ( loop@(𝑙𝑜𝑜𝑝꞉ (𝑤ℎ𝑖𝑙𝑒 b 𝑑𝑜 c)) , s'@(just s)) with evalExp b s
  ... | nothing = c , nothing -- Computation fail (i.e div by zero)
  ... | (just v) with v ?val= 𝑻 | v ?val= 𝑭
  ... | yes _ | _     = ssEvalwithFuel n ( 𝑠𝑒𝑞꞉ (c ﹔ loop) , s' )
  ... | no  _ | yes _ = ssEvalwithFuel n (𝑠𝑘𝑖𝑝 , s')
  ... | no _  | no _  = c , nothing -- Should not happen: TODO: refactor to eliminate this case

  ssEvalwithFuel (suc n) (𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ c₁ ﹔ c₂) , s) =  ssEvalwithFuel n ( c₂ , ( s >>= λ { ms → evalAssi ms c₁ } ) ) 
  ssEvalwithFuel (suc n) (𝑠𝑒𝑞꞉ c@(𝑠𝑒𝑞꞉ (c₁ ﹔ c₂) ﹔ c₃) , s) = ssEvalwithFuel (n) (𝑠𝑒𝑞꞉ (c₁ ﹔ (𝑠𝑒𝑞꞉ (c₂ ﹔ c₃))) ,  s)

  
  ssEvalwithFuel (suc n) ( (𝑠𝑒𝑞꞉ (c@(𝑐𝑡𝑟𝑙꞉ (𝑖𝑓 b 𝑡ℎ𝑒𝑛 c₁ 𝑒𝑙𝑠𝑒 c₂)) ﹔ c₃ ) ) , nothing ) = c , nothing
  ssEvalwithFuel (suc n) ( (𝑠𝑒𝑞꞉ (c@(𝑐𝑡𝑟𝑙꞉ (𝑖𝑓 b 𝑡ℎ𝑒𝑛 c₁ 𝑒𝑙𝑠𝑒 c₂)) ﹔ c₃ ) ) , s'@(just s) ) with evalExp b s
  ... | nothing = c , nothing
  ... | (just v) with v ?val= 𝑻 | v ?val= 𝑭
  ... | yes _ | _     = ssEvalwithFuel n ( (𝑠𝑒𝑞꞉ (c₁ ﹔ c₃) ) , s' )
  ... | no  _ | yes _ = ssEvalwithFuel n ( (𝑠𝑒𝑞꞉ (c₂ ﹔ c₃) ) , s' )
  ... | no _  | no _  = c , nothing -- Should not happen: TODO: refactor to eliminate this case

  ssEvalwithFuel (suc n) ( (𝑠𝑒𝑞꞉ (loop@(𝑙𝑜𝑜𝑝꞉ (𝑤ℎ𝑖𝑙𝑒 b 𝑑𝑜 c₁)) ﹔ c₂ ) ) , nothing ) = c₁ , nothing
  ssEvalwithFuel (suc n) ( (𝑠𝑒𝑞꞉ (loop@(𝑙𝑜𝑜𝑝꞉ (𝑤ℎ𝑖𝑙𝑒 b 𝑑𝑜 c₁)) ﹔ c₂ ) ) , s'@(just s)) with evalExp b s
  ... | nothing = c₁ , nothing
  ... | (just v) with v ?val= 𝑻 | v ?val= 𝑭
  ... | yes _ | _     = ssEvalwithFuel n ( 𝑠𝑒𝑞꞉ (𝑠𝑒𝑞꞉ (c₁ ﹔ loop) ﹔ c₂) , s' )
  ... | no  _ | yes _ = ssEvalwithFuel n ( c₂ , s')
  ... | no _  | no _  = c₁ , nothing -- Should not happen: TODO: refactor to eliminate this case

  ssEvalwithFuel (suc n) (𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ c₂) , s) = ssEvalwithFuel (suc n) (c₂ , s)
  -}

  {-
  _ExecWith_terminatesInState_ : (c : C) → ( s : S) → Terminates c s → S → Set
  c ExecWith s terminatesInState s' with terminates c s
  ... | umm = {!!}
  -}

  --Σ[ evaluates ∈ terminates c s ] (drop-just (proj₂ evaluates) )  
  

{-

  evalProg : ℕ → C → S → Maybe S
  evalProg (suc n) (𝑎𝑠𝑠𝑖꞉  p ) s = evalAssi s p
  evalProg n (𝑠𝑒𝑞꞉ (c₁ ﹔ c₂)) s = (evalProg n  c₁ s) >>= (evalProg n c₂)
--  ... | nothing , _ = nothing
--  ... | just s' , n = (evalProg c₂) 
  evalProg n (𝑐𝑡𝑟𝑙꞉ (𝑖𝑓 b 𝑡ℎ𝑒𝑛 c₁ 𝑒𝑙𝑠𝑒 c₂)) s with evalExp b s
  evalProg n (𝑐𝑡𝑟𝑙꞉ (𝑖𝑓 b 𝑡ℎ𝑒𝑛 c₁ 𝑒𝑙𝑠𝑒 c₂)) s | nothing = nothing
  evalProg n (𝑐𝑡𝑟𝑙꞉ (𝑖𝑓 b 𝑡ℎ𝑒𝑛 c₁ 𝑒𝑙𝑠𝑒 c₂)) s | just x    with x ?val= 𝑻
  evalProg n (𝑐𝑡𝑟𝑙꞉ (𝑖𝑓 b 𝑡ℎ𝑒𝑛 c₁ 𝑒𝑙𝑠𝑒 c₂)) s | just x | yes _ = evalProg n c₁ s
  evalProg n (𝑐𝑡𝑟𝑙꞉ (𝑖𝑓 b 𝑡ℎ𝑒𝑛 c₁ 𝑒𝑙𝑠𝑒 c₂)) s | just x | no _  = evalProg n c₂ s
  evalProg n (𝑙𝑜𝑜𝑝꞉ (𝑤ℎ𝑖𝑙𝑒 b 𝑑𝑜 c )) s  with evalExp b s
  evalProg n (𝑙𝑜𝑜𝑝꞉ (𝑤ℎ𝑖𝑙𝑒 b 𝑑𝑜 c )) s | nothing = nothing
  evalProg n (𝑙𝑜𝑜𝑝꞉ (𝑤ℎ𝑖𝑙𝑒 b 𝑑𝑜 c )) s | just x with x ?val= 𝑻
  evalProg n (𝑙𝑜𝑜𝑝꞉ (𝑤ℎ𝑖𝑙𝑒 b 𝑑𝑜 c )) s | just x | yes _ = (evalProg n c s) >>= (evalProg n (𝑙𝑜𝑜𝑝꞉ (𝑤ℎ𝑖𝑙𝑒 b 𝑑𝑜 c )))
  evalProg n (𝑙𝑜𝑜𝑝꞉ (𝑤ℎ𝑖𝑙𝑒 b 𝑑𝑜 c )) s | just x | no _  = just s
-}

--  data evalLoop : Maybe S → Set where
--    stop     : ∀ s b c → evalExp b s ≡ just 𝑭 → WHILE b DO c → evalLoop (just s)
--    loop : ∀ s b c → evalExp b s ≡ just 𝑻 → WHILE b DO c → evalLoop (evalProg n c s) 
{-
  evalN : ℕ → C → S → Maybe S
  evalN zero c s = just s
  evalN (suc n) c s = evalProg c s >>= evalN n c


  evalWhile : ∀ b c s  → ( p : WHILE b DO c )
              → Σ[ n ∈ ℕ ]  Σ[ s' ∈ S ] evalN n c s ≡ just s' × evalExp b s' ≡ just 𝑭 
              → evalLoop {!!}
  evalWhile b c s (𝑤ℎ𝑖𝑙𝑒 .b 𝑑𝑜 .c) (zero , s' , fst , snd) = {!!}
  evalWhile b c s (𝑤ℎ𝑖𝑙𝑒 .b 𝑑𝑜 .c) (suc n , s' , fst , snd) = {!!}
-}






