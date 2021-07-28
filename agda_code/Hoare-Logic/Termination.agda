
-- Lib imports
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; inspect ; [_] ; cong )
open import Data.Maybe using ( Maybe ; just ; nothing ; _>>=_ ; Is-just ; to-witness )
open import Data.Maybe.Relation.Unary.Any using (Any)
open import Data.Product using (Σ ; Σ-syntax ; _×_  ; _,_  ; proj₁ ; proj₂ )
open import Data.Nat using (ℕ ; suc ; zero)
open import Data.Unit using ( ⊤ ; tt )
open import Relation.Unary using (Pred)
open import Data.Empty

-- Project imports
open import Representation.Data using (D-Representation )
open import Representation.State using (S-Representation)
open import Misc


module Hoare-Logic.Termination (dRep : D-Representation )
  (sRep : S-Representation dRep ) where

  open D-Representation dRep
  open S-Representation sRep

  open import Mini-C.Expressions dRep sRep
  open import Mini-C.Lang dRep sRep
  open import Mini-C.Evaluation dRep sRep


  Terminates : 𝐶 → S → Set
  Terminates c s = Σ[ n ∈ ℕ ] ( Is-just (proj₂ (ssEvalwithFuel n ( c , just s ))))

  data Terminates' :  𝐶 → S → Set where
    t : ∀ {c} {s} (n : ℕ) → Is-just (proj₂ (ssEvalwithFuel n ( c , just s ))) → Terminates' c s


  skipTerminates : ∀ s → Terminates 𝑠𝑘𝑖𝑝 s
  skipTerminates s = 2 , Any.just tt

  data Eval : S → 𝐶 → S → Set where
    result= : ∀ {c} {s} → (t : Terminates c s) → Eval s c (to-witness (proj₂ t))
    

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
  assiProgW/ValidExpTerminates i e s (.i ꞉= .e) p = 1 , is-JustExp→is-JustAssi {i} {e} {s} p

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


