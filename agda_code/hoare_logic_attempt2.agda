


import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_  ; refl ; sym ; cong)
--open import Relation.Nullary.Reflects
--open import Relation.Nullary.Decidable
open import Data.Empty
open import Relation.Nullary
open import Relation.Nullary.Decidable using (False ; True ; isYes ; isNo ; ⌊_⌋ )
open import Data.Bool as Bool renaming (Bool to 𝔹) using ( true ; false) 
open import Data.Integer as Int using (ℤ ; _+_ ; _-_ ; _*_ )
open import Data.Integer.Base using (∣_∣ )  
open import Data.Integer.DivMod using ( _div_ ; _mod_ )
open import Data.List as List using (List; _∷_; [] ; map ; _++_ )
open import Data.String.Properties using (_≈?_)
open import Data.Nat as ℕ renaming (_+_ to _⊕_ ; _*_ to _⊛_ ) using (ℕ; zero; suc; _∸_; _≤_; pred ; _≟_ ; _≤?_)
open import Data.Maybe using (Maybe)
open import Data.Maybe.Categorical as Cₘ
--open import Data.Maybe.Relation.Binary.Pointwise using (Pointwise ; drop-just)
open import Data.Product renaming (_,_ to _∧_  )

open Maybe
open ℤ


open import Agda.Builtin.Unit
open import Data.Empty using (⊥)

open import integer_operations

open import Data.Product


{-
pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []
-}


localVar = Id × Val



module Programs where


  {- Not ideal this being a List, contains more information than we need (the order)
     which (as I suspected) is making proofs further down the line more difficult.
     The State should be a 𝑆𝑒𝑡 of Entrys. -}
  S = List localVar

  {-
  Maybe do something like this:

  The set of unordered pairs of A can be defined using a higher-inductive 
  type with set-truncation, just as you suggested, somewhat like this 
  (I am writing this off the top of my head without verifying it in Agda, 
  but you'll get the point:)
  
  data UPair (A : Type ℓ) : Type ℓ where
    mkpair : (x y : A) → UPair A
    uswap : ∀ a b → mkpair a b ≡ mkpair b a
    trunc : ∀ (u v : UPair A) (p q : u ≡ v) → p ≡ q


  -- Andrej Bauer


  data Store : Set where

    one :  Id → Val → Store
    step : Store → Id no in State → Id val + State → State
    idUnique : State Id Val₁ → State Id Val₂ → Val₁ ≡ Val₂

  -} 

  {-
  data Store : List localVar → Set where
    list      :  ( ls : List localVar ) → Store ls 
    unorderedₗ : ∀ {id : Id} {v : Val } → { ls : List localVar } → Store ( (id , v) ∷ ls ) → Store ( ls ++ (( id , v ) ∷ []) )
    unorderedᵣ : ∀ {id : Id} {v : Val } → { ls : List localVar } → Store ( ls ++ (( id , v ) ∷ []) ) → Store ( (id , v) ∷ ls )


  
  updateStore : ∀ {ls} {ls'} → Id → Val → Store ls → Store ls'
  updateStore {ls} {_} i z (list .ls) = ?
  updateStore {.( _ ++ ([ _ , _ ]))} {_} i z (unorderedₗ s) = ?
  updateStore {.((_ , _) ∷ _)} {_} i z (unorderedᵣ s) = ?
  -}

  -- LOOK BACK AT WHAT WAS CAUSING YOU TO WORRY ABOUT LIST REPRESENTATION
  
  {-
  data Store  where
    _:=:_  : Id → Val → Store
    combine  : ∀ {i} → (s s' : Store)
                     → (hasLocalVar s i → notLocalVar s' i)
                     → (hasLocalVar s' i → notLocalVar s i)
                     → Store

  
  data notLocalVar where
    single    : ∀ {z} i j  → i ≡ j → ⊥ → notLocalVar (i :=: z) j 
    notEither : ∀ i s s' → notLocalVar s i → notLocalVar s' i → notLocalVar (combine s s' _ _) i


  data hasLocalVar  where
    justOne   : ∀ i z s → hasLocalVar (i :=: z) i 
    toTheLeft : ∀ i s s' →  hasLocalVar s i → notLocalVar s' i → hasLocalVar (combine s s' _ _) i
    toTheRight : ∀ i s s' → notLocalVar s i → hasLocalVar s' i → hasLocalVar (combine s s' _ _) i
  -}

  updateState : Id → Val → S → S
  updateState i z  []  = [( i ∧ z )]
  updateState i e ((fst ∧ snd) ∷ zs)  with fst ≟ i
  ...                                 | yes _ = (i ∧ e) ∷ zs
  ...                                 | no _ = (fst ∧ snd ) ∷ updateState i e zs
  

  getVar : Id → S → Maybe Val
  getVar i [] = nothing
  getVar i ((fst ∧ snd) ∷ zs) with ⌊ i ≟ fst ⌋
  ...                                 | true =  just snd 
  ...                                 | false = getVar i zs


  evalArgs : S → List Expr → List (Maybe ℤ)
  evalArgs s [] = []
  evalArgs s (Constant x ∷ es) = (just x) ∷ evalArgs s es
  evalArgs s (Var x ∷ es)      = (getVar x s) ∷ evalArgs s es 
  evalArgs s (Op op exps ∷ es) = let args = evalArgs s exps in (opEval op args) ∷ evalArgs s es

  
  eval :  Expr → S -> Maybe ℤ
  eval (Constant x) s = just x
  eval (Var x)      s = getVar x s
  eval (Op op exps) s = opEval op (evalArgs s exps)

  {-
  data ℤPropValue : List Id → Set where
    Con : ℤ → ℤPropValue []
    Var : ∀ {i : Id} → ℤPropValue (i ∷ []) 
    -- TODO: Add expressions so [(X + 1) > 3] can be a goal?


  data 𝔹PropValue : List Id → Set where
    Con : 𝔹 → 𝔹PropValue []
    --Var : Id → 𝔹PropValue


  data ℤProp : List Id → Set where
    eqPℤ      : ∀ {l r : List Id} → ℤPropValue l → ℤPropValue r → ℤProp (l ++ r)
    LeqPℤ     : ∀ {l r : List Id} → ℤPropValue l → ℤPropValue r → ℤProp (l ++ r)
    LessPℤ    : ∀ {l r : List Id} → ℤPropValue l → ℤPropValue r → ℤProp (l ++ r)
    GeqPℤ     : ∀ {l r : List Id} → ℤPropValue l → ℤPropValue r → ℤProp (l ++ r)
    GreaterPℤ : ∀ {l r : List Id} → ℤPropValue l → ℤPropValue r → ℤProp (l ++ r)
  -}

  {- Trying: Add List Id as indexed data type ? -}
  
  data ℤPropValue : Set where
    Con : ℤ → ℤPropValue
    Var : Id → ℤPropValue
    -- TODO: Add expressions so [(X + 1) > 3] can be a goal?


  data 𝔹PropValue : Set where
    Con : 𝔹 → 𝔹PropValue
    --Var : Id → 𝔹PropValue


  data ℤProp : Set where
    eqPℤ      : ℤPropValue → ℤPropValue → ℤProp
    LeqPℤ     : ℤPropValue → ℤPropValue → ℤProp
    LessPℤ    : ℤPropValue → ℤPropValue → ℤProp
    GeqPℤ     : ℤPropValue → ℤPropValue → ℤProp
    GreaterPℤ : ℤPropValue → ℤPropValue → ℤProp
  

  -- Maybe need to be xplicit about which variable the proposition holds for rather than generalise over all variables in the store
  
  data PROPO : Set where
    𝔹•        : 𝔹PropValue → PROPO
    𝔹ℤ        : ℤProp → PROPO
    eq𝔹       : PROPO → PROPO → PROPO
    𝔹∧        : PROPO → PROPO → PROPO
    𝔹V        : PROPO → PROPO → PROPO
    -- 𝔹¬        : PROPO → PROPO
  

  {-
  data PROPO : List Id → Set where
    𝔹•       : ∀ {l : List Id} → 𝔹PropValue l → PROPO l
    𝔹ℤ       : ∀ {l : List Id} → ℤProp l → PROPO l
    eq𝔹      : ∀ {l r : List Id} → PROPO l → PROPO r → PROPO (l ++ r) -- does this make sense???
    𝔹∧       : ∀ {l r : List Id} → PROPO l → PROPO r → PROPO (l ++ r)
    𝔹V       : ∀ {l r : List Id} → PROPO l → PROPO r → PROPO (l ++ r)


  data holds : {ls : List Id} → S → PROPO ls → Set where
    CCEq :  ∀ {x y : ℤ} → {s : S} → (x ≡ y) → holds s (𝔹ℤ    (eqPℤ (Con x) (Con y))  )
    VCEq :  ∀ {x y : ℤ} → {id : Id} → {s : S} → (𝔹ℤ  (eqPℤ  ?       ?    ) )  
  -}


  
  {-    
  data holds : List Id → PROPO → S → Set where
    CCEq : ∀ {vars : Id} → {x y : ℤ} → { s : S } → ( x ≡ y ) → holds vars ( 𝔹ℤ (eqPℤ (Con x) (Con y) ) ) s
    CVEq : ∀ {vars : Id} → {x y : ℤ} → { s : S } → {id idₛ : Id} → ( x ≡ y ) → (id ≡ idₛ) → holds vars (𝔹ℤ (eqPℤ (Con x) (Var id))) ((idₛ , y) ∷ s )  
    VCEq : ∀ {vars : Id} → {x y : ℤ} → { s : S } → {id idₛ : Id} → ( x ≡ y ) → (id ≡ idₛ) → holds vars (𝔹ℤ (eqPℤ (Var id) (Con x))) ((idₛ , y) ∷ s )
    VVEq : ∀ {vars : Id} → {x y : ℤ} → { s : S } → {id₁ id₂ idₛ₁ idₛ₂ : Id} → ( x ≡ y ) → (id₁ ≡ idₛ₁) → (id₂ ≡ idₛ₂) → holds vars (𝔹ℤ (eqPℤ (Var id₁) (Var id₂))) ((id₁ , x) ∷ (id₂ , y) ∷ s)
    ANDHolds : ∀ {vars : Id} → {p q : PROPO} → {s : S} → holds vars p s → holds vars q s → holds vars (𝔹∧ p q) s
    ORHoldL  : ∀ {vars : Id} → {p q : PROPO} → {s : S} → holds vars p s → holds vars (𝔹V p q) s
    ORHoldR  : ∀ {vars : Id} → {p q : PROPO} → {s : S} → holds vars q s → holds vars (𝔹V p q) s
  -}



  


  {- This doesn't seem to be working too well with the function 'getVar' within the constructor. Going to try and change to have the same property encoded in a data type
  data holds : PROPO → S → Set where
    CCEq : ∀ {x y : ℤ} → { s : S } → ( x ≡ y ) → holds ( 𝔹ℤ (eqPℤ (Con x) (Con y) ) ) s
    CVEq : ∀ {x y : ℤ} → { s : S } → {id : Id} → ( x ≡ y ) → getVar id s ≡ just (y) →  holds (𝔹ℤ (eqPℤ (Con x) (Var id))) s  
    VCEq : ∀ {x y : ℤ} → { s : S } → {id : Id} → ( x ≡ y ) → getVar id s ≡ just (y) →  holds (𝔹ℤ (eqPℤ (Var id) (Con x))) s
    VVEq : ∀ {x y : ℤ} → { s : S } → {id₁ id₂ : Id} → ( x ≡ y ) → getVar id₁ s ≡ just (x) → getVar id₂ s ≡ just (y) → holds (𝔹ℤ (eqPℤ (Var id₁) (Var id₂))) s
    ANDHolds : ∀ {p q : PROPO} → {s : S} → holds p s → holds q s → holds (𝔹∧ p q) s
    ORHoldL  : ∀ {p q : PROPO} → {s : S} → holds p s → holds (𝔹V p q) s
    ORHoldR  : ∀ {p q : PROPO} → {s : S} → holds q s → holds (𝔹V p q) s
  -}
  
  data holds : PROPO → S → Set where
    CCEq : ∀ {x y : Val} → { s : S } → ( x ≡ y ) → holds ( 𝔹ℤ (eqPℤ (Con x) (Con y) ) ) s
    CVEq : ∀ (x y : Val) → (s : S) → (id : Id) → x ≡ y → hasValue id y s →  holds (𝔹ℤ (eqPℤ (Con x) (Var id))) s  
    VCEq : ∀ (x y : Val) → (s : S) → (id : Id) → x ≡ y → hasValue id y s →  holds (𝔹ℤ (eqPℤ (Var id) (Con x))) s
    VVEq : ∀ (x y : Val) → ( s : S ) → (id₁ id₂ : Id) → x ≡ y → hasValue id₁ x s → hasValue id₂ y s → holds (𝔹ℤ (eqPℤ (Var id₁) (Var id₂))) s
    ANDHolds : ∀ (p q : PROPO) → (s : S) → holds p s → holds q s → holds (𝔹∧ p q) s
    ORHoldL  : ∀ (p q : PROPO) → (s : S) → holds p s → holds (𝔹V p q) s
    ORHoldR  : ∀ (p q : PROPO) → (s : S) → holds q s → holds (𝔹V p q) s
  -- Todo: swap order of arguments around to make more intelligible

  sub : ℤ → Id → PROPO → PROPO
  sub f i (𝔹• (Con x)) = 𝔹• (Con x)
  sub f i (𝔹ℤ (eqPℤ (Con x) (Con x₁))) = 𝔹ℤ (eqPℤ (Con x) (Con x₁))
  sub f i (𝔹ℤ (eqPℤ (Con x) (Var x₁))) with i ≟ x₁
  ...                                       | yes _ = 𝔹ℤ (eqPℤ (Con x) (Con f))
  ...                                       | no _ = 𝔹ℤ (eqPℤ (Con x) (Var x₁))
  sub f i (𝔹ℤ (eqPℤ (Var x) (Con x₁))) with i ≟ x
  ...                                       | yes _ = 𝔹ℤ (eqPℤ (Con f) (Con x₁))
  ...                                       | no _ = 𝔹ℤ (eqPℤ (Var x) (Con x₁))
  sub f i (𝔹ℤ (eqPℤ (Var x) (Var x₁))) with ⌊ i ≟ x ⌋ | ⌊ i ≟ x₁ ⌋
  ...                                       | true  | true = 𝔹ℤ (eqPℤ (Con f) (Con f))
  ...                                       | true  | false = 𝔹ℤ (eqPℤ (Con f) (Var x₁))
  ...                                       | false | true = 𝔹ℤ (eqPℤ (Var x) (Con f))
  ...                                       | false | false = 𝔹ℤ (eqPℤ (Var x) (Var x₁))
  sub f i (𝔹ℤ (LeqPℤ (Con x) (Con x₁))) = 𝔹ℤ (LeqPℤ (Con x) (Con x₁))
  sub f i (𝔹ℤ (LeqPℤ (Con x) (Var x₁))) with ⌊ i ≟ x₁ ⌋
  ...                                       | true = 𝔹ℤ (LeqPℤ (Con x) (Con f))
  ...                                       | false = 𝔹ℤ (LeqPℤ (Con x) (Var x₁))
  sub f i (𝔹ℤ (LeqPℤ (Var x) (Con x₁))) with ⌊ i ≟ x ⌋
  ...                                       | true = 𝔹ℤ (LeqPℤ (Con f) (Con x₁))
  ...                                       | false = 𝔹ℤ (LeqPℤ (Var x) (Con x₁))
  sub f i (𝔹ℤ (LeqPℤ (Var x) (Var x₁))) with ⌊ i ≟ x ⌋ | ⌊ i ≟ x₁ ⌋
  ...                                       | true  | true = 𝔹ℤ (LeqPℤ (Con f) (Con f))
  ...                                       | true  | false = 𝔹ℤ (LeqPℤ (Con f) (Var x₁))
  ...                                       | false | true = 𝔹ℤ (LeqPℤ (Var x₁) (Con f))
  ...                                       | false | false = 𝔹ℤ (LeqPℤ (Var x) (Var x₁))
  sub f i (𝔹ℤ (LessPℤ (Con x) (Con x₁))) = 𝔹ℤ (LessPℤ (Con x) (Con x₁))
  sub f i (𝔹ℤ (LessPℤ (Con x) (Var x₁))) with ⌊ i ≟ x₁ ⌋
  ...                                       | true = 𝔹ℤ (LessPℤ (Con x) (Con f))
  ...                                       | false = 𝔹ℤ (LessPℤ (Con x) (Var x₁))
  sub f i (𝔹ℤ (LessPℤ (Var x) (Con x₁))) with ⌊ i ≟ x ⌋
  ...                                       | true = 𝔹ℤ (LessPℤ (Con f) (Con x₁))
  ...                                       | false = 𝔹ℤ (LessPℤ (Var x) (Con x₁))
  sub f i (𝔹ℤ (LessPℤ (Var x) (Var x₁))) with ⌊ i ≟ x ⌋ | ⌊ i ≟ x₁ ⌋
  ...                                       | true  | true = 𝔹ℤ (LessPℤ (Con f) (Con f))
  ...                                       | true  | false = 𝔹ℤ (LessPℤ (Con f) (Var x₁))
  ...                                       | false | true = 𝔹ℤ (LessPℤ (Var x₁) (Con f))
  ...                                       | false | false = 𝔹ℤ (LessPℤ (Var x) (Var x₁))
  sub f i (𝔹ℤ (GeqPℤ (Con x) (Con x₁))) = 𝔹ℤ (GeqPℤ (Con x) (Con x₁))
  sub f i (𝔹ℤ (GeqPℤ (Con x) (Var x₁))) with ⌊ i ≟ x₁ ⌋
  ...                                       | true = 𝔹ℤ (GeqPℤ (Con x) (Con f))
  ...                                       | false = 𝔹ℤ (GeqPℤ (Con x) (Var x₁))
  sub f i (𝔹ℤ (GeqPℤ (Var x) (Con x₁))) with ⌊ i ≟ x ⌋
  ...                                       | true = 𝔹ℤ (GeqPℤ (Con f) (Con x₁))
  ...                                       | false = 𝔹ℤ (GeqPℤ (Var x) (Con x₁))
  sub f i (𝔹ℤ (GeqPℤ (Var x) (Var x₁))) with ⌊ i ≟ x ⌋ | ⌊ i ≟ x₁ ⌋
  ...                                       | true  | true = 𝔹ℤ (GeqPℤ (Con f) (Con f))
  ...                                       | true  | false = 𝔹ℤ (GeqPℤ (Con f) (Var x₁))
  ...                                       | false | true = 𝔹ℤ (GeqPℤ (Var x₁) (Con f))
  ...                                       | false | false = 𝔹ℤ (GeqPℤ (Var x) (Var x₁))
  sub f i (𝔹ℤ (GreaterPℤ (Con x) (Con x₁))) = 𝔹ℤ (GreaterPℤ (Con x) (Con x₁))
  sub f i (𝔹ℤ (GreaterPℤ (Con x) (Var x₁))) with ⌊ i ≟ x₁ ⌋
  ...                                       | true = 𝔹ℤ (GreaterPℤ (Con x) (Con f))
  ...                                       | false = 𝔹ℤ (GreaterPℤ (Con x) (Var x₁))
  sub f i (𝔹ℤ (GreaterPℤ (Var x) (Con x₁))) with ⌊ i ≟ x ⌋
  ...                                       | true = 𝔹ℤ (GreaterPℤ (Con f) (Con x₁))
  ...                                       | false = 𝔹ℤ (GreaterPℤ (Var x) (Con x₁))
  sub f i (𝔹ℤ (GreaterPℤ (Var x) (Var x₁))) with ⌊ i ≟ x ⌋ | ⌊ i ≟ x₁ ⌋
  ...                                       | true  | true = 𝔹ℤ (GreaterPℤ (Con f) (Con f))
  ...                                       | true  | false = 𝔹ℤ (GreaterPℤ (Con f) (Var x₁))
  ...                                       | false | true = 𝔹ℤ (GreaterPℤ (Var x₁) (Con f))
  ...                                       | false | false = 𝔹ℤ (GreaterPℤ (Var x) (Var x₁))
  sub f i (eq𝔹 p p₁) = eq𝔹 (sub f i p) (sub f i p₁)
  sub f i (𝔹∧ p p₁) = 𝔹∧ (sub f i p) (sub f i p₁)
  sub f i (𝔹V p p₁) = 𝔹V (sub f i p) (sub f i p₁)
  

  {-
  data holds : ℤPropValue → ℤProp → ℤPropValue → S → Set where
    CCEq : ∀ {x y : ℤ} → { s : S } → (x ≡ y) →  holds (Con x) eqPℤ (Con y) s 
    CVEq : ∀ {x y : ℤ} → {id idₛ : ℕ} → { s : S } → (id ≡ idₛ) → (x ≡ y) → holds (Con x) eqPℤ (Var id) ((idₛ , y) ∷ s)
    VCEq : ∀ {x y : ℤ} → {id idₛ : ℕ} → { s : S } → (id ≡ idₛ) → (x ≡ y) → holds (Var id) eqPℤ (Con x) ((idₛ , y) ∷ s)
    VVEq : ∀ {x y : ℤ} → {id₁ id₂ idₛ₁ idₛ₂ : ℕ} → (id₁ ≡ idₛ₁) → (id₂ ≡ idₛ₂) → (x ≡ y) → holds (Var id₁) eqPℤ (Var id₂) ((idₛ₁ , x) ∷ (idₛ₂ , y) ∷ [] )
 
  -}


  
  data AssiProgram : Id → Expr → Set where
    _:=_ : ∀ (id : Id) → (exp : Expr) →  AssiProgram id exp

  evalAssi : ∀ {id : Id} {exp : Expr} → S → AssiProgram id exp → Maybe S
  evalAssi s (id := exp) with (eval exp s)
  ... | nothing = nothing
  ... | just f = just (updateState id f s)



  data Program : Set where

    assi  : ∀ {id : Id} {exp : Expr} → AssiProgram id exp → Program
    
    
  evalProgram : S → Program  → Maybe S
  evalProgram s (assi x) = evalAssi s x


  {-
  data Program : Set where
    Block : List Program → Program
    Assignment : Id → Expr → Program
    While : Expr → Program -> Program
    If : Expr → Program -> Program
    IfElse : Expr → Program → Program -> Program
  -}

  {-
  data isEq : ℤProp → Set where
    •• : isEq eqPℤ 
  -}

  drop-just : ∀ {A : Set} → {x y : A} → just x ≡ just y → x ≡ y
  drop-just refl = refl


  --



  

  
  
  assi=Upsert : ∀ {f} s i  → hasValue i f s → updateState i f s ≡ updateState i f (dropValue s i)
  assi=Upsert .((i , _) ∷ s) i (atthehead .i _ s) with (i ≟ i)
  ... | .true because ofʸ p = {!!}
  ... | .false because ofⁿ ¬p = {!!}



  ✰assi¬∅ : ∀ s i exp → (f : ℤ) → (a : AssiProgram i exp) → eval exp s ≡ just f
                                  → evalAssi s a ≡ just [] →  ⊥
  ✰assi¬∅ s i (Constant x) f (.i := .(Constant x)) p₁ p₂ = ✰updateNonEmpty i x s (drop-just p₂)
  ✰assi¬∅ s i (Var x) f (.i := .(Var x)) p₁ p₂ rewrite p₁ = ✰updateNonEmpty i f s (drop-just p₂)
  ✰assi¬∅ s i (Op x x₁) f (.i := .(Op x x₁)) p₁ p₂ rewrite p₁ = ✰updateNonEmpty i f s (drop-just p₂)
  


  eval✰  : ∀ s s' i exp f → (a : AssiProgram i exp) → eval exp s ≡ just f → evalAssi s a ≡ just s'
                           → updateState i f s ≡ s'
  eval✰ [] s' i (Constant x) f (.i := .(Constant x)) p₁ p₂ rewrite (drop-just p₁) = drop-just p₂
  eval✰ [] s' i (Op x x₁) f (.i := .(Op x x₁)) p₁ p₂ rewrite p₁ = drop-just p₂
  eval✰ ((fst , snd) ∷ s) s' i (Constant x) f (.i := .(Constant x)) p₁ p₂ with (i ≟ fst)
  ... | yes proof rewrite (sym proof) = let IH = eval✰ s s' i (Constant x) f (i := (Constant x)) p₁ {!!}  in  {!!}
  ... | no  proof = {!!}
  eval✰ ((fst , snd) ∷ s) s' i (Var x) f a p₁ p₂ = {!!}
  eval✰ ((fst , snd) ∷ s) s' i (Op x x₁) f a p₁ p₂ = {!!}

  {-
  
  with (i ≟ fst)
  ... | yes proof = let IH = eval✰ s s' i exp f a {!!} {!!}  in  {!!}
  ... | no  proof = {!!}

  eval✰ s [] i exp f a p₁ p₂ = ⊥-elim (✰Assi¬∅ s i exp f a p₁ p₂)
  eval✰ s ((fst , snd) ∷ s') i exp f (.i := .exp) p₁ p₂  with (i ≟ fst)
  ... | yes proof = let IH = eval✰ s s' i exp f (i := exp) p₁ {!!} in {!!}
  ... | no  proof = {!!}
  -}
  
  {-

  with (i ≟ fst)
  ... | yes proof = let IH = eval✰ s s' i exp f a p₁ {!!} in {!!}
  ... | no  proof = {!}!
  
  -}

  Predicate = PROPO
  State = S

  
  data HoareTriple : Predicate → Program → Predicate → Set where

    triple : ∀ (s s' : S) → (p q : Predicate) → (prog : Program)
                → evalProgram s prog ≡ just s'
                → holds p s → holds q s'
                → HoareTriple p prog q

  
  axiomOfAssignment : ∀ (s s' : State) (i : Id) (exp : Expr) (f : ℤ)
                        (p : Predicate) (a : AssiProgram i exp)
                      → evalAssi s a ≡ just s'
                      → eval exp s ≡ just f
                      → holds  p  s'
                      → holds (sub f i p)  s
  axiomOfAssignment s s' i e f (𝔹ℤ (eqPℤ (Con x) (Con x₁))) a p₁ p₂ (CCEq x₂) = CCEq x₂
  axiomOfAssignment s s' i e f (𝔹ℤ (eqPℤ (Con x) (Var x₁))) a p₁ p₂ (CVEq .x y .s' .x₁ x₂ x₃) = {!!}

  {-

  eval e s ≡ just f
  evalAssi s a ≡ just s'

  updateState i f s ≡ s'

  with i ≟ x₁
  ... | yes as = let e1 = Eq.subst (λ x → hasValue x₁ y (updateState x f s)) as {!!} in
                 let e2 = hasValueSame x₁ y f s e1  in
                 CCEq (Eq.trans x₂ e2)
  ... | no  as = {!!}


  -}


  axiomOfAssignment s s' i e f (𝔹ℤ (eqPℤ (Var x) (Con x₁))) a p₁ p₂ h₁ = {!!}
  axiomOfAssignment s s' i e f (𝔹ℤ (eqPℤ (Var x) (Var x₁))) a p₁ p₂ h₁ = {!!}
  axiomOfAssignment s s' i e f (𝔹∧ p p₃) a p₁ p₂ h₁ = {!!}
  axiomOfAssignment s s' i e f (𝔹V p p₃) a p₁ p₂ h₁ = {!!}

  {-
  --
  axiomOfAssignment : ∀ (s : State) (x : Id) (f : ℤ) (p : Predicate) (assi : AssiProgram)
                      → holds  p  (evalAssi {x} {f} s assi)
                      → holds (sub f x p)  s
  axiomOfAssignment s x f (𝔹ℤ (eqPℤ (Con x₁) (Con x₂))) asi (CCEq x₃) = CCEq x₃
  axiomOfAssignment s x f (𝔹ℤ (eqPℤ (Con x₁) (Var x₂))) asi (CVEq x' y' s' id' x₃ x₄) with x ≟ x₂
  ... | yes z =  let e1 = hasValueSame x₂ y' f s in
                 let e2 = Eq.subst (λ x → hasValue x₂ y' (updateState x f s)) z x₄ in
                 CCEq (Eq.trans x₃ (e1 e2))
  ... | no z =  let d : ¬ x₂ ≡ x
                    d = λ e → ⊥-elim (z (Eq.sym e)) in
                let e1 = hasValueDiff x₂ x y' f s d x₄ in
                CVEq x₁ y' s x₂ x₃ e1
  axiomOfAssignment s x f (𝔹ℤ (eqPℤ (Var x₁) (Con x₂))) asi (VCEq .x₂ y .(updateState x f s) .x₁ x₃ x₄) with (x ≟ x₁)
  ... | yes p = let e1 = hasValueSame x₁ y f s in
                let e2 = e1 (Eq.subst _  p x₄) in
                CCEq (sym (Eq.trans x₃ e2))
  ... | no  ¬p = let d : ¬ x₁ ≡ x
                     d = λ e → ⊥-elim (¬p (sym e)) in
                 let e1 = hasValueDiff x₁ x y f s d x₄  in
                 VCEq x₂ y s x₁ x₃ e1
  axiomOfAssignment s x f (𝔹ℤ (eqPℤ (Var x₁) (Var x₂))) asi (VVEq x₃ y .(updateState x f s) .x₁ .x₂ x₄ x₅ x₆) with (x ≟ x₁) | (x ≟ x₂)
  ... | yes p | yes p₁ = CCEq refl
  ... | yes p | no ¬p = let d : ¬ x₂ ≡ x
                            d = λ e → ⊥-elim (¬p (sym e)) in
                        let e1 = hasValueDiff  x₂ x y f s d x₆ in
                        let fstsub = Eq.subst _ p x₅ in
                        let sndsub = Eq.subst _ x₄ fstsub in
                        let e2 = hasValueSame x₁ y f s sndsub in
                        CVEq f y s x₂ (sym e2) e1
  ... | no ¬p | yes p = let d : ¬ x₁ ≡ x
                            d = λ e → ⊥-elim (¬p (sym e)) in
                        let e1 = hasValueDiff x₁ x y f s d (Eq.subst _ x₄ x₅) in
                        let e2 = hasValueSame x₂ y f s (Eq.subst _ p x₆) in
                        VCEq f  y s x₁ (sym e2) e1
  ... | no ¬p | no ¬p₁ = let d1 : ¬ x₁ ≡ x
                             d1 = λ e → ⊥-elim (¬p (sym e)) in
                         let d2 : ¬ x₂ ≡ x
                             d2 = λ e → ⊥-elim (¬p₁ (sym e)) in
                         let e1 = hasValueDiff x₁ x x₃ f s d1 x₅  in
                         let e2 = hasValueDiff x₂ x y f s d2 x₆   in
                         VVEq x₃ y s x₁ x₂ x₄ e1 e2 
  axiomOfAssignment s x f (𝔹∧ p p₁) asi (ANDHolds .p .p₁ .(updateState x f s) h h₁) =
                         let IH1 = axiomOfAssignment s x f p asi h in
                         let IH2 = axiomOfAssignment s x f p₁ asi h₁ in
                         ANDHolds (sub f x p) (sub f x p₁) s IH1 IH2
  axiomOfAssignment s x f (𝔹V p p₁) asi (ORHoldL .p .p₁ .(updateState x f s) h) =
                         let IH = axiomOfAssignment s x f p asi h in
                         ORHoldL (sub f x p) _ s IH
  axiomOfAssignment s x f (𝔹V p p₁) asi (ORHoldR .p .p₁ .(updateState x f s) h)  =
                         let IH = axiomOfAssignment s x f p₁ asi h in
                         ORHoldR _ (sub f x p₁) s IH

  -}

  {-
  RuleOfConsequence1 : ∀ (s : State) → (prog : Program) → (p q r : Predicate) → ((holds q s) → (holds r s))
                                     → HoareTriple p prog q → HoareTriple p prog r


  RuleOfConsequence1 s prog p q r consequence trp = {!!}


  RuleOfConsequence2 : ∀ (s : State) → (prog : Program) → (p q r : Predicate) → ((holds p s) → (holds r s))
                                     → HoareTriple p prog q → HoareTriple r prog q




  RuleOfConsequence2 s prog p q r consequence trp = {!!}

  -}

 

  {-
  with x ≟ x₁
  ... | yes z = let e1 = hasValueSame x₁ y f s in
                let e2 = e1 (Eq.subst _ z x₄) in
                CCEq (Eq.sym (Eq.trans x₃ e2))
  ... | no z = let d : ¬ x₁ ≡ x
                   d = λ e → ⊥-elim (z (Eq.sym e)) in
               let e1 = hasValueDiff x₁ x y f s d x₄ in
               VCEq x₂ y s x₁ x₃ e1

  -}


  {-
  axiomOfAssignment {s} {x} {f} {𝔹ℤ (eqPℤ (Con x₁) (Con x₂))} {asi} (CCEq x₃) = CCEq x₃
  axiomOfAssignment {s} {x} {f} {𝔹ℤ (eqPℤ (Con x₁) (Var x₂))} {asi} (CVEq x₃ x₄ x₅) with ⌊ x ≟ x₂ ⌋
  ...                                                                                    | true  = let foo = x ≡ x₂ in  CCEq {!!} 
  ...                                                                                    | false = {!!}
  axiomOfAssignment {s} {x} {f} {𝔹ℤ (eqPℤ (Var x₁) x₂)} {asi} holdAfterAssi = {!!}
  axiomOfAssignment {s} {x} {f} {𝔹∧ p p₁} {asi} holdAfterAssi = {!!}
  axiomOfAssignment {s} {x} {f} {𝔹V p p₁} {asi} holdAfterAssi = {!!}
  -}

  
  



module Hoare where


  -- P₀ { x := f } P₁
  -- P₀ = any state in which f can be evaluated
  -- P₁ = state with x = f
  --axiomOfAssignment : {P₀ P₁ : S → Set} →
  --                    (∀ (s : S) → P₀ s ) →
                      
  

