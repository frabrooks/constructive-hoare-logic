


import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_  ; refl ; sym ; cong)
open import Relation.Nullary.Decidable using ( False ; True ; isYes ; isNo ; ⌊_⌋ )
open import Relation.Nullary  
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
open import Data.Empty using (⊥ ; ⊥-elim)


pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []



open import integer_operations


module Programs where

  open import Data.Product

  
  Identifier = ℕ

  data Expr  : Set where
    Constant : ℤ → Expr
    Var : Identifier → Expr
    Op : OpName → List Expr → Expr


  
  S = List (Identifier × ℤ) 
  -- Store = maybe some kind of stack instead?? 


  updateState : Identifier → ℤ → S → S
  updateState i z  []  = [( i ∧ z )]
  updateState i e ((fst ∧ snd) ∷ zs)  with ⌊ (fst ≟ i)  ⌋
  ...                                 | true = (i ∧ e) ∷ zs
  ...                                 | false = (fst ∧ snd ) ∷ updateState i e zs 
  

  getVar : Identifier → S → Maybe (ℤ)
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
  data ℤPropValue : List Identifier → Set where
    Con : ℤ → ℤPropValue []
    Var : ∀ {i : Identifier} → ℤPropValue (i ∷ []) 
    -- TODO: Add expressions so [(X + 1) > 3] can be a goal?


  data 𝔹PropValue : List Identifier → Set where
    Con : 𝔹 → 𝔹PropValue []
    --Var : Identifier → 𝔹PropValue


  data ℤProp : List Identifier → Set where
    eqPℤ      : ∀ {l r : List Identifier} → ℤPropValue l → ℤPropValue r → ℤProp (l ++ r)
    LeqPℤ     : ∀ {l r : List Identifier} → ℤPropValue l → ℤPropValue r → ℤProp (l ++ r)
    LessPℤ    : ∀ {l r : List Identifier} → ℤPropValue l → ℤPropValue r → ℤProp (l ++ r)
    GeqPℤ     : ∀ {l r : List Identifier} → ℤPropValue l → ℤPropValue r → ℤProp (l ++ r)
    GreaterPℤ : ∀ {l r : List Identifier} → ℤPropValue l → ℤPropValue r → ℤProp (l ++ r)
  -}

  {- Trying: Add List Identifier as indexed data type ? -}
  
  data ℤPropValue : Set where
    Con : ℤ → ℤPropValue
    Var : Identifier → ℤPropValue
    -- TODO: Add expressions so [(X + 1) > 3] can be a goal?


  data 𝔹PropValue : Set where
    Con : 𝔹 → 𝔹PropValue
    --Var : Identifier → 𝔹PropValue


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
  data PROPO : List Identifier → Set where
    𝔹•       : ∀ {l : List Identifier} → 𝔹PropValue l → PROPO l
    𝔹ℤ       : ∀ {l : List Identifier} → ℤProp l → PROPO l
    eq𝔹      : ∀ {l r : List Identifier} → PROPO l → PROPO r → PROPO (l ++ r) -- does this make sense???
    𝔹∧       : ∀ {l r : List Identifier} → PROPO l → PROPO r → PROPO (l ++ r)
    𝔹V       : ∀ {l r : List Identifier} → PROPO l → PROPO r → PROPO (l ++ r)


  data holds : {ls : List Identifier} → S → PROPO ls → Set where
    CCEq :  ∀ {x y : ℤ} → {s : S} → (x ≡ y) → holds s (𝔹ℤ    (eqPℤ (Con x) (Con y))  )
    VCEq :  ∀ {x y : ℤ} → {id : Identifier} → {s : S} → (𝔹ℤ  (eqPℤ  ?       ?    ) )  
  -}


  
  {-    
  data holds : List Identifier → PROPO → S → Set where
    CCEq : ∀ {vars : Identifier} → {x y : ℤ} → { s : S } → ( x ≡ y ) → holds vars ( 𝔹ℤ (eqPℤ (Con x) (Con y) ) ) s
    CVEq : ∀ {vars : Identifier} → {x y : ℤ} → { s : S } → {id idₛ : Identifier} → ( x ≡ y ) → (id ≡ idₛ) → holds vars (𝔹ℤ (eqPℤ (Con x) (Var id))) ((idₛ , y) ∷ s )  
    VCEq : ∀ {vars : Identifier} → {x y : ℤ} → { s : S } → {id idₛ : Identifier} → ( x ≡ y ) → (id ≡ idₛ) → holds vars (𝔹ℤ (eqPℤ (Var id) (Con x))) ((idₛ , y) ∷ s )
    VVEq : ∀ {vars : Identifier} → {x y : ℤ} → { s : S } → {id₁ id₂ idₛ₁ idₛ₂ : Identifier} → ( x ≡ y ) → (id₁ ≡ idₛ₁) → (id₂ ≡ idₛ₂) → holds vars (𝔹ℤ (eqPℤ (Var id₁) (Var id₂))) ((id₁ , x) ∷ (id₂ , y) ∷ s)
    ANDHolds : ∀ {vars : Identifier} → {p q : PROPO} → {s : S} → holds vars p s → holds vars q s → holds vars (𝔹∧ p q) s
    ORHoldL  : ∀ {vars : Identifier} → {p q : PROPO} → {s : S} → holds vars p s → holds vars (𝔹V p q) s
    ORHoldR  : ∀ {vars : Identifier} → {p q : PROPO} → {s : S} → holds vars q s → holds vars (𝔹V p q) s
  -}


  {-
  data hasValue : Identifier → ℤ → S → Set where
    singleton : ∀ {i : Identifier} → {z : ℤ} → {s : S} →  hasValue i z ((i , z) ∷ s )
    elsewhere : ∀ {i j : Identifier} → {z y : ℤ} → {s : S} →  hasValue i z s → hasValue i z ((j , y) ∷ s )
  -}


  -- This doesn't seem to be working too well with the function 'getVar' within the constructor. Going to try and change to have the same property encoded in a data type
  data holds : PROPO → S → Set where
    CCEq : ∀ {x y : ℤ} → { s : S } → ( x ≡ y ) → holds ( 𝔹ℤ (eqPℤ (Con x) (Con y) ) ) s
    CVEq : ∀ {x y : ℤ} → { s : S } → {id : Identifier} → ( x ≡ y ) → getVar id s ≡ just (y) →  holds (𝔹ℤ (eqPℤ (Con x) (Var id))) s  
    VCEq : ∀ {x y : ℤ} → { s : S } → {id : Identifier} → ( x ≡ y ) → getVar id s ≡ just (y) →  holds (𝔹ℤ (eqPℤ (Var id) (Con x))) s
    VVEq : ∀ {x y : ℤ} → { s : S } → {id₁ id₂ : Identifier} → ( x ≡ y ) → getVar id₁ s ≡ just (x) → getVar id₂ s ≡ just (y) → holds (𝔹ℤ (eqPℤ (Var id₁) (Var id₂))) s
    ANDHolds : ∀ {p q : PROPO} → {s : S} → holds p s → holds q s → holds (𝔹∧ p q) s
    ORHoldL  : ∀ {p q : PROPO} → {s : S} → holds p s → holds (𝔹V p q) s
    ORHoldR  : ∀ {p q : PROPO} → {s : S} → holds q s → holds (𝔹V p q) s
  
  {-
  data holds : PROPO → S → Set where
    CCEq : ∀ {x y : ℤ} → { s : S } → ( x ≡ y ) → holds ( 𝔹ℤ (eqPℤ (Con x) (Con y) ) ) s
    CVEq : ∀ {x y : ℤ} → { s : S } → {id : Identifier} → ( x ≡ y ) → hasValue id y s →  holds (𝔹ℤ (eqPℤ (Con x) (Var id))) s  
    VCEq : ∀ {x y : ℤ} → { s : S } → {id : Identifier} → ( x ≡ y ) → hasValue id y s →  holds (𝔹ℤ (eqPℤ (Var id) (Con x))) s
    VVEq : ∀ {x y : ℤ} → { s : S } → {id₁ id₂ : Identifier} → ( x ≡ y ) → hasValue id₁ x s → hasValue id₂ y s → holds (𝔹ℤ (eqPℤ (Var id₁) (Var id₂))) s
    ANDHolds : ∀ {p q : PROPO} → {s : S} → holds p s → holds q s → holds (𝔹∧ p q) s
    ORHoldL  : ∀ {p q : PROPO} → {s : S} → holds p s → holds (𝔹V p q) s
    ORHoldR  : ∀ {p q : PROPO} → {s : S} → holds q s → holds (𝔹V p q) s
 -}

  sub : ℤ → Identifier → PROPO → PROPO
  sub f i (𝔹• (Con x)) = 𝔹• (Con x)
  sub f i (𝔹ℤ (eqPℤ (Con x) (Con x₁))) = 𝔹ℤ (eqPℤ (Con x) (Con x₁))
  sub f i (𝔹ℤ (eqPℤ (Con x) (Var x₁))) with ⌊ i ≟ x₁ ⌋
  ...                                       | true = 𝔹ℤ (eqPℤ (Con x) (Con f))
  ...                                       | false = 𝔹ℤ (eqPℤ (Con x) (Var x₁))
  sub f i (𝔹ℤ (eqPℤ (Var x) (Con x₁))) with ⌊ i ≟ x ⌋
  ...                                       | true = 𝔹ℤ (eqPℤ (Con f) (Con x₁))
  ...                                       | false = 𝔹ℤ (eqPℤ (Var x) (Con x₁))
  sub f i (𝔹ℤ (eqPℤ (Var x) (Var x₁))) with ⌊ i ≟ x ⌋ | ⌊ i ≟ x₁ ⌋
  ...                                       | true  | true = 𝔹ℤ (eqPℤ (Con f) (Con f))
  ...                                       | true  | false = 𝔹ℤ (eqPℤ (Con f) (Var x₁))
  ...                                       | false | true = 𝔹ℤ (eqPℤ (Var x₁) (Con f))
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



  data AssiProgram : Identifier → ℤ → Set where
    asi : {id : Identifier} → {f : ℤ} →  AssiProgram id f 


  -- Need to figure out how to get around Maybe on retreival from storage??
  evalAssi : ∀ {i : Identifier} → {f : ℤ} → S → AssiProgram i f → S
  evalAssi   {i} {f}  s asi  = updateState i f s
  --evalAssi {id} {Var x} s asi = updateState id {!getVar x s = Maybe!} {!!}

  {-
  data isEq : ℤProp → Set where
    •• : isEq eqPℤ 
  -}



  
  {-
  test : ∀ {s : S} → {f : ℤ} → { p : PROPO } → ( x y : Identifier ) → ( ( x ≡ y ) → ⊥ ) → holds p ( ( x ∧ f ) ∷ s ) → holds p s
  test {s} {f} {.(𝔹ℤ (eqPℤ (Con _) (Con _)))} x y no (CCEq x₁) = CCEq x₁
  test {.[]} {f} {.(𝔹ℤ (eqPℤ (Con f) (Var x)))} x y no (CVEq refl singleton) = CVEq {!!} {!!}
  test {s} {f} {.(𝔹ℤ (eqPℤ (Con f) (Var x)))} x y no (CVEq refl elsewhere) = CVEq {!!} {!!}
  test {s} {f} {.(𝔹ℤ (eqPℤ (Var _) (Con _)))} x y no (VCEq x₁ x₂) = {!!}
  test {s} {f} {.(𝔹ℤ (eqPℤ (Var _) (Var _)))} x y no (VVEq x₁ x₂ x₃) = {!!}
  test {s} {f} {.(𝔹∧ _ _)} x y no (ANDHolds h h₁) = {!!}
  test {s} {f} {.(𝔹V _ _)} x y no (ORHoldL h) = {!!}
  test {s} {f} {.(𝔹V _ _)} x y no (ORHoldR h) = {!!}
  -}
  

  drop-just : ∀ {A : Set} → {x y : A} →
            just x ≡ just y → x ≡ y
  drop-just refl = refl


  simpleGet : ∀ (s : S) → (x : Identifier) → (f y : ℤ) → getVar x (updateState x f s)  ≡ just y → f ≡ y
  simpleGet [] x f y get with ⌊ x ≟ x  ⌋
  ...                         | true = drop-just get
  simpleGet (x₁ ∷ s) x f y get with ⌊ proj₁ x₁ ≟ x ⌋
  ...                               | false = {!!}
  ...                               | true with ⌊ x ≟ x ⌋
  ...                                           | false = {!!}
  ...                                           | true = drop-just get


 

  {-
  _=?′_ : ∀ (m n : ℕ) → Dec (m ≡ n)
  m =?′ n with m ≟ n | ≤ᵇ→≤ m n | ≤→≤ᵇ {m} {n}
  ...        | true   | p        | _            = yes (p tt)
  ...        | false  | _        | ¬p           = no ¬p
  -}



  -- = hasValueDiff does this much better perhaps
  lemm : ∀ {s : S} → { id₁ id₂ : Identifier} → {y f : ℤ} → ((id₁ ≡ id₂) → ⊥) → getVar id₁ ((id₂ , f) ∷ s) ≡ just y → getVar id₁ s ≡ just y
  lemm {[]} {id₁} {id₂} {y} {f} noteq get= with (id₁ ≟ id₂)
  ... | .true because ofʸ p = ⊥-elim (noteq p)
  lemm {(fst , snd) ∷ s} {id₁} {id₂} {y} {f} noteq get=  with (id₁ ≟ id₂) | (id₁ ≟ fst) | (fst ≟ id₂)
  ... | .true because ofʸ p   | _  | _ =  ⊥-elim (noteq p)
  ... | .false because ofⁿ ¬p | .true because ofʸ p | .true because ofʸ p₁ = let IH = lemm {s} {id₁} {id₂} {y} {f} noteq {!!} in {!!}
  ... | .false because ofⁿ ¬p | .true because ofʸ p | .false because ofⁿ ¬p₁ = let IH = lemm {s} {id₁} {id₂} {y} {f} noteq {!!} in {!!}
  ... | .false because ofⁿ ¬p | .false because ofⁿ ¬p₁ | aa = let IH = lemm {s} {id₁} {id₂} {y} {f} noteq {!!} in {!!}



  lem : ∀ {s : S}  → { id₁ id₂ : Identifier} → {y f : ℤ} → getVar id₁ ((id₂ , f ) ∷ [] ) ≡ just y  → (id₁ ≡ id₂)
  lem  {s} {i} {ii} {y} {f} gv with ( i ≟ ii )
  ... | .true because ofʸ p = p


  lem2 : ∀ {s : S} → { id₁ id₂ : Identifier} → {y f : ℤ} → getVar id₁ ((id₂ , f) ∷ s ) ≡ just y → getVar id₁ s ≡ nothing → (id₁ ≡ id₂)
  lem2  {s} {id₁} {id₂} {y}  {f}  gv noth with (id₁ ≟ id₂)
  ... | .true because ofʸ   p    =  p
  ... | .false because ofⁿ ¬p rewrite noth   = ⊥-elim (just≢nothing gv)
    where just≢nothing : ∀ {A : Set} → {a : A} → nothing ≡ just a → ⊥
          just≢nothing ()


  
  lem3 : ∀ {s : S} → { id₁ : Identifier} → {y  f : ℤ} → getVar id₁ ((id₁ , f) ∷ s ) ≡ just y → getVar id₁ [ (id₁ , f) ] ≡ just y 
  lem3 {[]} {id₁} {y} {f} gv = gv
  lem3 {(fst , snd) ∷ s} {id₁} {y} {f} gv with (id₁ ≟ id₁)
  ... | .true because ofʸ p = gv
  ... | .false because ofⁿ ¬p = ⊥-elim (¬p refl)


  lem4 : ∀ { id₁ id₂ : Identifier} → {z : ℤ} → ((id₁ ≡ id₂) → ⊥ ) → getVar id₁ [ (id₂ , z ) ] ≡ nothing
  lem4   {id₁} {id₂} {z} noteq with (id₁ ≟ id₂)
  ... | .true because ofʸ p = ⊥-elim (noteq p)
  ... | .false because ofⁿ ¬p = refl


  valueAfterUpdate : ∀ {s : S} → { id₁ id₂ : Identifier } → {y f : ℤ } → ((id₁ ≡ id₂) → ⊥) → getVar id₁ (updateState id₂ f s) ≡ just y → getVar id₁ s ≡ just  y
  valueAfterUpdate {[]} {id₁} {id₂} {y} {f} noteq get= with (id₁ ≟ id₂)
  ... | .true because ofʸ p = ⊥-elim (noteq p)
  valueAfterUpdate { [ (fst , snd) ] } {id₁} {id₂} {y} {f} noteq get= with (fst ≟ id₂) | (fst ≟ id₁)
  ... | .true because ofʸ p | .true because ofʸ p₁ rewrite p = ⊥-elim (noteq (sym p₁))
  ... | .true because ofʸ p | .false because ofⁿ ¬p = ⊥-elim (noteq (lem {[]} {id₁} {id₂} {y} {f} get=))
  ... | .false because ofⁿ ¬p | .true because ofʸ p rewrite p = lem3 {[ (id₂ , f ) ]} {id₁}   {y} {snd} get=
  ... | .false because ofⁿ ¬p | .false because ofⁿ ¬p₁ = ⊥-elim (¬p₁ ( sym (lem2 {[ ( id₂ , f )  ]} {id₁} {fst} {y} {snd}  get= (lem4 {id₁} {id₂} {f} noteq))))
  valueAfterUpdate {(fst , snd) ∷ x ∷ s} {id₁} {id₂} {y} {f} noteq get= = {!!} -- Here's the problem: List's really don't seem to be working. Unless there is a way to generalise all the above lemmas beyond singletons


  {-
  valueAfterUpdate {[]} {id₁} {.id₁} {y} {.y} noteq singleton = ⊥-elim (noteq refl) 
  valueAfterUpdate {(fst , snd) ∷ s} {id₁} {id₂} {y} {f} noteq h with (fst ≟ id₂)
  ... | .true because ofʸ p = valueAfterUpdate ( noteq ) {!!}
  ... | .false because ofⁿ ¬p = {!!}
  -}
  


  
  axiomOfAssignment : ∀ {s : S} → {x : Identifier} → {f : ℤ}  → { p : PROPO } → { assi : AssiProgram x f } 
                                → holds  p  (evalAssi {x} {f}  s assi )                                                                
                                → holds (sub f x p)  s
  axiomOfAssignment {s} {x} {f} {𝔹ℤ (eqPℤ (Con x₁) (Con x₂))} {asi} (CCEq x₃) = CCEq x₃
  axiomOfAssignment {s} {x} {f} {𝔹ℤ (eqPℤ (Con x₁) (Var x₂))} {asi} hlds with  ( x ≟ x₂ )
  axiomOfAssignment {s} {x} {f} {𝔹ℤ (eqPℤ (Con x₁) (Var x₂))} {asi} (CVEq x₃ x₄) | .true because ofʸ p = CCEq {!!}
  axiomOfAssignment {s} {x} {f} {𝔹ℤ (eqPℤ (Con x₁) (Var x₂))} {asi} (CVEq x₃ x₄) | .false because ofⁿ ¬p = {!!}
  axiomOfAssignment {s} {x} {f} {𝔹ℤ (eqPℤ (Var x₁) (Con x₂))} {asi} h = {!!}
  axiomOfAssignment {s} {x} {f} {𝔹ℤ (eqPℤ (Var x₁) (Var x₂))} {asi} h = {!!}
  axiomOfAssignment {s} {x} {f} {𝔹∧ p p₁} {asi} h = {!!}
  axiomOfAssignment {s} {x} {f} {𝔹V p p₁} {asi} h = {!!}
  


  {-
  axiomOfAssignment {s} {x} {f} {𝔹ℤ (eqPℤ (Con x₁) (Con x₂))} {asi} (CCEq x₃) = CCEq x₃
  axiomOfAssignment {s} {x} {f} {𝔹ℤ (eqPℤ (Con x₁) (Var x₂))} {asi} (CVEq x₃ x₄ x₅) with ⌊ x ≟ x₂ ⌋
  ...                                                                                    | true  = let foo = x ≡ x₂ in  CCEq {!!} 
  ...                                                                                    | false = {!!}
  axiomOfAssignment {s} {x} {f} {𝔹ℤ (eqPℤ (Var x₁) x₂)} {asi} holdAfterAssi = {!!}
  axiomOfAssignment {s} {x} {f} {𝔹∧ p p₁} {asi} holdAfterAssi = {!!}
  axiomOfAssignment {s} {x} {f} {𝔹V p p₁} {asi} holdAfterAssi = {!!}
  -}

  

  data Program : Set where
    Block : List Program → Program
    Assignment : Identifier → Expr → Program
    While : Expr → Program -> Program
    If : Expr → Program -> Program
    IfElse : Expr → Program → Program -> Program
       




module Hoare where


  -- P₀ { x := f } P₁
  -- P₀ = any state in which f can be evaluated
  -- P₁ = state with x = f
  --axiomOfAssignment : {P₀ P₁ : S → Set} →
  --                    (∀ (s : S) → P₀ s ) →
                      
  

