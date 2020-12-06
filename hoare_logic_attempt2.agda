


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


pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []



open import integer_operations


module Programs where

  open import Data.Product


  Id = ℕ
  Val = ℤ

  data Expr  : Set where
    Constant : Val → Expr
    Var : Id → Expr
    Op : OpName → List Expr → Expr


  Entry = Id × Val

  S = List Entry

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



  data hasValue : Id → ℤ → S → Set where
    atthehead : ∀ i z s → hasValue i z ((i , z) ∷ s)
    elsewhere : ∀ i j z w s s' → i ≡ j → ⊥ → hasValue i z s → s' ≡ ((j , w) ∷ s ) → hasValue i z s'



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



  data AssiProgram : Id → ℤ → Set where
    asi : {id : Id} → {f : ℤ} →  AssiProgram id f 


  -- Need to figure out how to get around Maybe on retreival from storage??
  evalAssi : ∀ {i : Id} → {f : ℤ} → S → AssiProgram i f → S
  evalAssi   {i} {f}  s asi  = updateState i f s
  --evalAssi {id} {Var x} s asi = updateState id {!getVar x s = Maybe!} {!!}

  {-
  data isEq : ℤProp → Set where
    •• : isEq eqPℤ 
  -}



  

{-
  test : ∀ {s : S} → {f : ℤ} → { p : PROPO } → ( x y : Id ) → ( ( x ≡ y ) → ⊥ ) → holds p ( ( x ∧ f ) ∷ s ) → holds p s
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

{-
  simpleGet : ∀ (s : S) → (x : Id) → (f y : ℤ) → getVar x (updateState x f s)  ≡ just y → f ≡ y
  simpleGet [] x f y get with ⌊ x ≟ x  ⌋
  ...                         | true = drop-just get
  simpleGet (x₁ ∷ s) x f y get with ⌊ proj₁ x₁ ≟ x ⌋
  ...                               | false = {!!}
  ...                               | true with ⌊ x ≟ x ⌋
  ...                                           | false = {!!}
  ...                                           | true = drop-just get
-}


  --
  hasValueSame' : ∀ x y f s s' → s' ≡ (updateState x f s) → hasValue x y s' → y ≡ f
  hasValueSame' x y .y [] .([ (x , y) ]) refl (atthehead .x .y .[]) = refl
  hasValueSame' x y f (x₁ ∷ s) .((x , y) ∷ s₁) w (atthehead .x .y s₁) with proj₁ x₁ ≟ x
  hasValueSame' x y .y (x₁ ∷ s) ((.x , .y) ∷ .s) refl (atthehead .x .y .s) | yes _ = refl
  hasValueSame' x y f (.(x , y) ∷ s) ((.x , .y) ∷ .(updateState x f s)) refl (atthehead .x .y .(updateState x f s)) | no p = ⊥-elim (p refl)

  hasValueSame : ∀ x y f s → hasValue x y (updateState x f s) → y ≡ f
  hasValueSame x y f s hv =  hasValueSame' x y f s (updateState x f s) refl hv


  --
  hasValueDiff' : ∀ x x' y f s s' → ¬ x ≡ x' → s' ≡ (updateState x' f s) → hasValue x y s' → hasValue x y s
  hasValueDiff' x .x y .y [] .([( x , y )]) d refl (atthehead .x .y .[]) = ⊥-elim (d refl)
  hasValueDiff' x x' y f ((fst , snd) ∷ s) .((x , y) ∷ s₁) d e (atthehead .x .y s₁) with fst ≟ x'
  hasValueDiff' .x' x' y .y ((fst , snd) ∷ s) ((.x' , .y) ∷ .s) d refl (atthehead .x' .y .s) | yes p = ⊥-elim (d refl)
  hasValueDiff' .fst x' y f ((fst , .y) ∷ s) ((.fst , .y) ∷ .(updateState x' f s)) d refl (atthehead .fst .y .(updateState x' f s)) | no p = atthehead fst y s


  hasValueDiff : ∀ x x' y f s → ¬ x ≡ x' → hasValue x y (updateState x' f s) → hasValue x y s
  hasValueDiff x x' y f s d hv =  hasValueDiff' x x' y f s (updateState x' f s) d refl hv


  --
  axiomOfAssignment : ∀ (s : S) (x : Id) (f : ℤ) (p : PROPO) (assi : AssiProgram x f)
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

  

  data Program : Set where
    Block : List Program → Program
    Assignment : Id → Expr → Program
    While : Expr → Program -> Program
    If : Expr → Program -> Program
    IfElse : Expr → Program → Program -> Program
       




module Hoare where


  -- P₀ { x := f } P₁
  -- P₀ = any state in which f can be evaluated
  -- P₁ = state with x = f
  --axiomOfAssignment : {P₀ P₁ : S → Set} →
  --                    (∀ (s : S) → P₀ s ) →
                      
  

