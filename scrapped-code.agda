
  data _⊎_ : Set → Set → Set where

    inj₁ : ∀ {A B : Set} → A → A ⊎ B
    inj₂ : ∀ {A B : Set} → B → A ⊎ B


  infix 1 _⊎_

  ⊎E : {A B C : Set} → A ⊎ B → (A → C) → (B → C) → C
  ⊎E (inj₁ a) f g = f a
  ⊎E (inj₂ b) f g = g b 


  data _xx_ (A : Set) (B : Set) : Set where

    ⟨_,_⟩ : A → B → A xx B

  
  data even : ℕ → Set
  data odd  : ℕ → Set

  data even where
    even-zero : even zero
    even-suc : ∀ {n : ℕ} → odd n → even (suc n)

  data odd where
    odd-suc : ∀ {n : ℕ} → even n → odd (suc n)


  oddeven : ∀ n → odd n ⊎ even n
  oddeven zero =  inj₂  even-zero
  oddeven (suc n) = ⊎E (oddeven n) (λ z → inj₂ (even-suc z)) λ z → inj₁ (odd-suc z)


  open import Level

  data _×ℓ_ {m n : Level} (A : Set n ) (B : Set m) : Set (n ⊔ m ) where
   _,_ : A → B → A ×ℓ B


  {-
  evalℤProp : ℤPropValue → ℤProp → ℤPropValue → S →  Set ×ℓ Set  
  evalℤProp (Con x) eqPℤ (Con x₁) s = ( x ≡ x₁ ) , ⊤  
  evalℤProp (Con x) eqPℤ (Var x₁) ((fst , snd) ∷ _ ) =  (x₁ ≡ fst) , (x ≡ snd)
  evalℤProp (Var x) eqPℤ (Con x₁) ((fst , snd) ∷ _ ) = (x ≡ fst) , (x₁ ≡ snd)
  evalℤProp (Var x) eqPℤ (Var x₁) ((fst , snd) ∷ (fst₁ , snd₁) ∷ s) = (x ≡ fst) , ((snd ≡ snd₁) , (x₁ ≡ fst₁))
  -}

-- Need to figure out how to get around Maybe on retreival from storage?? -- (THIS IS RELATED TO FINDING A WAY FOR f TO BE AN EXPRESSION)


{-
  data Assertion : Set where
    Predic : Assertion → Assertion → Proposition → Assertion
    Propos : Value → Value → Proposition → Assertion

  evalProp : 

  evalAssertion : Assertion → S → Bool
  evalAssertion (Predic a₁ a₂ p) s = {!(evalAssertion a₁ s)!}
  evalAssertion (Propos x x₁ x₂) s = {!!}
  -}
  {-
  data Holds : Set where
    h : Holds 


  holds : Assertion → S → ⊤
  holds = λ _ _ → tt
  -}


  {-
  data Condition : Set where
    con : 
  -}

  -- Assertion =   Expr -- > S  -- > Set


  
  

  {-
  --                        ∀ s : S → P ( evalAssig s a) → P (updateState x₁ s x₂  )
  axiomOfAssi : ∀ (s : S) → ∀ (a : Assignment') → ∀ (P : S → Set) → P (evalAssig s a) → ((s' : S) → P s')
  axiomOfAssi s (x₁ := x₂) P x = let ss = updateState x₁ s x₂ in   {!!}

  --axiomOfAssi : ∀ (s : S) → ∀ (P : S → Set) → (P s) → (a : Assignment') → (P ( evalAssig s a))
  --axiomOfAssi s P x (x₁ := x₂) = {!!}


  data Hoare  (Q R : S → Set) : Assignment' → Set where

    h : {a : Assignment'} →  ∀ (s : S) → Q s → R (evalAssig s a) → Hoare Q R a 
  -}

--  h : (∀ s : S) → (∀ q : Q) → (∀ r : R) → (∀ a : Assigment') → Q s → r (evalAssig s a) → Hoare q a r


-- ASSERTION and Store/State are not the same thing

-- ASSERTION: 


-- ∀ i Identifier →
--   ∀ z Value (ℤ)  →
--   P₀ i s 


-- in
-- data _∈_ : (Identifier × ℤ) → S → Set where




--data HTrip {Q R : S → Set} Q → Program → R : Set where

--  t : (q : Q) → (s : Program) → (r : R) → eval





-- ⌊ i ≟ fst ⌋



-- {Q} S {R}



  -- Need to look at isEq eq as that seems bad = DONE
  -- Probs need embedding of actual propositional language over ℤPropValue = DONE
  -- Needs tree like structure here so we can do: (holds tree eval...) → (holds (SUB x f tree ) eval...) = DONE
  




  -- LOOK BACK AT WHAT WAS CAUSING YOU TO WORRY ABOUT LIST REPRESENTATION
  

{- 


State of project:


 - Sets in Agda, representing State/Store as list

 - Deep embedding of first order propositional calculus and shallow embedding of? ...





    free variables in 'holds'*
   - this would be useful for both Hoare and Separation logic I reckon
   - at the moment, using And within holds to build up bigger expressions, we have the problem that - no! actually I don't think there is a problem. With separation logic however there will be a problem when we come to introduce the frame rule.




  is-pos : ℤ → ℤ
  is-pos (pos    _) = pos 1
  is-pos (negsuc _) = pos 0

  opEval : OpName → List ( Maybe ℤ ) → Maybe ℤ
  opEval ||𝓬  [ x , y ]  =   orℤ <$>ₘ  x ⊛ₘ y
    where
    orℤ : ℤ → ℤ → ℤ
    orℤ (pos 0) (pos 0) = pos 0
    orℤ (pos n)    _    = pos 1
    orℤ   _    (pos n)  = pos 1
    orℤ   _     _       = pos 0
  opEval &&𝓬  [ x ,  y ]  = andℤ <$>ₘ x ⊛ₘ y
    where
    andℤ : ℤ → ℤ → ℤ
    andℤ (pos 0)  _      = pos 0
    andℤ  _      (pos 0) = pos 0
    andℤ (pos _) (pos _) = pos 1
    andℤ  _       _      = pos 0
  opEval ==𝓬   [ x , y  ]       = eqℤ <$>ₘ x ⊛ₘ y
    where
    is-zero : ℤ → ℤ
    is-zero (pos 0) = pos 1
    is-zero    _    = pos 0
    eqℤ : ℤ → ℤ → ℤ
    eqℤ   x   y = is-zero (x - y)
  opEval ≤𝓬  [ x , y ]      = leqℤ <$>ₘ x ⊛ₘ y -- x ≤ y
    where
    is-neg : ℤ → ℤ
    is-neg (negsuc _) = pos 1
    is-neg (pos    _) = pos 0
    leqℤ : ℤ → ℤ → ℤ
    leqℤ   x   y = is-neg ((x - y) - (pos 1))
  opEval <𝓬   [ x , y ]     = lessℤ <$>ₘ x ⊛ₘ y -- x < y
    where
    is-neg : ℤ → ℤ
    is-neg (negsuc _) = pos 1
    is-neg (pos    _) = pos 0
    lessℤ : ℤ → ℤ → ℤ
    lessℤ   x   y = is-neg (x - y)
  opEval ≥𝓬  [ x , y ]    = geqℤ <$>ₘ x ⊛ₘ y  -- x ≥ y
    where
    geqℤ : ℤ → ℤ → ℤ
    geqℤ   x   y = is-pos (x - y)
  opEval >𝓬 [ x , y ]     = greaterℤ <$>ₘ x ⊛ₘ y -- x > y
    where
    greaterℤ : ℤ → ℤ → ℤ
    greaterℤ   x   y = is-pos ((x - y) - (pos 1))
  opEval +𝓬  [ x , y ]  = (_+_)   <$>ₘ x ⊛ₘ y
  opEval -𝓬  [ x , y ]  = (_-_)   <$>ₘ x ⊛ₘ y
  opEval *𝓬  [ x , y ]  = (_*_)   <$>ₘ x ⊛ₘ y
  opEval /𝓬  [ x , y ]  = (maybeDiv y)  ⊛ₘ x 
    where
    maybe≢0 : (z : ℤ) →  Maybe ( False ( ∣ z ∣ ℕ.≟ 0) )
    maybe≢0 (pos ℕ.zero)         = nothing
    maybe≢0 (Int.+[1+ n ])       = just (tt)
    maybe≢0 (negsuc n)           = just (tt)
    maybeDiv : Maybe ℤ → Maybe (ℤ → ℤ)
    maybeDiv nothing = nothing
    maybeDiv (just divisor) = (λ p → (λ z₁ → (z₁ div divisor) {p} )) <$>ₘ (maybe≢0 divisor)
  opEval %𝓬  [ x , y ]  = (maybeMod y)  ⊛ₘ x 
    where
    maybe≢0 : (z : ℤ) →  Maybe ( False ( ∣ z ∣ ℕ.≟ 0) )
    maybe≢0 (pos ℕ.zero)         = nothing
    maybe≢0 (Int.+[1+ n ])       = just (tt)
    maybe≢0 (negsuc n)           = just (tt)
    maybeMod : Maybe ℤ → Maybe (ℤ → ℤ)
    maybeMod nothing = nothing
    maybeMod (just divisor) = (λ p → (λ z₁ → pos ((z₁ mod divisor) {p}))) <$>ₘ (maybe≢0 divisor)
  opEval !𝓬  [ x ]      = x >>=ₘ notℤ 
    where
    notℤ : ℤ → Maybe ℤ
    notℤ (pos ℕ.zero) = just (pos 1)
    notℤ Int.+[1+ ℕ.zero ] = just (pos 0)
    notℤ Int.+[1+ ℕ.suc n ] = nothing
    notℤ (negsuc n) = nothing
  opEval _     _           = nothing



  evalArgs : S → List Expr → List (Maybe ℤ) -- Val 
  evalArgs s [] = []
  evalArgs s (Constant x ∷ es) = (just x) ∷ evalArgs s es
  evalArgs s (Var x ∷ es)      = (getVar x s) ∷ evalArgs s es 
  evalArgs s (Op op exps ∷ es) = let args = evalArgs s exps in (opEval op args) ∷ evalArgs s es

  
  eval :  Expr → S -> Maybe ℤ -- Val
  eval (Constant x) s = just x
  eval (Var x)      s = getVar x s
  eval (Op op exps) s = opEval op (evalArgs s exps)






  -- Penultimate Exp solution

  
  {-
  data 𝔹Op : Set where

    -- Logical OR
    || : 𝔹Op  

    -- Logical AND
    && : 𝔹Op

    -- Equality Operators
    == : 𝔹Op

    -- Relational Operators
    ≤ : 𝔹Op
    ≥ : 𝔹Op
    < : 𝔹Op
    > : 𝔹Op

    -- Not
    ! : 𝔹Op
  
  data ℤOp : Set where

    +𝓬 : ℤOp
    -𝓬 : ℤOp

    *𝓬 : ℤOp
    /𝓬 : ℤOp
    %𝓬 : ℤOp
    

  -- Operators for the Expressions in the Mini C-like language
  data Operator : Set where

    -- Boolean Operators
    _:𝔹 : 𝔹Op → Operator

    -- Integer Operators
    _:ℤ : ℤOp → Operator

  

  data Expr : Set where
    Constant : Val → Expr
    Var      : Id → Expr
    ℤExp    : ℤOp → List ℤExp → Expr 
    𝔹Exp    : 𝔹Op → List 𝔹Exp → Expr


  -- Evaluation of expressions
  evalExp :  Expr → S -> Maybe Val
  evalExp (Constant x) s = just x
  evalExp (Var x)      s = getVarVal x s
  evalExp (Op op exps) s = opEval op (evalArgs s exps)
    where
    evalArgs : S → List Expr → List (Maybe Val)
    evalArgs s [] = []
    evalArgs s (Constant x ∷ es) = (just x) ∷ evalArgs s es
    evalArgs s (Var x ∷ es)      = (getVarVal x s) ∷ evalArgs s es 
    evalArgs s (Op op exps ∷ es) = let args = evalArgs s exps in (opEval op args) ∷ evalArgs s es


  -}




  {-

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
  
















-}





















