
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
  





  -- A predicate is a subset of ( S × Exp ) s.t.
  -- evalExp exp s ≡ true ∨ false and (exp is WFF)

  {-
  𝐴 = Σ[ e ∈ Exp ] ( ( s : S ) →  Is-just (evalExp e s)
    → ( evalExp e s ≡ just 𝑻 ) ⊎ ( evalExp e s ≡ just 𝑭 ))
  -- THIS DEFINITION IS BROKEN, (Const 1) + (Const 0) is
  -- a valid predicate!
  -}





-- For an assertion to hold and or be inhabited it must
  -- evaluate successfully (Σ (Is-just _)), and the result
  -- of this evaluation must be the left projection of 𝐴
  -- (namely, the case where evalExp e s ≡ just 𝑻)

  ------------------
  --Assert : ∀ {e} {s} → 𝑃 e s → Set
  --Assert (pred wff) = T $ toTruthValue wff



  {-
  _⇒_ :  𝑃 → 𝑃 → Set
  P@(e , s , wffp) ⇒ Q = Σ (WFF (evalExp e s (proj₁ Q)))
                           (λ wffq → (Assert P → (T $ toTruthValue wffq)))
  -}





  -- test : ∀ {s} (P : 𝑃 e1 s) → (Q : 𝑃 e2 s) → P ⇒ Q

{-
  test : ∀ {s} (P : 𝑃 e1 s) → (Q : 𝑃 e2 s) → P ⇒ Q
  test  {s} (pred wffp) (pred wffq)  assert =
       ConjunctionElim₁
         (evalExp e2 s)
         (evalExp (op₂ (𝑐𝑜𝑛𝑠𝑡 ➊) ( == :𝔹) (𝑐𝑜𝑛𝑠𝑡 ➊ ) ) s ) wffp assert wffq
-}


  -- Σ (WFF (evalExp (proj₁ P) s))(T ∘ toTruthValue)

  {-
  Assert : 𝐴 → S → Set
  Assert P s = let returnVal = evalExp (proj₁ P) s in
       (Is-just returnVal) ×  
       ([ ( λ _ → ⊤ ) , ( λ _ → ⊥ ) ]  ∘ (proj₂ P) s )
  -}



  subExp : Exp → Id → Exp → Exp
  subExp e' id e = {!!}

  -- is Sub 𝐴 still and 𝐴? % and / case?
  -- sub : 𝑃 → Id → 𝑃 → 𝑃
  -- sub p i q = ?

  {-
  sub : Exp → Id → 𝐴 → 𝐴  
  sub e' id (op₂ x ϕ@(∙ :𝔹) y , s , _ ) =
     let    l = (subExp e' id x)
     in let r = (subExp e' id y)
     in (op₂ l ϕ r ) , s ,
     (:𝔹₂⇒Prop (∙ :𝔹₂) (evalExp l s) (evalExp r s))
  sub e' id (op₁ ϕ@(∙ :𝔹) e , s , _) =
      let e' = (subExp e' id e)
      in let exp' = (op₁ ϕ e')
      in exp' , s , :𝔹₁⇒Prop (∙ :𝔹₁) (evalExp e' s)
  sub e' id (exp@(op₁ (∙ :𝕍) e) , s , isprop)
      = exp , s , (λ wff → ⊥-elim (:𝕍₁⇒¬Prop (∙ :𝕍₁)
      (evalExp e s) (isprop wff)))
  sub e' id (exp@(op₂ x (∙ :𝕍) y) , s , isprop)
      = exp , s , (λ wff → ⊥-elim (:𝕍₂⇒¬Prop (∙ :𝕍₂)
      (evalExp x s) (evalExp y s) (isprop wff)))
  sub e' id (term (Const x) , snd) = {!!}
  sub e' id (term (Var x) , fst , snd) = {!!}
  sub e' id (term 𝒕 , snd) = {!!}
  sub e' id (term 𝒇 , snd) = {!!}
-}

  {-
  -- Substitute Expression for an Identifier in an Expression
  subExp : Exp → Id → Exp → Exp
  subExp e id (binOp l ∙ r) = binOp (subExp e id l) ∙ (subExp e id r)
  subExp e id (unOp ∙ e') = unOp ∙ (subExp e id e')
  subExp e id (term (Const c)) = (term (Const c))
  subExp e id (term 𝒕) = (term 𝒕)
  subExp e id (term 𝒇) = (term 𝒇)
  -- this is where the actual substitution happens:
  subExp e id (term (Var id')) with id ?id= id'
  ... | yes _ = e -- Substitute
  ... | no  _ = (term (Var id')) -- Don't sub.

    -- Substitute Expression for Identifier in a Predicate
  sub : Exp → Id → 𝐴 → 𝐴
  sub e' id p  with p
  ... | binOp l ϕ@(∙ :𝔹) r , snd = (binOp (subExp e' id l) ϕ (subExp e' id r)),
        (λ s → ᵇᵒ² (evalExp (subExp e' id l) s) (isᵇᵒ² ∙) (evalExp (subExp e' id r) s))
  ... | unOp x fst , snd = {!!} , (λ s → {!!})
  ... | term x , snd = {!!} , (λ s → {!!})
  ... | binOp l (ᶻᵒ ∙) r , 𝑝 =
      𝑐𝑜𝑛𝑠𝑡 ➊ , -- expression we put here is irrelevant,
                 -- agda just doesn't like leaving it empty with  _
      (λ s → {!!})
      --(λ s → ⊥-elim (ᶻᵒ²' (evalExp l s) (evalExp r s) (isᶻᵒ² ∙) (𝑝 s)))
  -}
  {-
  subTerm : Exp → Id → Terminal → Terminal ⊎ Exp
  subTerm e i (Const x) = inj₁ (Const x)
  subTerm e i (Var x) with i ?id= x
  ... | yes _ = inj₂ e
  ... | no  _ = inj₁ (Var x)
  subTerm e i 𝒕 = inj₁ 𝒕
  subTerm e i 𝒇 = inj₁ 𝒇
  -}

  {-
  sub e i (binOp l α r) = (binOp (sub e i l) α (sub e i r))
  sub e i (unOp ¬ᵇ e') = (unOp ¬ᵇ (sub e i e'))
  sub e i (term t) with (subTerm e i t)
  ... | inj₁ t'  = (term t')
  ... | inj₂ e'  = e'
  -}


  {-
  sub e i (𝔹: e') = 𝔹: (sub𝔹Exp e i e' )
  sub e i (ℤ: e') = ℤ: (subℤExp e i e')
  sub e i (term: t) = ( proj₂ (proj₂ ( subTerm e i t )))
  -}


  {-
  -- substitute Value for Identifier in Integer expression
  subℤExp : Val → Id → ℤExp → ℤExp
  subℤExp v i (⇉ᶻ l +ᶻ r) = (⇉ᶻ (subℤExp v i l) +ᶻ (subℤExp v i r))
  subℤExp v i (⇉ᶻ l -ᶻ r) = (⇉ᶻ (subℤExp v i l) -ᶻ (subℤExp v i r))
  subℤExp v i (⇉ᶻ l *ᶻ r) = (⇉ᶻ (subℤExp v i l) *ᶻ (subℤExp v i r)) 
  subℤExp v i (⇉ᶻ l /ᶻ r) = (⇉ᶻ (subℤExp v i l) /ᶻ (subℤExp v i r))  
  subℤExp v i (⇉ᶻ l %ᶻ r) = (⇉ᶻ (subℤExp v i l) %ᶻ (subℤExp v i r))
  subℤExp v i (Const x) = (Const x)
  subℤExp v i (Var x) with i ?id= x
  ... | yes _ = (Const v)
  ... | no  _ = (Var x)

  -- substitute Value for Identifier in Proposition
  sub : Val → Id → 𝐴 → 𝐴
  sub v i (ᶻ⇉ᵇ l ≤ r)  =  (ᶻ⇉ᵇ ( subℤExp v i l ) ≤  ( subℤExp v i r ))
  sub v i (ᶻ⇉ᵇ l < r)  =  (ᶻ⇉ᵇ ( subℤExp v i l ) <  ( subℤExp v i r ))
  sub v i (ᶻ⇉ᵇ l == r) =  (ᶻ⇉ᵇ ( subℤExp v i l ) == ( subℤExp v i r ))
  sub v i (ᶻ⇉ᵇ l ≥ r)  =  (ᶻ⇉ᵇ ( subℤExp v i l ) ≥  ( subℤExp v i r ))
  sub v i (ᶻ⇉ᵇ l > r)  =  (ᶻ⇉ᵇ ( subℤExp v i l ) >  ( subℤExp v i r ))
  sub v i (⇉ᵇ l && r) =  (⇉ᵇ (sub v i l) && (sub v i r))
  sub v i (⇉ᵇ l || r) =  (⇉ᵇ (sub v i l) || (sub v i r))
  sub v i (⇉ᵇ l ⇔ r) =  (⇉ᵇ (sub v i l) ⇔ (sub v i r))
  sub v i (⇾ᵇ ! e) = (⇾ᵇ ! (sub v i e))
  sub v i 𝒕 = 𝒕
  sub v i 𝒇 = 𝒇
  -}


  {-
  
  -}


{-
  sub𝔹Exp e i 𝒕         = 𝒕
  sub𝔹Exp e i 𝒇         = 𝒇
  sub𝔹Exp e i (Var x) with i ?id= x
  sub𝔹Exp e i (term𝔹 (Var x)) | yes _ = e
  sub𝔹Exp e i (term𝔹 (Var x)) | yes _ = ᶻ⇉ᵇ x == (termℤ 𝒕)
  ... | no _  = (term𝔹 (Var x))
-}


  {-
  subℤExp e i (⇉ᶻ l +ᶻ r) = (ℤ: (⇉ᶻ (sub e i l) +ᶻ (sub e i r)))
  subℤExp e i (⇉ᶻ l -ᶻ r) = (ℤ: (⇉ᶻ (sub e i l) -ᶻ (sub e i r)))
  subℤExp e i (⇉ᶻ l *ᶻ r) = (ℤ: (⇉ᶻ (sub e i l) *ᶻ (sub e i r)) )
  subℤExp e i (⇉ᶻ l /ᶻ r) = (ℤ: (⇉ᶻ (sub e i l) /ᶻ (sub e i r))  )
  subℤExp e i (⇉ᶻ l %ᶻ r) = (ℤ: (⇉ᶻ (sub e i l) %ᶻ (sub e i r)))
  subℤExp e i (𝔹Exp-ℤExp b) = (𝔹: (sub e i b))
  subℤExp e i (termℤ t ) with (subTerm e i t)
  ... | foo = ?

  -- substitute Expression for Identifier in Proposition
  sub𝔹Exp e i (ᶻ⇉ᵇ l α r) = (𝔹: (ᶻ⇉ᵇ ( subℤExp e i l) α ( subℤExp e i r) ))
  sub𝔹Exp e i (⇉ᵇ l α r ) = (𝔹: (⇉ᵇ ( sub𝔹Exp e i l) α ( sub𝔹Exp e i r) ))
  sub𝔹Exp e i (⇾ᵇ ¬ᵇ p) = (𝔹: (⇾ᵇ ¬ᵇ (sub𝔹Exp e i p)))
  sub𝔹Exp e i (term𝔹 t) with (subTerm e i t)
  ... | foo = ?

  -}



-- PQR₂ (to-witness ijQ₁) (PQR₁ s x (𝒻 , ijQ₁)) Σ[tQ₂]

-- PQR₂ s' (PQR₁ s x (𝒻 , ijQ₁)) (fst , {!snd!})

-- PQR₂ (to-witness ijQ1ₙ) (PQR₁ s x (Q1ₙ , ijQ1ₙ) ) ( Q2ₙ , ijQ2ₙ)



 --PQR₂ (to-witness (proj₂ (proj₁ (ǫ ϕ)))) (PQR₁ s x (proj₁ (ǫ  ϕ))) (proj₂ (ǫ ϕ)) -- (PQR₁  x (proj₁ (ǫ ϕ))) (proj₂ (ǫ ϕ))

{-
  Γ : ∀ i e s → (ϕ : Is-just (evalExp e s)) → Is-just (updateState i (to-witness ϕ) s)
  Γ i e s ij = ?
-}


  {-
  D2-Rule-of-Composition : ∀ {P} {Q₁} {R₁} {Q₂} {R} → ⟪ P ⟫ Q₁ ⟪ R₁ ⟫ → ⟪ R₁ ⟫ Q₂ ⟪ R ⟫ → ⟪ P ⟫ (𝑠𝑒𝑞꞉ (Q₁ ﹔ Q₂)) ⟪ R ⟫
  D2-Rule-of-Composition PQR₁ PQR₂  = λ s x ϕ → {!!}
    where
    ǫ : ∀ {Q₁} {Q₂} {s} → ⌊ᵗ ( 𝑠𝑒𝑞꞉ (Q₁ ﹔ Q₂)) ⸴  s ᵗ⌋ → Σ ⌊ᵗ Q₁ ⸴ s ᵗ⌋ ( λ μ →  ⌊ᵗ Q₂ ⸴ (to-witness (proj₂ μ)) ᵗ⌋ )
    ǫ {𝑎𝑠𝑠𝑖꞉ (i ꞉= e)} {𝑎𝑠𝑠𝑖꞉ (i' ꞉= e')} {s} ( (suc (suc n)) , snd) with evalExp e s | inspect (evalExp e) s
    ... | just x | Eq.[ eq ] with evalExp e' (updateState i x s) | inspect (evalExp e') (updateState i x s)
    ... | just x' | Eq.[ eq' ]  = let δ = subst (λ k → Is-just (Data.Maybe.map (λ v → updateState i v s) k)) (sym eq) (any-just tt) in
                                  ( 4 ,  δ    ) , 
                                  ( 3 ,  {!!} )
    ǫ {𝑎𝑠𝑠𝑖꞉ x} {𝑠𝑒𝑞꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑎𝑠𝑠𝑖꞉ x} {𝑐𝑡𝑟𝑙꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑎𝑠𝑠𝑖꞉ x} {𝑙𝑜𝑜𝑝꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑎𝑠𝑠𝑖꞉ x} {𝑠𝑘𝑖𝑝} (fst , snd) = {!!}
    ǫ {𝑠𝑒𝑞꞉ x} {𝑎𝑠𝑠𝑖꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑠𝑒𝑞꞉ x} {𝑠𝑒𝑞꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑠𝑒𝑞꞉ x} {𝑐𝑡𝑟𝑙꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑠𝑒𝑞꞉ x} {𝑙𝑜𝑜𝑝꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑠𝑒𝑞꞉ x} {𝑠𝑘𝑖𝑝} (fst , snd) = {!!}
    ǫ {𝑐𝑡𝑟𝑙꞉ x} {𝑎𝑠𝑠𝑖꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑐𝑡𝑟𝑙꞉ x} {𝑠𝑒𝑞꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑐𝑡𝑟𝑙꞉ x} {𝑐𝑡𝑟𝑙꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑐𝑡𝑟𝑙꞉ x} {𝑙𝑜𝑜𝑝꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑐𝑡𝑟𝑙꞉ x} {𝑠𝑘𝑖𝑝} (fst , snd) = {!!}
    ǫ {𝑙𝑜𝑜𝑝꞉ x} {𝑎𝑠𝑠𝑖꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑙𝑜𝑜𝑝꞉ x} {𝑠𝑒𝑞꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑙𝑜𝑜𝑝꞉ x} {𝑐𝑡𝑟𝑙꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑙𝑜𝑜𝑝꞉ x} {𝑙𝑜𝑜𝑝꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑙𝑜𝑜𝑝꞉ x} {𝑠𝑘𝑖𝑝} (fst , snd) = {!!}
    ǫ {𝑠𝑘𝑖𝑝} {𝑎𝑠𝑠𝑖꞉ x} (fst , snd) = {!!}
    ǫ {𝑠𝑘𝑖𝑝} {𝑠𝑒𝑞꞉ x} (fst , snd) = {!!}
    ǫ {𝑠𝑘𝑖𝑝} {𝑐𝑡𝑟𝑙꞉ x} (fst , snd) = {!!}
    ǫ {𝑠𝑘𝑖𝑝} {𝑙𝑜𝑜𝑝꞉ x} (fst , snd) = {!!}
    ǫ {𝑠𝑘𝑖𝑝} {𝑠𝑘𝑖𝑝} (fst , snd) = {!!}

-}

{-
  ssEvalwithFuel-evalAssi : (i : Id) (e : Exp) (s : S) → ssEvalwithFuel 1 (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) , just s) ≡ evalAssi s (i ꞉= e)
  ssEvalwithFuel-evalAssi i e s = refl

  ssEvalWithFuel-seq : (n : ℕ) (c₁ c₂ c₃ : 𝐶) (s : S)
                       → ssEvalwithFuel (suc n) (𝑠𝑒𝑞꞉ (𝑠𝑒𝑞꞉ (c₁ ﹔ c₂) ﹔ c₃) , just s)
                          ≡ ssEvalwithFuel (n) (𝑠𝑒𝑞꞉ (c₁ ﹔ (𝑠𝑒𝑞꞉ (c₂ ﹔ c₃))) ,  just s)
  ssEvalWithFuel-seq n c₁ c₂ c₃ s = refl


  Term-asm : {i : Id} {e : Exp} (x : i := e) (s s' : S)
             → evalAssi s x ≡ just s'
             → Σ ⌊ᵗ 𝑎𝑠𝑠𝑖꞉ x ⸴ s ᵗ⌋ λ c → to-witness (proj₂ c) ≡ s'
  Term-asm {i} {e} (i ꞉= e) s s' c rewrite ssEvalwithFuel-evalAssi i e s = (1 , proj₁ z) , proj₂ z
    where
      z₁ : maybe (λ x → just (updateState i x s)) nothing (evalExp e s) ≡ Data.Maybe.map (λ v → updateState i v s) (evalExp e s)
      z₁ = refl

      z : Σ (Is-just (Data.Maybe.map (λ v → updateState i v s) (evalExp e s))) λ c → to-witness c ≡ s'
      z rewrite z₁ | c =  Any.just tt , refl


  ssEvalwithFuel-nothing : (n : ℕ) (c : 𝐶) → ssEvalwithFuel n (c , nothing) ≡ nothing
  ssEvalwithFuel-nothing zero (𝑎𝑠𝑠𝑖꞉ x) = refl
  ssEvalwithFuel-nothing (suc n) (𝑎𝑠𝑠𝑖꞉ (i ꞉= e)) = refl
  ssEvalwithFuel-nothing zero (𝑠𝑒𝑞꞉ x) = refl
  ssEvalwithFuel-nothing (suc n) (𝑠𝑒𝑞꞉ (c₁ ﹔ c₂)) = refl
  ssEvalwithFuel-nothing zero (𝑐𝑡𝑟𝑙꞉ x) = refl
  ssEvalwithFuel-nothing (suc n) (𝑐𝑡𝑟𝑙꞉ (𝑖𝑓 b 𝑡ℎ𝑒𝑛 c₁ 𝑒𝑙𝑠𝑒 c₂)) = refl
  ssEvalwithFuel-nothing zero (𝑙𝑜𝑜𝑝꞉ x) = refl
  ssEvalwithFuel-nothing (suc n) (𝑙𝑜𝑜𝑝꞉ (𝑤ℎ𝑖𝑙𝑒 b 𝑑𝑜 c₁)) = refl
  ssEvalwithFuel-nothing zero 𝑠𝑘𝑖𝑝 = refl
  ssEvalwithFuel-nothing (suc n) 𝑠𝑘𝑖𝑝 = refl

  π : ∀ {ℓ} {A} {a} {s : Maybe {ℓ} A} → s ≡ just a → ( ϕ : Is-just s ) → to-witness ϕ ≡ a
  π {_} {_} {_} .{just _} refl (any-just _) = refl


  Term-comp2 : {c₁ c₂ : 𝐶} {s : S} {n₁ n₂ : ℕ}
               (t₁ : Is-just (ssEvalwithFuel n₁ (c₁ , just s)))
               (t₂ : Is-just (ssEvalwithFuel n₂ (c₂ , just (to-witness t₁))))
               → Is-just (ssEvalwithFuel (suc (n₁ Data.Nat.+ n₂)) (𝑠𝑒𝑞꞉ (c₁ ﹔ c₂) , just s))
  Term-comp2 {𝑎𝑠𝑠𝑖꞉ (i ꞉= e)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = z -- rewrite ssEvalwithFuel-evalAssi i e s 
    where
      z₁ : maybe (λ x → just (updateState i x s)) nothing (evalExp e s) ≡ Data.Maybe.map (λ v → updateState i v s) (evalExp e s)
      z₁ = refl

      z : Is-just (ssEvalwithFuel (suc (n₁ Data.Nat.+ n₂)) (c₂ , maybe (λ x → just (updateState i x s)) nothing (evalExp e s)))
      z  with evalExp e s
      ... | just x  with addFuel (suc n₁) (n₂ , t₂)
      ... | ( _ , ij ) , eq rewrite eq = subst ((λ s →  Any (λ _ → ⊤)
            (ssEvalwithFuel (suc (n₁ Data.Nat.+ n₂)) (c₂ , just s)))) z₃ ij
          where
          z₃ : to-witness t₁ ≡ (updateState i x s)
          z₃ = π refl t₁

  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) ﹔ 𝑎𝑠𝑠𝑖꞉ (i' ꞉= e'))} {c₂} {s} {suc (suc n₁)} {n₂} t₁ t₂ = z
    where
      
      z : Is-just (ssEvalwithFuel (suc (n₁ Data.Nat.+ n₂)) ( 𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i' ꞉= e') ﹔ c₂) , maybe (λ x → just (updateState i x s)) nothing (evalExp e s)))
      z  with evalExp e s
      ... | just x  with addFuel n₁ (n₂ , t₂)
      ... | ( _ , ij ) , eq with evalExp e' (updateState i x s)
      ... | just x₁ rewrite eq  = subst (λ s →  Any (λ _ → ⊤)
            (ssEvalwithFuel (n₁ Data.Nat.+ n₂) ( c₂ , just s ))) z₃ ij
          where
          z₃ : to-witness t₁ ≡ updateState i' x₁ (updateState i x s)
          z₃ = π refl t₁


  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) ﹔ 𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i' ꞉= e') ﹔ 𝑎𝑠𝑠𝑖꞉ (i'' ꞉= e'')))} {c₃} {s} {suc (suc n₁)} {n₂} t₁ t₂ with evalExp e s | n₁
  ... | just v | suc n₁' with addFuel n₁' (n₂ , t₂)
  ... | (.(n₁' Data.Nat.+ n₂) , snd₁) , refl with evalExp e' (updateState i v s)
  ... | just v' with evalExp e'' (updateState i' v' (updateState i v s))
  ... | just v'' with n₂
  ... | zero rewrite 0⇒𝑠𝑘𝑖𝑝 {to-witness t₁} {c₃} t₂ = {!!}
  ... | suc foo = {!!}


    where
    z₃ : to-witness t₁ ≡ updateState i'' v'' (updateState i' v' (updateState i v s))
    z₃ = π refl t₁

-- let foo = subst ((λ s → Is-just (ssEvalwithFuel (n₁' Data.Nat.+ n₂) (c₃ , just s)))) z₃ snd₁ in {!!}

  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) ﹔ 𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i' ꞉= e') ﹔ 𝑠𝑒𝑞꞉ x))} {c₃} {s} {suc (suc n₁)} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) ﹔ 𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i' ꞉= e') ﹔ 𝑐𝑡𝑟𝑙꞉ x))} {c₃} {s} {suc (suc n₁)} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) ﹔ 𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i' ꞉= e') ﹔ 𝑙𝑜𝑜𝑝꞉ x))} {c₃} {s} {suc (suc n₁)} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) ﹔ 𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i' ꞉= e') ﹔ 𝑠𝑘𝑖𝑝))} {c₃} {s} {suc (suc n₁)} {n₂} t₁ t₂ = {!!}

  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) ﹔ 𝑠𝑒𝑞꞉ (𝑠𝑒𝑞꞉ x ﹔ c₂))} {c₃} {s} {suc (suc n₁)} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) ﹔ 𝑠𝑒𝑞꞉ (𝑐𝑡𝑟𝑙꞉ x ﹔ c₂))} {c₃} {s} {suc (suc n₁)} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) ﹔ 𝑠𝑒𝑞꞉ (𝑙𝑜𝑜𝑝꞉ x ﹔ c₂))} {c₃} {s} {suc (suc n₁)} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) ﹔ 𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ c₂))} {c₃} {s} {suc (suc n₁)} {n₂} t₁ t₂ = {!!}



  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ x ﹔ 𝑐𝑡𝑟𝑙꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ x ﹔ 𝑙𝑜𝑜𝑝꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ x ﹔ 𝑠𝑘𝑖𝑝)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑠𝑒𝑞꞉ x ﹔ 𝑎𝑠𝑠𝑖꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑠𝑒𝑞꞉ x ﹔ 𝑠𝑒𝑞꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑠𝑒𝑞꞉ x ﹔ 𝑐𝑡𝑟𝑙꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑠𝑒𝑞꞉ x ﹔ 𝑙𝑜𝑜𝑝꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑠𝑒𝑞꞉ x ﹔ 𝑠𝑘𝑖𝑝)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑐𝑡𝑟𝑙꞉ x ﹔ 𝑎𝑠𝑠𝑖꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑐𝑡𝑟𝑙꞉ x ﹔ 𝑠𝑒𝑞꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑐𝑡𝑟𝑙꞉ x ﹔ 𝑐𝑡𝑟𝑙꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑐𝑡𝑟𝑙꞉ x ﹔ 𝑙𝑜𝑜𝑝꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑐𝑡𝑟𝑙꞉ x ﹔ 𝑠𝑘𝑖𝑝)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑙𝑜𝑜𝑝꞉ x ﹔ 𝑎𝑠𝑠𝑖꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑙𝑜𝑜𝑝꞉ x ﹔ 𝑠𝑒𝑞꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑙𝑜𝑜𝑝꞉ x ﹔ 𝑐𝑡𝑟𝑙꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑙𝑜𝑜𝑝꞉ x ﹔ 𝑙𝑜𝑜𝑝꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑙𝑜𝑜𝑝꞉ x ﹔ 𝑠𝑘𝑖𝑝)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ 𝑎𝑠𝑠𝑖꞉ x)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ 𝑠𝑒𝑞꞉ x)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ 𝑐𝑡𝑟𝑙꞉ x)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ 𝑙𝑜𝑜𝑝꞉ x)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ 𝑠𝑘𝑖𝑝)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑐𝑡𝑟𝑙꞉ x} {c₂} {s} {n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑙𝑜𝑜𝑝꞉ x} {c₂} {s} {n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑘𝑖𝑝} {c₂} {s} {n₁} {n₂} t₁ t₂ = {!!}

  Term-comp : {c₁ c₂ : 𝐶} {s : S} → (t₁ : ⌊ᵗ c₁ ⸴ s ᵗ⌋) (t₂ : ⌊ᵗ c₂ ⸴ to-witness (proj₂ t₁) ᵗ⌋)
              → ⌊ᵗ 𝑠𝑒𝑞꞉ (c₁ ﹔ c₂) ⸴ s ᵗ⌋
  Term-comp {c₁} {c₂} {s} (n₁ , t₁) (n₂ , t₂) = suc (n₁ Data.Nat.+ n₂) , Term-comp2 {c₁} {c₂} {s} {n₁} {n₂} t₁ t₂


  ǫ : ∀ {Q₁} {Q₂} {s} → ⌊ᵗ ( 𝑠𝑒𝑞꞉ (Q₁ ﹔ Q₂)) ⸴  s ᵗ⌋ → Σ ⌊ᵗ Q₁ ⸴ s ᵗ⌋ ( λ μ →  ⌊ᵗ Q₂ ⸴ (to-witness (proj₂ μ)) ᵗ⌋ )
  ǫ {𝑎𝑠𝑠𝑖꞉ x} {Q₂} {s} (suc n , snd) with ⊎-maybe (evalAssi s x)
  ... | inj₁ q rewrite q | ssEvalwithFuel-nothing n Q₂ = ⊥-elim (Is-just-nothing snd)
  ... | inj₂ (a , q) rewrite q = proj₁ (Term-asm x s a q) , n , z
      where
        z : Is-just (ssEvalwithFuel n (Q₂ , just (to-witness (proj₂ (proj₁ (Term-asm x s a q))))))
        z rewrite (proj₂ (Term-asm x s a q)) = snd

  ǫ {𝑠𝑒𝑞꞉ (c₁ ﹔ c₂)} {Q₂} {s} (suc n , snd) rewrite ssEvalWithFuel-seq n c₁ c₂ Q₂ s = Term-comp z₁ z₄ , {!!}
      where
        z : Σ ⌊ᵗ c₁ ⸴ s ᵗ⌋ ( λ μ →  ⌊ᵗ 𝑠𝑒𝑞꞉ (c₂ ﹔ Q₂) ⸴ (to-witness (proj₂ μ)) ᵗ⌋ )
        z = ǫ (n , snd)

        z₁ : ⌊ᵗ c₁ ⸴ s ᵗ⌋
        z₁ = proj₁ z

        z₂ : ⌊ᵗ 𝑠𝑒𝑞꞉ (c₂ ﹔ Q₂) ⸴ (to-witness (proj₂ z₁)) ᵗ⌋
        z₂ = proj₂ z

        z₃ : Σ ⌊ᵗ c₂ ⸴ to-witness (proj₂ z₁) ᵗ⌋ ( λ μ →  ⌊ᵗ Q₂ ⸴ to-witness (proj₂ μ) ᵗ⌋ )
        z₃ = ǫ z₂

        z₄ : ⌊ᵗ c₂ ⸴ to-witness (proj₂ z₁) ᵗ⌋
        z₄ = proj₁ z₃

        z₅ : ⌊ᵗ Q₂ ⸴ to-witness (proj₂ z₄) ᵗ⌋
        z₅ = proj₂ z₃


  ǫ {𝑐𝑡𝑟𝑙꞉ x} {Q₂} (suc n , snd) = {!!} , {!!}
  ǫ {𝑙𝑜𝑜𝑝꞉ x} {Q₂} (suc n , snd) = {!!} , {!!}
  ǫ {𝑠𝑘𝑖𝑝} {Q₂} (suc n , snd) = {!!} , {!!}

  D2-Rule-of-Composition : ∀ {P} {Q₁} {R₁} {Q₂} {R} → ⟪ P ⟫ Q₁ ⟪ R₁ ⟫ → ⟪ R₁ ⟫ Q₂ ⟪ R ⟫ → ⟪ P ⟫ (𝑠𝑒𝑞꞉ (Q₁ ﹔ Q₂)) ⟪ R ⟫
  D2-Rule-of-Composition {P} {Q₁} {R₁} {Q₂} {R} PQR₁ PQR₂ s x ϕ = {!!}
    -- PQR₂ (to-witness j₁) {!!} {!!} -- PQR₂ (to-witness (proj₂ (proj₁ (ǫ ϕ)))) (PQR₁ s x (proj₁ (ǫ ϕ))) {!!}
    --PQR₂ (to-witness (proj₂ (proj₁ (ǫ ϕ)))) (PQR₁ s x (proj₁ (ǫ ϕ))) (proj₂ (ǫ ϕ)) -- (PQR₁  x (proj₁ (ǫ ϕ))) (proj₂ (ǫ ϕ))
    where
      z₁ : ⌊ᵗ Q₁ ⸴ s ᵗ⌋
      z₁ = proj₁ (ǫ ϕ)

      n₁ : ℕ
      n₁ = proj₁ z₁

      j₁ : Is-just (ssEvalwithFuel n₁ ( Q₁ , just s ))
      j₁ = proj₂ z₁

      z₂ : ⌊ᵗ Q₂ ⸴ to-witness (proj₂ (proj₁ (ǫ ϕ))) ᵗ⌋
      z₂ = proj₂ (ǫ ϕ)



  -}

  {-
  axiomOfAssignment : ∀ {i} {v} {e} (p  :  𝑃) → ( a :  i := e )
                        → ( ( s : S ) →  evalExp e s ≡ (just v))
                        → ⟪ (sub v i p) ⟫ ( 𝑎𝑠𝑠𝑖꞉ a ) ⟪ p ⟫
  axiomOfAssignment {i} {v} {e} p (.i ꞉= .e) pr s pre s' eval =  {!!}
  
 
  axiomOfAssignment : ∀ {i} {e}  (p  :  𝑃) → ( a :  i := e )
                        → ⟪ (sub e i  p) ⟫ ( 𝑎𝑠𝑠𝑖꞉ a ) ⟪ p ⟫
  axiomOfAssignment {i} {e} p (.i ꞉= .e) s pre s' eval with p | (sub e i p)
  ... | ᶻ⇉ᵇ x x₁ x₂     | ᶻ⇉ᵇ x₃ x₄ x₅ = {!!}
  ... | ᶻ⇉ᵇ x x₁ x₂     | ⇉ᵇ bar x₃ bar₁ = {!!}
  ... | ᶻ⇉ᵇ x x₁ x₂     | ⇾ᵇ x₃ bar = {!!}
  ... | ᶻ⇉ᵇ x x₁ x₂     | term𝔹 x₃ = {!!}
  ... | ⇉ᵇ foo x foo₁  | ᶻ⇉ᵇ x₁ x₂ x₃ = {!!}
  ... | ⇉ᵇ foo x foo₁  | ⇉ᵇ bar x₁ bar₁ = {!!}
  ... | ⇉ᵇ foo x foo₁  | ⇾ᵇ x₁ bar = {!!}
  ... | ⇉ᵇ foo x foo₁  | term𝔹 x₁ = {!!}
  ... | ⇾ᵇ x foo       | ᶻ⇉ᵇ x₁ x₂ x₃ = {!!}
  ... | ⇾ᵇ x foo       | ⇉ᵇ bar x₁ bar₁ = {!!}
  ... | ⇾ᵇ x foo       | ⇾ᵇ x₁ bar = {!!}
  ... | ⇾ᵇ x foo       | term𝔹 x₁ = {!!}
  ... | term𝔹 x        | ᶻ⇉ᵇ x₁ x₂ x₃ = {!!}
  ... | term𝔹 x        | ⇉ᵇ bar x₁ bar₁ = {!!}
  ... | term𝔹 x        | ⇾ᵇ x₁ bar = {!!}
  ... | term𝔹 x        | term𝔹 x₁ = {!!}
-}


{-
  -- Axioms
  axiom-of-assignment : ∀ {i} {v} {p} {s s'} {e}
                        → ((sub v i p) ← s)
                        -- Proof that assignment terminates
                        → (i := e |evalExp= v USING s GIVES s') 
                        → ( p ← s' ) 
  axiom-of-assignment {i} {v} {p} {s} {.(updateState i v s)}
                          (holdsBecause eval→𝑻)
                          ((.i :=' _ w/ .s andPExp) x)
                          rewrite sym (s⇔u i v s p)
                          = holdsBecause eval→𝑻



   -- R⊃S → P{Q}R → P{Q}S
  
   -- {Q} S {R}

  


  -- Not sure about these, probs need to have Hoare triple (i.e.  ⊢P{Q}R ) for these to make sense 

  rule-of-consequence1 : ∀ {i} {v} {p q r} {s s'} {e}

                         → ((Assert q ∵ s') → (Assert r ∵ s' ))          --       R ⊃ S
                         
                         → (Assert p ∵ s')                                --        P
                         
                         -- Proof that program terminates
                         -- TODO: All program kinds need to go here, not just
                         -- assignment (i.e. while, block, ifelse etc.)
                         → (i := e |evalExp= v USING s GIVES s')                  -- {Q}

                         → (Assert q ∵ s')                                    -- R

                         → (Assert r ∵ s')
  rule-of-consequence1 {i} {v} {p} {q} {r} {s} {s'} q⊃r a prog b = q⊃r b



  rule-of-consequence2 : ∀ {i} {v} {p q r} {s s'} {e}

                         → ((Assert p ∵ s) → (Assert r ∵ s' ))
                         
                         → (Assert p ∵ s)
                         
                         -- Proof that program terminates
                         -- TODO: All program kinds need to go here, not just
                         -- assignment (i.e. while, block, ifelse etc.)
                         → (i := e |evalExp= v USING s GIVES s')

                         → (Assert q ∵ s')

                         → (Assert r ∵ s)
  rule-of-consequence2 {i} {v} {p} {q} {r} {s} {s'} q⊃r a prog b = {!!}

-}


{-

  record Foo : Set₁ where
    field
      A      : Set
      toBool : A → Data.Bool.Bool
      
  open Foo
  
  data ↪S' : Set where
    𝔴𝔥𝔦𝔩𝔢_𝒹ℴ_ : Ex → Block → ↪S'
    _:=_ : Id → Ex → ↪S'
  open ↪S' public
  
  data Block where
    _;  : ↪S' → Block
    _;_ : ↪S' → Block → Block
  open Block public

  Block = ℭ

  ssEvalwF : ℕ → ℭ → 𝔖 → Maybe 𝔖
  ssEvalwF n (x :: xs) s = ?

  Term : ℕ → List Ex → 𝔖 →Set
  Term n c s = Is-just (ssEvalwF n c s)

  lem : ∀ {Foo} (a : A Foo) → Is-just (Bar {Foo} a) → Is-just (Bar {Foo} a)
  lem {Foo} a ij with (toBool Foo) a
  ... | b = {!!}
-}























