
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
  


  


