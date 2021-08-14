
-- Lib Imports
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import Relation.Binary using (Decidable)
open import Relation.Nullary.Decidable using (False )
open import Data.Product as Pr using ( Σ ; Σ-syntax ; _,_  ; proj₂) 
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ ; fromInj₁ ; fromInj₂ )
open import Data.Maybe using ( Maybe ; just ; nothing ; Is-just )
import Data.Maybe.Relation.Unary.Any 
open Data.Maybe.Relation.Unary.Any.Any renaming ( just to any-just )
open import Data.Empty using ( ⊥ ; ⊥-elim )
open import Function using ( _∘_ )
-- Integers
open import Data.Integer as Int
open ℤ
open import Data.Integer.DivMod using (_div_ ; _mod_ )
open import Data.Integer.Properties using
     (  *-distribˡ-+ ; +-identityˡ ; +-identityʳ ; m≡n⇒m-n≡0
     ;  *-zeroʳ      ; *-identityʳ )
     renaming
     ( +-comm  to ℤ+-comm  ; *-comm  to ℤ*-comm  ;
       +-assoc to ℤ+-assoc ; *-assoc to ℤ*-assoc )
-- Natural Numbers
open import Data.Nat as Nat using ( ℕ )
     renaming ( suc to s ; _≟_ to _≟ⁿ_  ; _≤_ to _≤ⁿ_ )
-- Booleans
open import Data.Bool using (Bool ; true ; false ; T ; _∨_ ; _∧_ ; not )  
open import Data.Bool.Properties using ( ∧-comm )
open import Agda.Builtin.Unit


-- Local Imports
open import Misc
open import Data-Interface

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Representations.Data-Infinite-Arithmetic where

  -- ════════════════════════════════════════════════════════════════════════════
  -- Representations.Data-Infinite-Arithmetic:
  --
  -- Implementation of the data interface with an infinite arithmetic strategy.
  -- I.e. Integers aren't bounded and are represented using Agda's standard
  -- library Integer. Data Values - the kind that are stored in variables - are
  -- represented as the disjoint union of the sets of Integers and Booleans.

  pattern ns n = (negsuc n)
  pattern 𝑝 n  = (pos n)
  pattern isjust = any-just tt
  WFF = Is-just

  -- ════════════════════════════════════════════════════════════════════════════
  module Value-Implementation-Infinite where


    -- Indentifiers are represented as natural numbers
    Id = ℕ
    
    -- Every Val is either ℤ or 𝔹
    Val = ℤ ⊎ Bool

    pattern 𝔹⦆∶ n = just (inj₂ n)
    pattern ℤ⦆∶ n = just (inj₁ n)

    -- Casting between Ints and Truth values. As per the C standard (and most
    -- languages with implicit casting between ℤ's and 𝔹's) zero is cast to
    -- false and any non-zero value is cast to true.
    ⦅𝔹⦆ : ℤ → Bool
    ⦅𝔹⦆ (𝑝 0)    = false
    ⦅𝔹⦆ +[1+ _ ] = true
    ⦅𝔹⦆ (ns  _ ) = true

    ⦅ℤ⦆ : Bool → ℤ
    ⦅ℤ⦆ false = 𝑝 0
    ⦅ℤ⦆ true  = 𝑝 1

    trans⦅𝔹⦆⦅ℤ⦆ : ∀ b → T (⦅𝔹⦆ (⦅ℤ⦆ b)) ≡ T b
    trans⦅𝔹⦆⦅ℤ⦆ false = refl
    trans⦅𝔹⦆⦅ℤ⦆ true  = refl

    asBool : Maybe Bool → Maybe Val
    asBool = inj₂ <$>_
    asInt : Maybe ℤ → Maybe Val
    asInt  = inj₁ <$>_

    𝒙 : Id
    𝒙 = 0
    𝒚 : Id
    𝒚 = 1
    𝒛 : Id
    𝒛 = 2

    𝒙≢𝒛 : 𝒙 ≡ 𝒛 → ⊥
    𝒙≢𝒛 ()
    𝒚≢𝒛 : 𝒚 ≡ 𝒛 → ⊥
    𝒚≢𝒛 ()

    𝑻 : Val
    𝑻 = inj₂ true

    𝑭 : Val
    𝑭 = inj₂ false

    toTruthValue : {v : Maybe Val} → WFF v → Bool
    toTruthValue {just (inj₂ b)} _ = b
    toTruthValue {just (inj₁ z)} _ = ⦅𝔹⦆ z

    toIntValue : Val → ℤ
    toIntValue (inj₁ z) = z
    toIntValue (inj₂ b) = ⦅ℤ⦆ b


    𝑻is𝑻 : toTruthValue {just 𝑻} (any tt) ≡ true
    𝑻is𝑻 = refl

    𝑭is𝑭 : toTruthValue {just 𝑭} (any tt) ≡ false
    𝑭is𝑭 = refl

    ⓪ : Val
    ⓪ = inj₁ (𝑝 0)
    
    ① : Val
    ① = inj₁ (𝑝 1)

    ② : Val
    ② = inj₁ (𝑝 2)

    _?id=_ : Decidable {A = Id} _≡_ 
    _?id=_ = Nat._≟_

  -- ════════════════════════════════════════════════════════════════════════════
  module Operation-Implementation-Infinite where

    open Value-Implementation-Infinite
    
    𝔡 : Value-Implementation
    𝔡 = record { Value-Implementation-Infinite }

    open Value-Implementation 𝔡 using (⊢ ; ⊬  ; Int∶ )

    _̇ : ∀ {ℓ} {A : Set ℓ} → (x : A) → Maybe A
    _̇ = just
    infix 50 _̇
    
    ----------------------------------------------------------
    -- Basic lemmas / operations

    private is-neg : ℤ → Bool
    is-neg (negsuc _) = true
    is-neg (pos    _) = false

    private is-pos : ℤ → Bool
    is-pos (pos    _) = true
    is-pos (negsuc _) = false

    private suc⊖ : ∀ m n → s m ⊖ s n ≡ m ⊖ n 
    suc⊖ 0 0 = refl
    suc⊖ 0 (s n) = refl
    suc⊖ (s m) 0 = refl
    suc⊖ (s m) (s n)
      with (s m) Nat.<ᵇ (s n)
    ... | false = refl
    ... | true  = refl

    private n⊖n=0 : ∀ m → m ⊖ m ≡ +0
    n⊖n=0 0 = refl
    n⊖n=0 (s m) rewrite suc⊖ m m = n⊖n=0 m

    private z+-z=0 : ∀ m → m + - m ≡ +0
    z+-z=0 (𝑝 0) = refl
    z+-z=0 +[1+ n ]   rewrite suc⊖ n n = n⊖n=0 n 
    z+-z=0 (negsuc n) rewrite suc⊖ n n = n⊖n=0 n 

    private eq : ℤ → ℤ → Bool 
    eq (𝑝  n) (𝑝  m) = n Nat.≡ᵇ m
    eq (ns n) (ns m) = n Nat.≡ᵇ m
    eq (𝑝 _)  (ns _) = false
    eq (ns _) (𝑝 _)  = false
    -- eq a b = is-zero (a - b)
    -- Used for divide by zero error
    private is¬0 : ( z : ℤ ) → Maybe (False (∣ z ∣ ≟ⁿ 0))
    is¬0 (𝑝 0)      = nothing
    is¬0 (+[1+ n ]) = just tt
    is¬0 (ns n)     = just tt

    valAsℤ : Maybe Val → Maybe ℤ
    valAsℤ  = fromInj₁ ⦅ℤ⦆ <$>_ 

    valAs𝔹 : Maybe Val → Maybe Bool
    valAs𝔹 = fromInj₂ ⦅𝔹⦆ <$>_

    apply⊎𝔹²→𝔹 : ∀ (f : Bool → Bool → Bool)
                 → Maybe Val → Maybe Val → Maybe Val
    apply⊎𝔹²→𝔹 f a b = asBool (f <$>(valAs𝔹 a)<*>(valAs𝔹 b))

    apply⊎ℤ²→ℤ : ∀ (f : ℤ → ℤ → ℤ)
                 → Maybe Val → Maybe Val → Maybe Val
    apply⊎ℤ²→ℤ f a b = asInt  (f <$>(valAsℤ a)<*>(valAsℤ b))

    apply⊎ℤ²→𝔹 : ∀ (f : ℤ → ℤ → Bool)
                 → Maybe Val → Maybe Val → Maybe Val
    apply⊎ℤ²→𝔹 f a b = asBool (f <$>(valAsℤ a)<*>(valAsℤ b))

    ----------------------------------------------------------
    -- Program Operators used in the expression language
    --
    -- Remember non-zero values are taken as 𝑇 as per C standard

    ----------------------------------------
    -- Operators of domain 𝔹 and codomain 𝔹
    _||ᵥ_ : Maybe Val → Maybe Val → Maybe Val 
    _||ᵥ_ = apply⊎𝔹²→𝔹 _∨_

    _&&ᵥ_ : Maybe Val → Maybe Val → Maybe Val 
    _&&ᵥ_ = apply⊎𝔹²→𝔹 _∧_

    _==ᵥ_ : Maybe Val → Maybe Val → Maybe Val
    _==ᵥ_  = apply⊎ℤ²→𝔹 eq 

    ----------------------------------------
    -- Operators of domain ℤ and codomain 𝔹
    _≤ᵥ_ : Maybe Val → Maybe Val → Maybe Val 
    _≤ᵥ_ = apply⊎ℤ²→𝔹 leq 
      where
      leq : ℤ → ℤ → Bool
      leq a b = is-neg ((a - b) - (𝑝 1))

    _<ᵥ_ : Maybe Val → Maybe Val → Maybe Val 
    _<ᵥ_ = apply⊎ℤ²→𝔹 less
      where
      less : ℤ → ℤ → Bool
      less a b = is-neg (a - b)

    _≥ᵥ_ : Maybe Val → Maybe Val → Maybe Val 
    _≥ᵥ_ = apply⊎ℤ²→𝔹 geq
      where
      geq : ℤ → ℤ → Bool
      geq a b = is-pos (a - b)

    _>ᵥ_ : Maybe Val → Maybe Val → Maybe Val 
    _>ᵥ_ = apply⊎ℤ²→𝔹 greater
      where
      greater : ℤ → ℤ → Bool
      greater a b = is-pos ((a - b) - (𝑝 1))

    ----------------------------------------
    -- Operators of domain ℤ and codomain ℤ
    _+ᵥ_ : Maybe Val  →  Maybe Val  →  Maybe Val
    _+ᵥ_ = apply⊎ℤ²→ℤ _+_

    _-ᵥ_ : Maybe Val → Maybe Val → Maybe Val
    _-ᵥ_ = apply⊎ℤ²→ℤ _-_

    _*ᵥ_ : Maybe Val → Maybe Val → Maybe Val
    _*ᵥ_ = apply⊎ℤ²→ℤ _*_

    _/ᵥ_ : Maybe Val → Maybe Val → Maybe Val
    _ /ᵥ nothing = nothing
    nothing /ᵥ just _ = nothing
    a@(just _) /ᵥ just (inj₂ b) = a /ᵥ (just (inj₁ (⦅ℤ⦆ b)))
    a@(just _) /ᵥ (just (inj₁ z)) =
      asInt ((λ a ¬0 → (a div z) {¬0})
            <$> (valAsℤ a) <*> (is¬0 z))

    _%ᵥ_ : Maybe Val → Maybe Val → Maybe Val
    _ %ᵥ nothing = nothing
    nothing %ᵥ just _ = nothing
    a@(just _) %ᵥ just (inj₂ b) = a %ᵥ (just (inj₁ (⦅ℤ⦆ b)))
    a@(just _) %ᵥ (just (inj₁ z)) =
      asInt ((λ a ¬0 → 𝑝 ((a mod z) {¬0}))
            <$> (valAsℤ a) <*> (is¬0 z))

    ----------------------------------------
    -- Unary Operators

    -- Boolean negation
    ¬ᵥ : Maybe Val → Maybe Val
    ¬ᵥ = asBool ∘ (not <$>_) ∘ valAs𝔹

    -- Increment
    ++ᵥ : Maybe Val → Maybe Val
    ++ᵥ = asInt ∘ (Int.suc <$>_) ∘ valAsℤ 

    -- Decrement
    ─-ᵥ : Maybe Val → Maybe Val
    ─-ᵥ = asInt ∘ (Int.pred <$>_) ∘ valAsℤ

    -- Integer Negation
    ──ᵥ : Maybe Val → Maybe Val
    ──ᵥ = asInt ∘ (Int.-_ <$>_) ∘ valAsℤ
    
    ----------------------------------------
    -- Expression Lemmas


    A1 : ∀ x y → x +ᵥ y ≡ y +ᵥ x   -- addition is commutative
    A1 nothing nothing = refl
    A1 nothing (just _) = refl
    A1 (just _) nothing = refl
    A1 (ℤ⦆∶ x) (ℤ⦆∶ y) rewrite ℤ+-comm x y = refl
    A1 (ℤ⦆∶ x) (𝔹⦆∶ y) rewrite ℤ+-comm x (⦅ℤ⦆ y) = refl
    A1 (𝔹⦆∶ x) (ℤ⦆∶ y)rewrite ℤ+-comm (⦅ℤ⦆ x) y = refl
    A1 (𝔹⦆∶ x) (𝔹⦆∶ y) rewrite ℤ+-comm (⦅ℤ⦆ x) (⦅ℤ⦆ y) = refl

    A2 : ∀ x y → x *ᵥ y ≡ y *ᵥ x  -- multiplication is commutative
    A2 nothing nothing = refl
    A2 nothing (just _) = refl
    A2 (just _) nothing = refl
    A2 (ℤ⦆∶ x) (ℤ⦆∶ y) rewrite ℤ*-comm x y = refl
    A2 (ℤ⦆∶ x) (𝔹⦆∶ y) rewrite ℤ*-comm x (⦅ℤ⦆ y) = refl
    A2 (𝔹⦆∶ x) (ℤ⦆∶ y) rewrite ℤ*-comm (⦅ℤ⦆ x) y = refl
    A2 (𝔹⦆∶ x) (𝔹⦆∶ y) rewrite ℤ*-comm (⦅ℤ⦆ x) (⦅ℤ⦆ y) = refl

    A3 : ∀ x y z → x +ᵥ (y +ᵥ z) ≡ (x +ᵥ y) +ᵥ z  -- associativity of +
    A3 nothing nothing nothing = refl
    A3 nothing nothing (just _) = refl
    A3 nothing (just _) nothing = refl
    A3 nothing (just _) (just _) = refl
    A3 (just _) nothing nothing = refl
    A3 (just _) nothing (just _) = refl
    A3 (just _) (just _) nothing = refl
    A3 (ℤ⦆∶ x) (ℤ⦆∶ y) (ℤ⦆∶ z) rewrite ℤ+-assoc x y z = refl
    A3 (ℤ⦆∶ x) (ℤ⦆∶ y) (𝔹⦆∶ z) rewrite ℤ+-assoc x y (⦅ℤ⦆ z) = refl
    A3 (ℤ⦆∶ x) (𝔹⦆∶ y) (ℤ⦆∶ z) rewrite ℤ+-assoc x (⦅ℤ⦆ y) z = refl
    A3 (ℤ⦆∶ x) (𝔹⦆∶ y) (𝔹⦆∶ z) rewrite ℤ+-assoc x (⦅ℤ⦆ y) (⦅ℤ⦆ z) = refl
    A3 (𝔹⦆∶ x) (ℤ⦆∶ y) (ℤ⦆∶ z) rewrite ℤ+-assoc (⦅ℤ⦆ x) y z = refl
    A3 (𝔹⦆∶ x) (ℤ⦆∶ y) (𝔹⦆∶ z) rewrite ℤ+-assoc (⦅ℤ⦆ x) y (⦅ℤ⦆ z) = refl
    A3 (𝔹⦆∶ x) (𝔹⦆∶ y) (ℤ⦆∶ z) rewrite ℤ+-assoc (⦅ℤ⦆ x) (⦅ℤ⦆ y) z = refl
    A3 (𝔹⦆∶ x) (𝔹⦆∶ y) (𝔹⦆∶ z) rewrite ℤ+-assoc (⦅ℤ⦆ x) (⦅ℤ⦆ y) (⦅ℤ⦆ z) = refl


    A4 : ∀ x y z → x *ᵥ (y *ᵥ z) ≡ (x *ᵥ y) *ᵥ z  -- associativity of *
    A4 nothing nothing nothing = refl
    A4 nothing nothing (just _) = refl
    A4 nothing (just _) nothing = refl
    A4 nothing (just _) (just _) = refl
    A4 (just _) nothing nothing = refl
    A4 (just _) nothing (just _) = refl
    A4 (just _) (just _) nothing = refl
    A4 (ℤ⦆∶ x) (ℤ⦆∶ y) (ℤ⦆∶ z) rewrite ℤ*-assoc x y z = refl
    A4 (ℤ⦆∶ x) (ℤ⦆∶ y) (𝔹⦆∶ z) rewrite ℤ*-assoc x y (⦅ℤ⦆ z) = refl
    A4 (ℤ⦆∶ x) (𝔹⦆∶ y) (ℤ⦆∶ z) rewrite ℤ*-assoc x (⦅ℤ⦆ y) z = refl
    A4 (ℤ⦆∶ x) (𝔹⦆∶ y) (𝔹⦆∶ z) rewrite ℤ*-assoc x (⦅ℤ⦆ y) (⦅ℤ⦆ z) = refl
    A4 (𝔹⦆∶ x) (ℤ⦆∶ y) (ℤ⦆∶ z) rewrite ℤ*-assoc (⦅ℤ⦆ x) y z = refl
    A4 (𝔹⦆∶ x) (ℤ⦆∶ y) (𝔹⦆∶ z) rewrite ℤ*-assoc (⦅ℤ⦆ x) y (⦅ℤ⦆ z) = refl
    A4 (𝔹⦆∶ x) (𝔹⦆∶ y) (ℤ⦆∶ z) rewrite ℤ*-assoc (⦅ℤ⦆ x) (⦅ℤ⦆ y) z = refl
    A4 (𝔹⦆∶ x) (𝔹⦆∶ y) (𝔹⦆∶ z) rewrite ℤ*-assoc (⦅ℤ⦆ x) (⦅ℤ⦆ y) (⦅ℤ⦆ z) = refl


    A5 : ∀ x y z → x *ᵥ (y +ᵥ z) ≡ (x *ᵥ y) +ᵥ (x *ᵥ z)  -- * distributes
    A5 nothing nothing nothing = refl
    A5 nothing nothing (just -) = refl
    A5 nothing (just _) nothing = refl
    A5 nothing (just _) (just _) = refl
    A5 (just _) nothing nothing = refl
    A5 (just _) nothing (just _) = refl
    A5 (just _) (just _) nothing = refl
    A5 (ℤ⦆∶ x) (ℤ⦆∶ y) (ℤ⦆∶ z) rewrite *-distribˡ-+ x y z = refl
    A5 (ℤ⦆∶ x) (ℤ⦆∶ y) (𝔹⦆∶ z) rewrite *-distribˡ-+ x y (⦅ℤ⦆ z) = refl
    A5 (ℤ⦆∶ x) (𝔹⦆∶ y) (ℤ⦆∶ z) rewrite *-distribˡ-+ x (⦅ℤ⦆ y) z = refl
    A5 (ℤ⦆∶ x) (𝔹⦆∶ y) (𝔹⦆∶ z) rewrite *-distribˡ-+ x (⦅ℤ⦆ y) (⦅ℤ⦆ z) = refl
    A5 (𝔹⦆∶ x) (ℤ⦆∶ y) (ℤ⦆∶ z) rewrite *-distribˡ-+ (⦅ℤ⦆ x) y z = refl
    A5 (𝔹⦆∶ x) (ℤ⦆∶ y) (𝔹⦆∶ z) rewrite *-distribˡ-+ (⦅ℤ⦆ x) y (⦅ℤ⦆ z) = refl
    A5 (𝔹⦆∶ x) (𝔹⦆∶ y) (ℤ⦆∶ z) rewrite *-distribˡ-+ (⦅ℤ⦆ x) (⦅ℤ⦆ y) z = refl
    A5 (𝔹⦆∶ x) (𝔹⦆∶ y) (𝔹⦆∶ z) rewrite *-distribˡ-+ (⦅ℤ⦆ x) (⦅ℤ⦆ y) (⦅ℤ⦆ z) = refl


    -- The `(y ≤ᵥ x)' guarantee is not needed here with infinite arithmetic
    A6 : ∀ x y → ⊢ (y ≤ᵥ x) →  ⊢ ((x -ᵥ y) +ᵥ y) ≃ ⊢ x  -- + cancels subtraction
    A6 = go
      where
      ℤ+-cancels-y : ∀ x y → (x Int.- y) Int.+ y ≡ x
      ℤ+-cancels-y x y rewrite   ℤ+-assoc x (- y) y
                               | ℤ+-comm (- y) y
                               | m≡n⇒m-n≡0 y y refl
                               | +-identityʳ x = refl

      go : ∀ x y → ⊢ (y ≤ᵥ x) → ⊢ ((x -ᵥ y) +ᵥ y) ≃ ⊢ x
      go (ℤ⦆∶ x) (ℤ⦆∶ y) _ rewrite ℤ+-cancels-y x y =
         record { to = λ a → isjust , proj₂ a ; from = λ a → isjust , proj₂ a }
      go (ℤ⦆∶ x) (𝔹⦆∶ y) _ rewrite ℤ+-cancels-y x (⦅ℤ⦆ y) =
         record { to = λ a → isjust , proj₂ a ; from = λ a → isjust , proj₂ a }
      go (𝔹⦆∶ x) (ℤ⦆∶ y) _ rewrite ℤ+-cancels-y (⦅ℤ⦆ x) y | trans⦅𝔹⦆⦅ℤ⦆ x = 
         record { to = λ a → isjust , proj₂ a ; from = λ a → isjust , proj₂ a }
      go (𝔹⦆∶ x) (𝔹⦆∶ y) _ rewrite ℤ+-cancels-y (⦅ℤ⦆ x) (⦅ℤ⦆ y) | trans⦅𝔹⦆⦅ℤ⦆ x =
         record { to = λ a → isjust , proj₂ a ; from = λ a → isjust , proj₂ a }

    A7 : ∀ x → ⊢ (x +ᵥ  ⓪ ̇) ≃ ⊢ x
    A7 nothing = record { to = λ () ; from = λ () }
    A7 (ℤ⦆∶ x) rewrite +-identityʳ x =
         record { to = λ a → isjust , proj₂ a ; from = λ a → isjust , proj₂ a }
    A7 (𝔹⦆∶ y) rewrite +-identityʳ (⦅ℤ⦆ y)  | trans⦅𝔹⦆⦅ℤ⦆ y = 
         record { to = λ a → isjust , proj₂ a ; from = λ a → isjust , proj₂ a }

    A8 : ∀ x → (x ̇ *ᵥ ⓪ ̇) ≡ ⓪ ̇
    A8 (inj₁ x) rewrite *-zeroʳ x = refl
    A8 (inj₂ false) = refl
    A8 (inj₂ true)  = refl

    A9 : ∀ x → ⊢ (x *ᵥ  ① ̇) ≃ ⊢ x
    A9 nothing = record { to = λ () ; from = λ () }
    A9 (ℤ⦆∶ x) rewrite *-identityʳ x =
         record { to = λ a → isjust , proj₂ a ; from = λ a → isjust , proj₂ a }    
    A9 (𝔹⦆∶ y) rewrite *-identityʳ (⦅ℤ⦆ y) | trans⦅𝔹⦆⦅ℤ⦆ y = 
         record { to = λ a → isjust , proj₂ a ; from = λ a → isjust , proj₂ a }        

    -- An implementation's arithmetic strategey (whether the operations are
    -- operating on a bounded or unbounded set of integers - i.e. true
    -- Integers or 32/64-bit-words) must be identified by implementing one of
    -- the following, mutually exclusive axioms.
    -- Here we are using `true' Integers so the infinite case is implemented.
    ARITHMETIC-STRATEGY :

           -- There does 𝑛𝑜𝑡 exist a Value s.t. all other Values are lesser
           ((Σ[ x ∈ Val ] ((y : Val) → (Int∶ y) ≤ (Int∶ x))) → ⊥) -- Infinite 
           -- Or, there does exist such a max value.
         ⊎ (Σ[ max ∈ Val ] ((x : Val) → (Int∶ x) ≤ (Int∶ max)))     -- Finite

    ∞-arithmetic : (Σ[ x ∈ Val ] ((y : Val) → (Int∶ y) ≤ (Int∶ x))) → ⊥
    ∞-arithmetic (max , Ψ) = go max (Ψ (inj₁ (suc (Int∶ max))))
      where

      lem : ∀ n → Int∶ (inj₁ (suc (Int∶ n))) ≡ suc (Int∶ n)
      lem n = refl

      go₃ : ∀ n → Nat.suc n ≤ⁿ n → ⊥
      go₃ (s n) (Nat.s≤s p) = go₃ n p

      go₂ : ∀ n → suc n ≤ n → ⊥
      go₂ (𝑝 0) (+≤+ ())
      go₂ +[1+ 0 ] (+≤+ (Nat.s≤s ()))
      go₂ +[1+ s n ] (+≤+ m≤n) = go₃ (s (s n)) m≤n
      go₂ (ns (s n)) (-≤- n≤m) = go₃ n n≤m

      go : ∀ n → Int∶ (inj₁ (suc (Int∶ n))) ≤ Int∶ n → ⊥
      go n p rewrite lem n = go₂ (toIntValue n) p

    ARITHMETIC-STRATEGY = inj₁ ∞-arithmetic

    -- ARITHMETIC-STRATEGY is not finite here so this can be `⊥-elim'-ed
    OVERFLOW-STRATEGY :  ( max : Val ) → ((x : Val) → (Int∶ x) ≤ (Int∶ max))
                         →                            
                         ( max ̇ +ᵥ ① ̇ ) ≡ nothing    -- Strict Interpretation
                         ⊎
                         ( max ̇ +ᵥ ① ̇ ) ≡ max ̇               -- Firm Boundary
                         ⊎
                         ( max ̇ +ᵥ ① ̇ ) ≡ ⓪ ̇            -- Modulo Arithmetic
                         
    OVERFLOW-STRATEGY = λ max x → ⊥-elim (∞-arithmetic (max , x))


    DeMorgan₁ : ∀ x y → ¬ᵥ (x ||ᵥ y) ≡ (¬ᵥ x) &&ᵥ (¬ᵥ y)
    DeMorgan₁ nothing nothing = refl
    DeMorgan₁ nothing (just x) = refl
    DeMorgan₁ (just x) nothing = refl
    DeMorgan₁ (just (inj₁ (𝑝 0))) (just (inj₁ (𝑝 0))) = refl
    DeMorgan₁ (just (inj₁ (𝑝 0))) (just (inj₁ +[1+ _ ])) = refl
    DeMorgan₁ (just (inj₁ +[1+ _ ])) (just (inj₁ (𝑝 0))) = refl
    DeMorgan₁ (just (inj₁ +[1+ _ ])) (just (inj₁ +[1+ _ ])) = refl
    DeMorgan₁ (just (inj₁ (𝑝 0))) (just (inj₁ (ns 0))) = refl
    DeMorgan₁ (just (inj₁ (𝑝 0))) (just (inj₁ (ns (s _)))) = refl
    DeMorgan₁ (just (inj₁ +[1+ _ ])) (just (inj₁ (ns 0))) = refl
    DeMorgan₁ (just (inj₁ +[1+ _ ])) (just (inj₁ (ns (s _)))) = refl
    DeMorgan₁ (just (inj₁ (ns n))) (just (inj₁ (𝑝 _))) = refl
    DeMorgan₁ (just (inj₁ (ns n))) (just (inj₁ (ns _))) = refl
    DeMorgan₁ (just (inj₁ (𝑝 0))) (just (inj₂ false)) = refl
    DeMorgan₁ (just (inj₁ +[1+ _ ])) (just (inj₂ false)) = refl
    DeMorgan₁ (just (inj₁ (𝑝 0))) (just (inj₂ true)) = refl
    DeMorgan₁ (just (inj₁ +[1+ _ ])) (just (inj₂ true)) = refl
    DeMorgan₁ (just (inj₁ (ns 0))) (just (inj₂ false)) = refl
    DeMorgan₁ (just (inj₁ (ns (s _)))) (just (inj₂ false)) = refl
    DeMorgan₁ (just (inj₁ (ns 0))) (just (inj₂ true)) = refl
    DeMorgan₁ (just (inj₁ (ns (s _)))) (just (inj₂ true)) = refl
    DeMorgan₁ (just (inj₂ false)) (just (inj₁ (𝑝 _))) = refl
    DeMorgan₁ (just (inj₂ false)) (just (inj₁ (ns _))) = refl
    DeMorgan₁ (just (inj₂ true)) (just (inj₁ (𝑝 _))) = refl
    DeMorgan₁ (just (inj₂ true)) (just (inj₁ (ns _))) = refl
    DeMorgan₁ (just (inj₂ false)) (just (inj₂ false)) = refl
    DeMorgan₁ (just (inj₂ false)) (just (inj₂ true)) = refl
    DeMorgan₁ (just (inj₂ true)) (just (inj₂ false)) = refl
    DeMorgan₁ (just (inj₂ true)) (just (inj₂ true)) = refl


    DeMorgan₂ : ∀ x y → ¬ᵥ (x &&ᵥ y) ≡ (¬ᵥ x) ||ᵥ (¬ᵥ y)
    DeMorgan₂ nothing nothing = refl
    DeMorgan₂ nothing (just _) = refl
    DeMorgan₂ (just _) nothing = refl
    DeMorgan₂ (just (inj₁ (𝑝 0))) (just (inj₁ (𝑝 0))) = refl
    DeMorgan₂ (just (inj₁ (𝑝 0))) (just (inj₁ +[1+ _ ])) = refl
    DeMorgan₂ (just (inj₁ +[1+ _ ])) (just (inj₁ (𝑝 0))) = refl
    DeMorgan₂ (just (inj₁ +[1+ _ ])) (just (inj₁ +[1+ _ ])) = refl
    DeMorgan₂ (just (inj₁ (𝑝 0))) (just (inj₁ (ns 0))) = refl
    DeMorgan₂ (just (inj₁ (𝑝 0))) (just (inj₁ (ns (s _)))) = refl
    DeMorgan₂ (just (inj₁ +[1+ _ ])) (just (inj₁ (ns 0))) = refl
    DeMorgan₂ (just (inj₁ +[1+ _ ])) (just (inj₁ (ns (s _)))) = refl
    DeMorgan₂ (just (inj₁ (ns _))) (just (inj₁ (𝑝 _))) = refl
    DeMorgan₂ (just (inj₁ (ns _))) (just (inj₁ (ns _))) = refl
    DeMorgan₂ (just (inj₁ (𝑝 0))) (just (inj₂ false)) = refl
    DeMorgan₂ (just (inj₁ +[1+ _ ])) (just (inj₂ false)) = refl
    DeMorgan₂ (just (inj₁ (𝑝 0))) (just (inj₂ true)) = refl
    DeMorgan₂ (just (inj₁ +[1+ _ ])) (just (inj₂ true)) = refl
    DeMorgan₂ (just (inj₁ (ns 0))) (just (inj₂ false)) = refl
    DeMorgan₂ (just (inj₁ (ns (s _)))) (just (inj₂ false)) = refl
    DeMorgan₂ (just (inj₁ (ns 0))) (just (inj₂ true)) = refl
    DeMorgan₂ (just (inj₁ (ns (s _)))) (just (inj₂ true)) = refl
    DeMorgan₂ (just (inj₂ false)) (just (inj₁ (𝑝 _))) = refl
    DeMorgan₂ (just (inj₂ false)) (just (inj₁ (ns _))) = refl
    DeMorgan₂ (just (inj₂ true)) (just (inj₁ (𝑝 _))) = refl
    DeMorgan₂ (just (inj₂ true)) (just (inj₁ (ns _))) = refl
    DeMorgan₂ (just (inj₂ false)) (just (inj₂ false)) = refl
    DeMorgan₂ (just (inj₂ false)) (just (inj₂ true)) = refl
    DeMorgan₂ (just (inj₂ true)) (just (inj₂ false)) = refl
    DeMorgan₂ (just (inj₂ true)) (just (inj₂ true)) = refl


    pattern isTrue = (any-just tt) , tt
            

    ConjunctionElim₁ : ∀ x y → ⊢ (x &&ᵥ y) → ⊢ x
    ConjunctionElim₁ (just (inj₁ +[1+ _ ])) (just (inj₁ +[1+ _ ])) T = isTrue
    ConjunctionElim₁ (just (inj₁ +[1+ _ ])) (just (inj₁ (ns _))) T = isTrue
    ConjunctionElim₁ (just (inj₁ (ns _))) (just (inj₁ _)) T = isTrue
    ConjunctionElim₁ (just (inj₁ +[1+ _ ])) (just (inj₂ _)) T = isTrue
    ConjunctionElim₁ (just (inj₁ (ns _))) (just (inj₂ _)) T = isTrue
    ConjunctionElim₁ (just (inj₂ true)) (just (inj₁ _)) T = isTrue
    ConjunctionElim₁ (just (inj₂ true)) (just (inj₂ _)) T = isTrue


    ConjunctionElim₂ : ∀ x y → ⊢ (x &&ᵥ y) → ⊢ y
    ConjunctionElim₂ (just (inj₁ +[1+ _ ])) (just (inj₁ +[1+ _ ])) T = isTrue
    ConjunctionElim₂ (just (inj₁ (ns _))) (just (inj₁ +[1+ _ ])) T = isTrue
    ConjunctionElim₂ (just (inj₁ +[1+ _ ])) (just (inj₁ (ns _))) T = isTrue
    ConjunctionElim₂ (just (inj₁ (ns _))) (just (inj₁ (ns _))) T = isTrue
    ConjunctionElim₂ (just (inj₁ +[1+ _ ])) (just (inj₂ true)) T = isTrue
    ConjunctionElim₂ (just (inj₁ (ns _))) (just (inj₂ true)) T = isTrue
    ConjunctionElim₂ (just (inj₂ true)) (just (inj₁ +[1+ _ ])) T = isTrue
    ConjunctionElim₂ (just (inj₂ true)) (just (inj₁ (ns _))) T = isTrue
    ConjunctionElim₂ (just (inj₂ true)) (just (inj₂ true)) T = isTrue

    ConjunctionIntro : ∀ x y → ⊢ x → ⊢ y → ⊢ (x &&ᵥ y)
    ConjunctionIntro (just (inj₁ +[1+ _ ])) (just (inj₁ +[1+ _ ])) _ _ = isTrue
    ConjunctionIntro (just (inj₁ +[1+ _ ])) (just (inj₁ (ns _))) _ _ = isTrue
    ConjunctionIntro (just (inj₁ (ns _))) (just (inj₁ +[1+ _ ])) _ _ = isTrue
    ConjunctionIntro (just (inj₁ (ns _))) (just (inj₁ (ns _)))  _ _ = isTrue
    ConjunctionIntro (just (inj₁ +[1+ _ ])) (just (inj₂ true)) _ _ = isTrue
    ConjunctionIntro (just (inj₁ (ns _))) (just (inj₂ true)) _ _ = isTrue
    ConjunctionIntro (just (inj₂ true)) (just (inj₁ +[1+ _ ])) _ _ = isTrue
    ConjunctionIntro (just (inj₂ true)) (just (inj₁ (ns _))) _ _ = isTrue
    ConjunctionIntro (just (inj₂ true)) (just (inj₂ true)) _ _ = isTrue

    ConjunctionComm  : ∀ x y → (x &&ᵥ y) ≡ (y &&ᵥ x)
    ConjunctionComm nothing nothing = refl
    ConjunctionComm nothing (just _) = refl
    ConjunctionComm (just _) nothing = refl  
    ConjunctionComm (ℤ⦆∶ x) (ℤ⦆∶ y) rewrite ∧-comm (⦅𝔹⦆ x) (⦅𝔹⦆ y) = refl
    ConjunctionComm (ℤ⦆∶ x) (𝔹⦆∶ y) rewrite ∧-comm (⦅𝔹⦆ x) y = refl
    ConjunctionComm (𝔹⦆∶ x) (ℤ⦆∶ y) rewrite ∧-comm x (⦅𝔹⦆ y) = refl
    ConjunctionComm (𝔹⦆∶ x) (𝔹⦆∶ y) rewrite ∧-comm x y = refl

    NegationIntro : ∀ v → ⊬ v → ⊢ (¬ᵥ v)
    NegationIntro (just (inj₁ (𝑝 Nat.zero))) ⊭v = isTrue
    NegationIntro (just (inj₂ false)) ⊭v = isTrue

    NegationElim  : ∀ v → ⊬ (¬ᵥ v) → ⊢ v
    NegationElim (just (inj₁ +[1+ _ ])) ⊭¬v = isTrue
    NegationElim (just (inj₁ (ns _))) ⊭¬v = isTrue
    NegationElim (just (inj₂ true)) ⊭¬v = isTrue


  -- Identifier = ℕ
  -- Values(𝕍)  = ℤ ⊎ 𝔹 -- Arithmetic = ∞
  Data-Infinite-Arith-Implementation : Data-Implementation
  Data-Infinite-Arith-Implementation = record
                             { 𝔙 = record {Value-Implementation-Infinite}
                             ; 𝒪 = record {Operation-Implementation-Infinite}}

