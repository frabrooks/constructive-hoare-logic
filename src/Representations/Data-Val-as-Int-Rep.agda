
-- Lib imports
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; cong ; inspect ; [_] ; subst )
open import Relation.Binary using (Decidable)
open import Relation.Nullary using ( yes ; no ; ¬_ )
open import Relation.Nullary.Decidable using (False ; True ; isYes ; isNo ; ⌊_⌋ )
open import Data.Product as Pr using ( Σ ; Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂) 
open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ ; fromInj₁ ; fromInj₂ ) renaming ( [_,_] to [_⸴_] )
open import Data.Maybe
import Data.Maybe.Relation.Unary.Any 
open Data.Maybe.Relation.Unary.Any.Any renaming ( just to any-just )
open import Level
open import Data.Empty using ( ⊥ ; ⊥-elim )
open import Function using ( _∘_ ; _$_ ; id  ) renaming ( flip to ′ )
import Data.Integer as Int
import Data.Nat as Nat
open import Data.Bool
open Nat using ( ℕ ) renaming ( suc to sucn ; _≟_ to _≟ⁿ_ ) 
open import Data.Bool.Base as Bool using (true; false)
open import Agda.Builtin.Unit
open import Data.Integer.DivMod using (_div_ ; _mod_ )
open Int 
open ℤ


-- Project Imports
open import Misc
open import Data

module Representations.Data-Val-as-Int-Rep where



  module ℤ-Value-Imp where


    pattern s n = (sucn n)
    pattern ns n = (negsuc n)
    pattern 𝑝 n  = (pos n)
    pattern isjust = any-just tt

    Id = ℕ

    -- Val needs to be either ℤ or 𝔹
    Val = ℤ ⊎ Bool


    -- Casting between Ints and Truth values
    -- As per the C standard (and most languages
    -- with implicit casting between ℤ's and 𝔹's)
    -- zero is cast to false and any non-zero valid
    -- value is cast to true.
    ⦅𝔹⦆ : ℤ → Bool
    ⦅𝔹⦆ (𝑝 0)    = false
    ⦅𝔹⦆ +[1+ _ ] = true
    ⦅𝔹⦆ (ns  _ ) = true

    ⦅ℤ⦆ : Bool → ℤ
    ⦅ℤ⦆ false = 𝑝 0
    ⦅ℤ⦆ true  = 𝑝 1


    asBool : Maybe Bool → Maybe Val
    asBool = inj₂ <$>_
    asInt : Maybe ℤ → Maybe Val
    asInt  = inj₁ <$>_

    𝔁 = 0
    𝔂 = 1
    𝔃 = 2

    𝑻 : Maybe Val
    𝑻 = just (inj₂ true)

    𝑭 : Maybe Val
    𝑭 = just (inj₂ false)


    toTruthValue  : {v : Maybe Val} → WFF v → Bool
    toTruthValue {just (inj₂ b)} _ = b
    toTruthValue {just (inj₁ z)} _ = ⦅𝔹⦆ z

    -- Truth constants should trivially be WFF
    𝑻isWFF : WFF 𝑻
    𝑻isWFF = any-just tt

    𝑭isWFF : WFF 𝑭
    𝑭isWFF = any-just tt
    
    𝑻is𝑻 : (isWFF : WFF 𝑻) → toTruthValue {𝑻} isWFF ≡ true
    𝑻is𝑻 _ = refl

    𝑭is𝑭 : (isWFF : WFF 𝑭) → toTruthValue {𝑭} isWFF ≡ false
    𝑭is𝑭 _ = refl

    ⓪ : Val
    ⓪ = (inj₁ (pos 0))
    ➊ : Val
    ➊ = (inj₁ (pos 1))
    ➋ : Val
    ➋ = (inj₁ (pos 2))
    ➌ : Val
    ➌ = (inj₁ (pos 3))

    𝔁≢𝔂 : 𝔁 ≡ 𝔂 → ⊥
    𝔁≢𝔂 ()
    𝔁≢𝔃 : 𝔁 ≡ 𝔃 → ⊥
    𝔁≢𝔃 ()
    𝔂≢𝔃 : 𝔂 ≡ 𝔃 → ⊥
    𝔂≢𝔃 ()

    _?id=_ : Decidable {A = Id} _≡_ 
    _?id=_ = Nat._≟_


  module ℤ-OP-Imp where

    open ℤ-Value-Imp

    𝔡 : Value-Implementation
    𝔡 = record { ℤ-Value-Imp }

    open Value-Implementation 𝔡 using (⊢ ; ⊭)

    ----------------------------------------------------------
    -- Basic lemmas / operations

    private is-neg : ℤ → Bool
    is-neg (negsuc _) = true
    is-neg (pos    _) = false

    private is-pos : ℤ → Bool
    is-pos (pos    _) = true
    is-pos (negsuc _) = false

    private suc⊖ : ∀ m n →
              s m ⊖ s n ≡ m ⊖ n 
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
    z+-z=0 +[1+ n ]
           rewrite suc⊖ n n = n⊖n=0 n 
    z+-z=0 (negsuc n)
           rewrite suc⊖ n n = n⊖n=0 n 

    private eq : ℤ → ℤ → Bool 
    eq (𝑝  n) (𝑝  m) = n Nat.≡ᵇ m
    eq (ns n) (ns m) = n Nat.≡ᵇ m
    eq (𝑝 _)  (ns _) = false
    eq (ns _) (𝑝 _)  = false
    --eq a b = is-zero (a - b)
    -- Used for divide by zero error
    private is¬0 : ( z : ℤ )
             → Maybe (False (∣ z ∣ ≟ⁿ 0))
    is¬0 (𝑝 0)      = nothing
    is¬0 (+[1+ n ]) = just tt
    is¬0 (ns n)     = just tt

    ----------------------------------------------------------
    -- Program Operators

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

    -- Any non-zero value is taken as 𝑻 in
    -- logical statements as per C standard
    _||𝓿_ : Maybe Val → Maybe Val → Maybe Val 
    _||𝓿_ = apply⊎𝔹²→𝔹 _∨_

    _&&𝓿_ : Maybe Val → Maybe Val → Maybe Val 
    _&&𝓿_ = apply⊎𝔹²→𝔹 _∧_

    _==𝓿_ : Maybe Val → Maybe Val → Maybe Val
    _==𝓿_  = apply⊎ℤ²→𝔹 eq 

    -- 𝔹 operators with ℤ inputs
    _≤𝓿_ : Maybe Val → Maybe Val → Maybe Val 
    _≤𝓿_ = apply⊎ℤ²→𝔹 leq 
      where
      leq : ℤ → ℤ → Bool
      leq a b = is-neg ((a - b) - (𝑝 1))

    _<𝓿_ : Maybe Val → Maybe Val → Maybe Val 
    _<𝓿_ = apply⊎ℤ²→𝔹 less
      where
      less : ℤ → ℤ → Bool
      less a b = is-neg (a - b)

    _≥𝓿_ : Maybe Val → Maybe Val → Maybe Val 
    _≥𝓿_ = apply⊎ℤ²→𝔹 geq
      where
      geq : ℤ → ℤ → Bool
      geq a b = is-pos (a - b)

    _>𝓿_ : Maybe Val → Maybe Val → Maybe Val 
    _>𝓿_ = apply⊎ℤ²→𝔹 greater
      where
      greater : ℤ → ℤ → Bool
      greater a b = is-pos ((a - b) - (𝑝 1))


    -- ℤ Operators
    _+𝓿_ : Maybe Val  →  Maybe Val  →  Maybe Val
    _+𝓿_ = apply⊎ℤ²→ℤ _+_

    _-𝓿_ : Maybe Val → Maybe Val → Maybe Val
    _-𝓿_ = apply⊎ℤ²→ℤ _-_

    _*𝓿_ : Maybe Val → Maybe Val → Maybe Val
    _*𝓿_ = apply⊎ℤ²→ℤ _*_

    _/𝓿_ : Maybe Val → Maybe Val → Maybe Val
    _ /𝓿 nothing = nothing
    nothing /𝓿 just _ = nothing
    a@(just _) /𝓿 just (inj₂ b) = a /𝓿 (just (inj₁ (⦅ℤ⦆ b)))
    a@(just _) /𝓿 (just (inj₁ z)) =
      asInt ((λ a ¬0 → (a div z) {¬0})
            <$> (valAsℤ a) <*> (is¬0 z))

    _%𝓿_ : Maybe Val → Maybe Val → Maybe Val
    _ %𝓿 nothing = nothing
    nothing %𝓿 just _ = nothing
    a@(just _) %𝓿 just (inj₂ b) = a %𝓿 (just (inj₁ (⦅ℤ⦆ b)))
    a@(just _) %𝓿 (just (inj₁ z)) =
      asInt ((λ a ¬0 → 𝑝 ((a mod z) {¬0}))
            <$> (valAsℤ a) <*> (is¬0 z))


    -- Unary operators
    ¬𝓿 : Maybe Val → Maybe Val
    ¬𝓿 = asBool ∘ (Bool.not <$>_) ∘ valAs𝔹

    ++𝓿 : Maybe Val → Maybe Val
    ++𝓿 = asInt ∘ (Int.suc <$>_) ∘ valAsℤ 

    ─-𝓿 : Maybe Val → Maybe Val
    ─-𝓿 = asInt ∘ (Int.pred <$>_) ∘ valAsℤ 

    ----------------------------------------------------------
    -- Miscellaneous operator lemmas  


    ----------------------------------------------------------
    -- Operation Predicates

    -- All binary Operations

    data OP₂ : (Maybe Val → Maybe Val → Maybe Val) → Set where
      ||𝓿₂  : OP₂ (_||𝓿_) 
      &&𝓿₂  : OP₂ (_&&𝓿_)    
      ==𝓿₂  : OP₂ (_==𝓿_) 
      ≤𝓿₂   : OP₂ (_≤𝓿_)     
      <𝓿₂   : OP₂ (_<𝓿_)     
      ≥𝓿₂   : OP₂ (_≥𝓿_)     
      >𝓿₂   : OP₂ (_>𝓿_)     
      +𝓿₂   : OP₂ (_+𝓿_)     
      -𝓿₂   : OP₂ (_-𝓿_)     
      *𝓿₂   : OP₂ (_*𝓿_)     
      %𝓿₂   : OP₂ (_%𝓿_)     
      /𝓿₂   : OP₂ (_/𝓿_) 

    data OP₁ : (Maybe Val → Maybe Val) → Set where
      ¬𝓿₁    : OP₁ (¬𝓿)
      ++𝓿₁   : OP₁ (++𝓿)
      ─-𝓿₁   : OP₁ (─-𝓿)


    -- Operations that preserve WFF-ness
    data OP₂:𝑤𝑓𝑓 : ∀ {∙} → (OP₂ ∙) → Set where
      ||𝓿:𝑤𝑓𝑓    : OP₂:𝑤𝑓𝑓 ( ||𝓿₂ ) 
      &&𝓿:𝑤𝑓𝑓    : OP₂:𝑤𝑓𝑓 ( &&𝓿₂ ) 
      ==𝓿:𝑤𝑓𝑓    : OP₂:𝑤𝑓𝑓 ( ==𝓿₂ ) 
      ≤𝓿:𝑤𝑓𝑓     : OP₂:𝑤𝑓𝑓 ( ≤𝓿₂  ) 
      <𝓿:𝑤𝑓𝑓     : OP₂:𝑤𝑓𝑓 ( <𝓿₂  ) 
      ≥𝓿:𝑤𝑓𝑓     : OP₂:𝑤𝑓𝑓 ( ≥𝓿₂  ) 
      >𝓿:𝑤𝑓𝑓     : OP₂:𝑤𝑓𝑓 ( >𝓿₂  )
      +𝓿:𝑤𝑓𝑓     : OP₂:𝑤𝑓𝑓 ( +𝓿₂  )
      -𝓿:𝑤𝑓𝑓     : OP₂:𝑤𝑓𝑓 ( -𝓿₂  )
      *𝓿:𝑤𝑓𝑓     : OP₂:𝑤𝑓𝑓 ( *𝓿₂  ) 


    {-
    -- Operations with output ≃ Val (in this rep = ℤ)
    data OP₂:𝕍 : ∀ {∙} → (OP₂ ∙) → Set where
      +𝓿:𝕍 : OP₂:𝕍 ( +𝓿₂  )
      -𝓿:𝕍 : OP₂:𝕍 ( -𝓿₂  )
      *𝓿:𝕍 : OP₂:𝕍 ( *𝓿₂  )
      %𝓿:𝕍 : OP₂:𝕍 ( %𝓿₂  )
      /𝓿:𝕍 : OP₂:𝕍 ( /𝓿₂  )

    data OP₁:𝕍 : ∀ {∙} → (OP₁ ∙) → Set where
      ++𝓿:𝕍 : OP₁:𝕍 ( ++𝓿₁ )
      ─-𝓿:𝕍 : OP₁:𝕍 ( ─-𝓿₁ )
    -}


    ----------------------------------------------------------
    -- Proof of operation predicates 

    wffₒᵤₜ⇒wffᵢₙ : ∀ {∙} x (α : OP₂ ∙ ) y → WFF (∙ x y)
               → WFF x × WFF y
    wffₒᵤₜ⇒wffᵢₙ (just _) ||𝓿₂ (just _) _ = isjust , isjust
    wffₒᵤₜ⇒wffᵢₙ (just _) &&𝓿₂ (just _) _ = isjust , isjust
    wffₒᵤₜ⇒wffᵢₙ (just _) ==𝓿₂ (just _) _ = isjust , isjust
    wffₒᵤₜ⇒wffᵢₙ (just _) ≤𝓿₂  (just _) _ = isjust , isjust
    wffₒᵤₜ⇒wffᵢₙ (just _) <𝓿₂  (just _) _ = isjust , isjust
    wffₒᵤₜ⇒wffᵢₙ (just _) ≥𝓿₂  (just _) _ = isjust , isjust
    wffₒᵤₜ⇒wffᵢₙ (just _) >𝓿₂  (just _) _ = isjust , isjust
    wffₒᵤₜ⇒wffᵢₙ (just _) +𝓿₂  (just _) _ = isjust , isjust
    wffₒᵤₜ⇒wffᵢₙ (just _) -𝓿₂  (just _) _ = isjust , isjust
    wffₒᵤₜ⇒wffᵢₙ (just _) *𝓿₂  (just _) _ = isjust , isjust
    wffₒᵤₜ⇒wffᵢₙ (just _) %𝓿₂  (just _) _ = isjust , isjust
    wffₒᵤₜ⇒wffᵢₙ (just _) /𝓿₂  (just _) _ = isjust , isjust

    :𝑤𝑓𝑓₂ : ∀ {∙} {x} {y} {α : OP₂ ∙} → (𝑤𝑓𝑓 : OP₂:𝑤𝑓𝑓 α)
            → WFF x → WFF y → WFF ( ∙ x y)
    :𝑤𝑓𝑓₂ {||𝓿} {just _} {just _} (||𝓿:𝑤𝑓𝑓) _ _ = any-just tt
    :𝑤𝑓𝑓₂ {&&𝓿} {just _} {just _} (&&𝓿:𝑤𝑓𝑓) _ _ = any-just tt
    :𝑤𝑓𝑓₂ {==𝓿} {just _} {just _} (==𝓿:𝑤𝑓𝑓) _ _ = any-just tt
    :𝑤𝑓𝑓₂ {≤𝓿}  {just _} {just _} (≤𝓿:𝑤𝑓𝑓) _ _ = any-just tt
    :𝑤𝑓𝑓₂ {<𝓿}  {just _} {just _} (<𝓿:𝑤𝑓𝑓) _ _ = any-just tt
    :𝑤𝑓𝑓₂ {≥𝓿}  {just _} {just _} (≥𝓿:𝑤𝑓𝑓) _ _ = any-just tt
    :𝑤𝑓𝑓₂ {>𝓿}  {just _} {just _} (>𝓿:𝑤𝑓𝑓) _ _ = any-just tt
    :𝑤𝑓𝑓₂ {+𝓿}  {just _} {just _} (+𝓿:𝑤𝑓𝑓) _ _ = any-just tt
    :𝑤𝑓𝑓₂ {─𝓿}  {just _} {just _} (-𝓿:𝑤𝑓𝑓) _ _ = any-just tt
    :𝑤𝑓𝑓₂ {*𝓿}  {just _} {just _} (*𝓿:𝑤𝑓𝑓) _ _ = any-just tt


    :𝑤𝑓𝑓₁ : ∀ {∙} {x} (α : OP₁ ∙) → WFF x → WFF (∙ x)
    :𝑤𝑓𝑓₁ {¬𝓿}  {just _} ¬𝓿₁  _ = any-just tt
    :𝑤𝑓𝑓₁ {++𝓿} {just _} ++𝓿₁ _ = any-just tt
    :𝑤𝑓𝑓₁ {─-𝓿} {just _} ─-𝓿₁ _ = any-just tt

    DeMorgan₁ : ∀ x y → ¬𝓿 (x ||𝓿 y) ≡ (¬𝓿 x) &&𝓿 (¬𝓿 y)
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


    DeMorgan₂ : ∀ x y → ¬𝓿 (x &&𝓿 y) ≡ (¬𝓿 x) ||𝓿 (¬𝓿 y)
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


    ConjunctionElim₁ : ∀ x y → ⊢ (x &&𝓿 y) → ⊢ x
    ConjunctionElim₁ (just (inj₁ +[1+ _ ])) (just (inj₁ +[1+ _ ])) T = (any-just tt) , tt
    ConjunctionElim₁ (just (inj₁ +[1+ _ ])) (just (inj₁ (ns _))) T = (any-just tt) , tt
    ConjunctionElim₁ (just (inj₁ (ns _))) (just (inj₁ _)) T = (any-just tt) , tt
    ConjunctionElim₁ (just (inj₁ +[1+ _ ])) (just (inj₂ _)) T = (any-just tt) , tt
    ConjunctionElim₁ (just (inj₁ (ns _))) (just (inj₂ _)) T = (any-just tt) , tt
    ConjunctionElim₁ (just (inj₂ true)) (just (inj₁ _)) T = (any-just tt) , tt
    ConjunctionElim₁ (just (inj₂ true)) (just (inj₂ _)) T = (any-just tt) , tt


    ConjunctionElim₂ : ∀ x y → ⊢ (x &&𝓿 y) → ⊢ y
    ConjunctionElim₂ (just (inj₁ +[1+ _ ])) (just (inj₁ +[1+ _ ])) T = (any-just tt) , tt
    ConjunctionElim₂ (just (inj₁ (ns _))) (just (inj₁ +[1+ _ ])) T = (any-just tt) , tt
    ConjunctionElim₂ (just (inj₁ +[1+ _ ])) (just (inj₁ (ns _))) T = (any-just tt) , tt
    ConjunctionElim₂ (just (inj₁ (ns _))) (just (inj₁ (ns _))) T = (any-just tt) , tt
    ConjunctionElim₂ (just (inj₁ +[1+ _ ])) (just (inj₂ true)) T = (any-just tt) , tt
    ConjunctionElim₂ (just (inj₁ (ns _))) (just (inj₂ true)) T = (any-just tt) , tt
    ConjunctionElim₂ (just (inj₂ true)) (just (inj₁ +[1+ _ ])) T = (any-just tt) , tt
    ConjunctionElim₂ (just (inj₂ true)) (just (inj₁ (ns _))) T = (any-just tt) , tt
    ConjunctionElim₂ (just (inj₂ true)) (just (inj₂ true)) T = any-just tt , tt

    ConjunctionIntro : ∀ x y → ⊢ x → ⊢ y → ⊢ (x &&𝓿 y)
    ConjunctionIntro (just (inj₁ +[1+ _ ])) (just (inj₁ +[1+ _ ])) _ _ = any-just tt , tt
    ConjunctionIntro (just (inj₁ +[1+ _ ])) (just (inj₁ (ns Nat.zero))) _ _ = any-just tt , tt
    ConjunctionIntro (just (inj₁ +[1+ _ ])) (just (inj₁ (ns (s _)))) _ _ = any-just tt , tt
    ConjunctionIntro (just (inj₁ (ns _))) (just (inj₁ +[1+ _ ])) _ _ = any-just tt , tt
    ConjunctionIntro (just (inj₁ (ns _))) (just (inj₁ (ns _)))  _ _ = any-just tt , tt
    ConjunctionIntro (just (inj₁ +[1+ _ ])) (just (inj₂ true)) _ _ = any-just tt , tt
    ConjunctionIntro (just (inj₁ (ns _))) (just (inj₂ true)) _ _ = any-just tt , tt
    ConjunctionIntro (just (inj₂ true)) (just (inj₁ +[1+ _ ])) _ _ = any-just tt , tt
    ConjunctionIntro (just (inj₂ true)) (just (inj₁ (ns _))) _ _ = any-just tt , tt
    ConjunctionIntro (just (inj₂ true)) (just (inj₂ true)) _ _ = any-just tt , tt

    NegationIntro : ∀ v → ⊭ v → ⊢ (¬𝓿 v)
    NegationIntro (just (inj₁ (𝑝 Nat.zero))) ⊭v = (any-just tt) , tt
    NegationIntro (just (inj₂ false)) ⊭v = (any-just tt) , tt

    NegationElim  : ∀ v → ⊭ (¬𝓿 v) → ⊢ v
    NegationElim (just (inj₁ +[1+ _ ])) ⊭¬v = (any-just tt) , tt
    NegationElim (just (inj₁ (ns _))) ⊭¬v = (any-just tt) , tt
    NegationElim (just (inj₂ true)) ⊭¬v = (any-just tt) , tt


  -- Identifier = ℕ
  -- Values(:𝕍) = ℤ
  Imp : Data-Implementation
  Imp = record
    { 𝔙 = record {ℤ-Value-Imp}
    ; 𝒪 = record {ℤ-OP-Imp   }}

