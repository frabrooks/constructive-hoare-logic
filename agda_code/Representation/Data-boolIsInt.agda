
{-# OPTIONS --allow-unsolved-metas #-}
-- Abstract out the representation of data (i.e. the Values and Variables)

module Representation.Data where

  open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym ; cong ; inspect ; [_] ; subst)
  open import Relation.Binary using (Decidable)
  open import Relation.Nullary using ( yes ; no )
  open import Relation.Nullary.Decidable using (False ; True ; isYes ; isNo ; ⌊_⌋ )
  open import Data.Product as Pr using ( _×_ ; _,_ ; proj₁ ; proj₂) 
  open import Data.Sum using ( _⊎_ ; inj₁ ; inj₂ ) renaming ( [_,_] to [_⸴_] )
  open import Data.Maybe
  import Data.Maybe.Relation.Unary.Any 
  open Data.Maybe.Relation.Unary.Any.Any renaming ( just to any-just )
  open import Level
  open import Data.Empty using ( ⊥ ; ⊥-elim )
  open import Function using ( _∘_ ; _$_ ; id  ) renaming ( flip to ′ )

  import Data.Integer as Int
  import Data.Nat as Nat
  open Nat using ( ℕ ) renaming ( suc to sucn ; _≟_ to _≟ⁿ_ ) 
  open import Data.Bool.Base using (true; false)

  open import Misc


  record D-Representation : Set₁ where
    field
      Id        : Set
      Val       : Set
      𝔁         : Id
      𝔂         : Id
      𝔃         : Id


      𝑻         : Val
      𝑭         : Val

      -- More constants (perhaps unnecessary)
      NaN       : Val
      +INF      : Val
      -INF      : Val
      ⓪        : Val
      ➊        : Val
      ➋        : Val
      ➌        : Val

      -- Truisms
      𝔁≢𝔂       : 𝔁 ≡ 𝔂 → ⊥
      𝔁≢𝔃       : 𝔁 ≡ 𝔃 → ⊥
      𝔂≢𝔃       : 𝔂 ≡ 𝔃 → ⊥
      ➋≢𝑻      : ➋ ≡ 𝑻 → ⊥     
      ➋≢𝑭      : ➋ ≡ 𝑭 → ⊥

      _?id=_    : Decidable {A = Id} _≡_
      _?val=_   : Decidable {A = Val} _≡_

      -------------------------------------------------
      -- Operations
      
      -- binary 𝔹 ops
      _||𝓿_     : Maybe Val → Maybe Val → Maybe Val
      _&&𝓿_     : Maybe Val → Maybe Val → Maybe Val
      _==𝓿_     : Maybe Val → Maybe Val → Maybe Val
      _≤𝓿_      : Maybe Val → Maybe Val → Maybe Val
      _<𝓿_      : Maybe Val → Maybe Val → Maybe Val
      _≥𝓿_      : Maybe Val → Maybe Val → Maybe Val
      _>𝓿_      : Maybe Val → Maybe Val → Maybe Val

      -- binary ℤ ops
      _+𝓿_      : Maybe Val → Maybe Val → Maybe Val
      _-𝓿_      : Maybe Val → Maybe Val → Maybe Val
      _*𝓿_      : Maybe Val → Maybe Val → Maybe Val
      _%𝓿_      : Maybe Val → Maybe Val → Maybe Val
      _/𝓿_      : Maybe Val → Maybe Val → Maybe Val

      -- unary operations
      !𝓿        : Maybe Val →  Maybe Val
      ++𝓿        : Maybe Val →  Maybe Val
      ──𝓿        : Maybe Val →  Maybe Val

      -------------------------------------------------
      -- Operation predicates


      -- All binary operations
      OP² : (Maybe Val → Maybe Val → Maybe Val) → Set
      ||𝓿ᵒᵖ  : OP² (_||𝓿_) 
      &&𝓿ᵒᵖ  : OP² (_&&𝓿_)    
      ==𝓿ᵒᵖ  : OP² (_==𝓿_) 
      ≤𝓿ᵒᵖ   : OP² (_≤𝓿_ )     
      <𝓿ᵒᵖ   : OP² (_<𝓿_ )     
      ≥𝓿ᵒᵖ   : OP² (_≥𝓿_ )     
      >𝓿ᵒᵖ   : OP² (_>𝓿_ )     
      +𝓿ᵒᵖ   : OP² (_+𝓿_ )     
      -𝓿ᵒᵖ   : OP² (_-𝓿_ )     
      *𝓿ᵒᵖ   : OP² (_*𝓿_ )     
      %𝓿ᵒᵖ   : OP² (_%𝓿_ )     
      /𝓿ᵒᵖ   : OP² (_/𝓿_ )     

      ᵒᵖ²j→j : ∀ {∙} x (α : OP² ∙ ) y → Is-just (∙ x y)
               → Is-just x × Is-just y 
     
      -- ᵇᵒ = boolean output
      -- i.e. inputs ≢ nothing ⇒ output always either T/F
      ᵇᵒOP²    : ∀ {∙} → OP² ∙ → Set
      ||𝓿ᵇᵒ       : ᵇᵒOP² ||𝓿ᵒᵖ
      &&𝓿ᵇᵒ       : ᵇᵒOP² &&𝓿ᵒᵖ
      ==𝓿ᵇᵒ       : ᵇᵒOP² ==𝓿ᵒᵖ
      ≤𝓿ᵇᵒ        : ᵇᵒOP² ≤𝓿ᵒᵖ
      <𝓿ᵇᵒ        : ᵇᵒOP² <𝓿ᵒᵖ
      ≥𝓿ᵇᵒ        : ᵇᵒOP² ≥𝓿ᵒᵖ
      >𝓿ᵇᵒ        : ᵇᵒOP² >𝓿ᵒᵖ

      ᵇᵒOP¹    : (Maybe Val → Maybe Val) → Set
      !𝓿ᵇᵒ       : ᵇᵒOP¹ !𝓿

      ᵇᵒ¹ : ∀ {∙} x  → ( α : ᵇᵒOP¹ ∙ )
            → Is-just (∙ x)
            → ∙ x ≡ just 𝑻 ⊎ ∙ x ≡ just 𝑭
            
      ᵇᵒ² : ∀ {∙} {ᵒᵖ𝑝 : OP² ∙} x (α : ᵇᵒOP² ᵒᵖ𝑝 ) y
            → Is-just (∙ x y )
            → ∙ x y ≡ just 𝑻 ⊎ ∙ x y ≡ just 𝑭

      -- ᶻᵒ = Integer operation/output
      -- i.e. inputs ≢ nothing ⇒ output is a ℤ
      ᶻᵒOP²    : ∀ {∙} → OP² ∙ → Set
      +𝓿ᶻᵒ  : ᶻᵒOP² +𝓿ᵒᵖ
      -𝓿ᶻᵒ  : ᶻᵒOP² -𝓿ᵒᵖ
      *𝓿ᶻᵒ  : ᶻᵒOP² *𝓿ᵒᵖ
      %𝓿ᶻᵒ  : ᶻᵒOP² %𝓿ᵒᵖ
      /𝓿ᶻᵒ  : ᶻᵒOP² /𝓿ᵒᵖ

      ᶻᵒOP¹    : (Maybe Val → Maybe Val) → Set
      ++𝓿ᶻᵒ  : ᶻᵒOP¹ ++𝓿
      ──𝓿ᶻᵒ  : ᶻᵒOP¹ ──𝓿 
          
      ᶻᵒ² : ∀ {∙} {ᵒᵖ𝑝 : OP² ∙} (α : ᶻᵒOP² ᵒᵖ𝑝 )
            → ( ( x y : Maybe Val) → Is-just x → Is-just y
            → ∙ x y ≡ just 𝑻 ⊎ ∙ x y ≡ just 𝑭  ) → ⊥

      ᶻᵒ²' : ∀ {∙} {ᵒᵖ𝑝 : OP² ∙} ( x y : Maybe Val)
            → (α : ᶻᵒOP² ᵒᵖ𝑝 )
            → (Is-just (∙ x y)
            → ∙ x y ≡ just 𝑻 ⊎ ∙ x y ≡ just 𝑭)  → ⊥

  

  module SimpleRepresentation where

    open import Agda.Builtin.Unit
    open import Data.Integer.DivMod using (_div_ ; _mod_ )
    
    open Int 
    open ℤ


    Id  = ℕ

    -- Val needs to be either ℤ or 𝔹
    Val = Int.ℤ

    𝔁 = 0
    𝔂 = 1
    𝔃 = 2

    𝑻 = pos 1
    𝑭 = pos 0

    -- Choice of representation of
    -- NaN and INF's here is arbitrary    
    -- as long as they are abstracted away
    NaN = pos 0 -- i.e. 𝑭
    +INF = pos 1
    -INF = pos 1
    

    ⓪ = pos 0
    ➊ = pos 1
    ➋ = pos 2
    ➌ = pos 3

    
    𝔁≢𝔂 : 𝔁 ≡ 𝔂 → ⊥
    𝔁≢𝔂 ()
    𝔁≢𝔃 : 𝔁 ≡ 𝔃 → ⊥
    𝔁≢𝔃 ()
    𝔂≢𝔃 : 𝔂 ≡ 𝔃 → ⊥
    𝔂≢𝔃 ()
    ➋≢𝑻      : ➋ ≡ 𝑻 → ⊥
    ➋≢𝑻 ()
    ➋≢𝑭      : ➋ ≡ 𝑭 → ⊥
    ➋≢𝑭 ()

    _?id=_ : Decidable {A = Id} _≡_ 
    _?id=_ = Nat._≟_

    _?val=_ : Decidable {A = Val} _≡_ 
    _?val=_ = Int._≟_


    ------------------------------------------------------------------
    -- Basic lemmas / operations

    

    pattern s n = (sucn n)
    pattern ns n = (negsuc n)
    pattern 𝑝 n  = (pos n)

    private is-neg : ℤ → ℤ
    is-neg (negsuc _) = 𝑝 1
    is-neg (pos    _) = 𝑝 0

    private is-pos : ℤ → ℤ
    is-pos (pos    _) = 𝑝 1
    is-pos (negsuc _) = 𝑝 0

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

    private or : Val → Val → Val
    or (𝑝 0)  (𝑝 0)  = 𝑭
    or   _        _      = 𝑻
    private and : Val → Val → Val
    and (𝑝 0)    _      = 𝑭
    and   _      (𝑝 0)  = 𝑭
    and   _        _      = 𝑻
    private is-zeroⁿ : ℕ → ℤ
    is-zeroⁿ  0      = 𝑻
    is-zeroⁿ  _      = 𝑭
    private is-zero : ℤ → ℤ
    is-zero (𝑝 0) = 𝑻
    is-zero  _      = 𝑭
    private eq : Val → Val → Val
    eq a b = is-zero (a - b)
    -- Used for divide by zero error
    private 0→nothing : ( z : ℤ )
              → Maybe (False (∣ z ∣ ≟ⁿ 0))
    0→nothing (𝑝 0)      = nothing
    0→nothing (+[1+ n ]) = just tt
    0→nothing (ns n)     = just tt

    ---------------------------------------------------------------------------
    -- Program Operators

    -- Any non-zero value is taken as 𝑻 in
    -- logical statements as per C standard
    _||𝓿_ : Maybe ℤ → Maybe ℤ → Maybe ℤ 
    a ||𝓿 b = or <$> a <*> b
    _&&𝓿_ : Maybe ℤ → Maybe ℤ → Maybe ℤ 
    a &&𝓿 b = and <$> a <*> b
    _==𝓿_ : Maybe ℤ → Maybe ℤ → Maybe ℤ
    a ==𝓿 b = eq <$> a <*> b

    -- 𝔹 operators with ℤ inputs
    _≤𝓿_ : Maybe ℤ → Maybe ℤ → Maybe ℤ 
    a ≤𝓿 b = leq <$> a <*> b
      where
      leq : Val → Val → Val
      leq a b = is-neg ((a - b) - (𝑝 1))

    _<𝓿_ : Maybe ℤ → Maybe ℤ → Maybe ℤ 
    a <𝓿 b = less <$> a <*> b 
      where
      less : Val → Val → Val
      less a b = is-neg (a - b)

    _≥𝓿_ : Maybe ℤ → Maybe ℤ → Maybe ℤ 
    a ≥𝓿 b = geq <$> a <*> b 
      where
      geq : Val → Val → Val
      geq a b = is-pos (a - b)

    _>𝓿_ : Maybe ℤ → Maybe ℤ → Maybe ℤ 
    a >𝓿 b = greater <$> a <*> b 
      where
      greater : Val → Val → Val
      greater a b = is-pos ((a - b) - (𝑝 1))


    -- ℤ Operators
    _+𝓿_ : Maybe ℤ  →  Maybe ℤ  →  Maybe ℤ
    a +𝓿 b = (_+_) <$> a <*> b

    _-𝓿_ : Maybe ℤ → Maybe ℤ → Maybe ℤ
    a -𝓿 b = (_-_) <$> a <*> b

    _*𝓿_ : Maybe ℤ → Maybe ℤ → Maybe ℤ
    a *𝓿 b = (_*_) <$> a <*> b

    _/𝓿_ : Maybe ℤ → Maybe ℤ → Maybe ℤ
    nothing /𝓿 _ = nothing 
    a /𝓿 b = maybeDiv b <*> a
      where
      maybeDiv : Maybe ℤ → Maybe (ℤ → ℤ)
      maybeDiv nothing = nothing
      maybeDiv (just divisor) =
        (λ not0 → (λ numerator →
        (numerator div divisor) {not0}))
        <$> ( 0→nothing divisor)

    _%𝓿_ : Maybe ℤ  →  Maybe ℤ  →  Maybe ℤ
    nothing %𝓿 _ = nothing 
    a %𝓿 b = maybeMod b <*> a
      where
      maybeMod : Maybe ℤ → Maybe (ℤ → ℤ)
      maybeMod nothing = nothing
      maybeMod (just divisor) =
        (λ not0 → (λ numerator → pos
        ((numerator mod divisor) {not0})))
        <$> ( 0→nothing divisor)


    -- Unary operators
    !𝓿 : Maybe ℤ → Maybe ℤ
    !𝓿 = (eq (𝑝 0)) <$>_

    ++𝓿 : Maybe ℤ → Maybe ℤ
    ++𝓿 = (_+_ (𝑝 1)) <$>_
    
    ──𝓿 : Maybe ℤ → Maybe ℤ
    ──𝓿 = (_-_ (𝑝 1)) <$>_


    ---------------------------------------------------------------------------
    -- Miscellaneous operator lemmas
    
    ==negsuc : ∀ n m
      → just (ns (s n)) ==𝓿 just (ns (s m))
      ≡ just (ns n) ==𝓿 just (ns m)
    ==negsuc 0 0 = refl
    ==negsuc 0 (s m) = refl
    ==negsuc (s n) 0 = refl
    ==negsuc (s n) (s m)
      with (s n) Nat.<ᵇ (s m)
      | (s m) Nat.<ᵇ (s n)
    ... | false | false = refl
    ... | false | true = refl
    ... | true  | false = refl
    ... | true  | true = refl

    ==possuc : ∀ n m
      → just (+ (s n)) ==𝓿 just (+ (s m))
      ≡ just (+ n) ==𝓿 just (+ m)
    ==possuc 0 0 = refl
    ==possuc 0 (s m) = refl
    ==possuc (s n) 0 = refl
    ==possuc (s n) (s m)
      with (s n) Nat.<ᵇ (s m)
      | (s m) Nat.<ᵇ (s n)
    ... | false | false = refl
    ... | false | true = refl
    ... | true  | false = refl
    ... | true  | true = refl

    <negsuc : ∀ n m
      → just (ns (s n)) <𝓿 just (ns (s m))
      ≡ just (ns n) <𝓿 just (ns m)
    <negsuc 0 0 = refl
    <negsuc 0 (s m) = refl
    <negsuc (s n) 0 = refl
    <negsuc (s n) (s m)
      with (s n) Nat.<ᵇ (s m)
      | (s m) Nat.<ᵇ (s n)
    ... | false | false = refl
    ... | false | true = refl
    ... | true  | false = refl
    ... | true  | true = refl

    <possuc : ∀ n m
      → just (+ (s n)) <𝓿 just (+ (s m))
      ≡ just (+ n) <𝓿 just (+ m)
    <possuc 0 0 = refl
    <possuc 0 (s m) = refl
    <possuc (s n) 0 = refl
    <possuc (s n) (s m)
      with (s n) Nat.<ᵇ (s m)
      | (s m) Nat.<ᵇ (s n)
    ... | false | false = refl
    ... | false | true = refl
    ... | true  | false = refl
    ... | true  | true = refl

    ≤negsuc : ∀ n m
      → just (ns (s n)) ≤𝓿 just (ns (s m))
      ≡ just (ns n) ≤𝓿 just (ns m)
    ≤negsuc 0 0 = refl
    ≤negsuc 0 (s m) = refl
    ≤negsuc (s n) 0 = refl
    ≤negsuc (s n) (s m)
      with (s n) Nat.<ᵇ (s m)
      | (s m) Nat.<ᵇ (s n)
    ... | false | false = refl
    ... | false | true = refl
    ... | true  | false = refl
    ... | true  | true = refl

    ≤possuc : ∀ n m
      → just (+ (s n)) ≤𝓿 just (+ (s m))
      ≡ just (+ n) ≤𝓿 just (+ m)
    ≤possuc 0 0 = refl
    ≤possuc 0 (s m) = refl
    ≤possuc (s n) 0 = refl
    ≤possuc (s n) (s m)
      with (s n) Nat.<ᵇ (s m)
      | (s m) Nat.<ᵇ (s n)
    ... | false | false = refl
    ... | false | true = refl
    ... | true  | false = refl
    ... | true  | true = refl


    >negsuc : ∀ n m
      → just (ns (s n)) >𝓿 just (ns (s m))
      ≡ just (ns n) >𝓿 just (ns m)
    >negsuc 0 0 = refl
    >negsuc 0 (s m) = refl
    >negsuc (s n) 0 = refl
    >negsuc (s n) (s m)
      with (s n) Nat.<ᵇ (s m)
      | (s m) Nat.<ᵇ (s n)
    ... | false | false = refl
    ... | false | true = refl
    ... | true  | false = refl
    ... | true  | true = refl

    >possuc : ∀ n m
      → just (+ (s n)) >𝓿 just (+ (s m))
      ≡ just (+ n) >𝓿 just (+ m)
    >possuc 0 0 = refl
    >possuc 0 (s m) = refl
    >possuc (s n) 0 = refl
    >possuc (s n) (s m)
      with (s n) Nat.<ᵇ (s m)
      | (s m) Nat.<ᵇ (s n)
    ... | false | false = refl
    ... | false | true = refl
    ... | true  | false = refl
    ... | true  | true = refl


    ≥negsuc : ∀ n m
      → just (ns (s n)) ≥𝓿 just (ns (s m))
      ≡ just (ns n) ≥𝓿 just (ns m)
    ≥negsuc 0 0 = refl
    ≥negsuc 0 (s m) = refl
    ≥negsuc (s n) 0 = refl
    ≥negsuc (s n) (s m)
      with (s n) Nat.<ᵇ (s m)
      | (s m) Nat.<ᵇ (s n)
    ... | false | false = refl
    ... | false | true = refl
    ... | true  | false = refl
    ... | true  | true = refl

    ≥possuc : ∀ n m
      → just (+ (s n)) ≥𝓿 just (+ (s m))
      ≡ just (+ n) ≥𝓿 just (+ m)
    ≥possuc 0 0 = refl
    ≥possuc 0 (s m) = refl
    ≥possuc (s n) 0 = refl
    ≥possuc (s n) (s m)
      with (s n) Nat.<ᵇ (s m)
      | (s m) Nat.<ᵇ (s n)
    ... | false | false = refl
    ... | false | true = refl
    ... | true  | false = refl
    ... | true  | true = refl

    
    is-zero[ℕ]=𝑭 : ∀ n m
      → (n ≡ m → ⊥) → is-zero (m ⊖ n) ≡ 𝑭
    is-zero[ℕ]=𝑭 0 0 ¬eq = ⊥-elim (¬eq refl)
    is-zero[ℕ]=𝑭 0 (s m) _ = refl
    is-zero[ℕ]=𝑭 (s n) 0 _ = refl
    is-zero[ℕ]=𝑭 (s n) (s m) ¬eq
      rewrite suc⊖ m n = is-zero[ℕ]=𝑭 n m
      (λ eq → ¬eq (cong s eq))

    is-zero[ℤ]=𝑭 : ∀ n m
      → (n ≡ m → ⊥) → is-zero (m + - n) ≡ 𝑭
    is-zero[ℤ]=𝑭 (𝑝 0)(𝑝 0) ¬eq = ⊥-elim (¬eq refl)
    is-zero[ℤ]=𝑭 (𝑝 0)    +[1+ m ] ¬eq = refl
    is-zero[ℤ]=𝑭 +[1+ _ ] (𝑝 0)    ¬eq = refl
    is-zero[ℤ]=𝑭 (𝑝 0)    (ns _)   ¬eq = refl
    is-zero[ℤ]=𝑭 +[1+ n ] (ns m)   ¬eq = refl
    is-zero[ℤ]=𝑭 (ns n)   (𝑝 0)    ¬eq = refl
    is-zero[ℤ]=𝑭 (ns n)   +[1+ m ] ¬eq = refl
    is-zero[ℤ]=𝑭 +[1+ n ] +[1+ m ] ¬eq =
      is-zero[ℕ]=𝑭 (s n) (s m)
      (λ x → ⊥-elim (¬eq (cong pos x)))
    is-zero[ℤ]=𝑭 (ns n) (ns m) ¬eq =
      is-zero[ℕ]=𝑭 (s m) (s n)
      (λ x → ⊥-elim (¬eq (cong toNegsuc (sym x) )))
      where
      toNegsuc : ℕ → ℤ
      toNegsuc 0 = ns 0
      toNegsuc (s y) = ns y
    
  
    ---------------------------------------------------------------------------
    -- Operation Predicates

    -- All binary Operations
    
    data OP² : (Maybe ℤ → Maybe ℤ → Maybe ℤ) → Set where
      ||𝓿ᵒᵖ  : OP² (_||𝓿_) 
      &&𝓿ᵒᵖ  : OP² (_&&𝓿_)    
      ==𝓿ᵒᵖ  : OP² (_==𝓿_) 
      ≤𝓿ᵒᵖ   : OP² (_≤𝓿_)     
      <𝓿ᵒᵖ   : OP² (_<𝓿_)     
      ≥𝓿ᵒᵖ   : OP² (_≥𝓿_)     
      >𝓿ᵒᵖ   : OP² (_>𝓿_)     
      +𝓿ᵒᵖ   : OP² (_+𝓿_)     
      -𝓿ᵒᵖ   : OP² (_-𝓿_)     
      *𝓿ᵒᵖ   : OP² (_*𝓿_)     
      %𝓿ᵒᵖ   : OP² (_%𝓿_)     
      /𝓿ᵒᵖ   : OP² (_/𝓿_) 

    OP¹ = Maybe ℤ → Maybe ℤ

      
    data ᵇᵒOP² : ∀ {∙} → (OP² ∙) → Set where
      ||𝓿ᵇᵒ    : ᵇᵒOP² ( ||𝓿ᵒᵖ ) 
      &&𝓿ᵇᵒ    : ᵇᵒOP² ( &&𝓿ᵒᵖ ) 
      ==𝓿ᵇᵒ    : ᵇᵒOP² ( ==𝓿ᵒᵖ ) 
      ≤𝓿ᵇᵒ     : ᵇᵒOP² ( ≤𝓿ᵒᵖ  ) 
      <𝓿ᵇᵒ     : ᵇᵒOP² ( <𝓿ᵒᵖ  ) 
      ≥𝓿ᵇᵒ     : ᵇᵒOP² ( ≥𝓿ᵒᵖ  ) 
      >𝓿ᵇᵒ     : ᵇᵒOP² ( >𝓿ᵒᵖ  ) 


    data ᵇᵒOP¹  : OP¹ → Set where
      !𝓿ᵇᵒ     : ᵇᵒOP¹ !𝓿


    data ᶻᵒOP² : ∀ {∙} → (OP² ∙) → Set where
      +𝓿ᶻᵒ : ᶻᵒOP² ( +𝓿ᵒᵖ  )
      -𝓿ᶻᵒ : ᶻᵒOP² ( -𝓿ᵒᵖ  )
      *𝓿ᶻᵒ : ᶻᵒOP² ( *𝓿ᵒᵖ  )
      %𝓿ᶻᵒ : ᶻᵒOP² ( %𝓿ᵒᵖ  )
      /𝓿ᶻᵒ : ᶻᵒOP² ( /𝓿ᵒᵖ  )

    data ᶻᵒOP¹ : OP¹ → Set where
      ++𝓿ᶻᵒ : ᶻᵒOP¹ ( ++𝓿 )
      ──𝓿ᶻᵒ : ᶻᵒOP¹ ( ──𝓿 )

    --------------------------------------------------------------------
    -- Proof of operation predicates 

    -- Used to simplify proof below NO LONGER NEEDED
    --∙⇒  : ( Val → Val → Val ) → ( Maybe ℤ → Maybe ℤ → Maybe ℤ )
    --∙⇒ ∙ = (λ a b → ap (maybe (λ x → just (∙ x)) nothing a) b)
    --∙⇒' : ( Val → Val ) → (Val → Val)  → ( Maybe ℤ → Maybe ℤ → Maybe ℤ )
    --∙⇒' is-? exp = ∙⇒ ( λ x → ( λ y → is-? $ exp (x + - y )  ))
    -- n.b flip has been renamed to ′

    -- Patterns just to make the proof below more readable
    pattern ≡𝑻 = (inj₁ refl)
    pattern ≡𝑭 = (inj₂ refl)
    pattern 𝟘     = (just (𝑝 0))
    pattern ≥1 n  = (just +[1+ n ])
    pattern 𝟘≤ n  = (just (𝑝 n))
    pattern ─1    = (just (negsuc 0))
    pattern ≤-1 n = (just (negsuc n))
    pattern ≤-2 n = (just (negsuc (sucn n)))
    pattern isJust = any-just tt


    ᵇᵒ² : ∀ {∙} {ᵒᵖ𝑝 : OP² ∙} x (α : ᵇᵒOP² ᵒᵖ𝑝 ) y → Is-just (∙ x y)
             → ∙ x y ≡ just 𝑻 ⊎ ∙ x y ≡ just 𝑭
    -- The following can essentially be read as truth tables
    -- (keeping in mind that what we're really pattern matching
    -- on is the underlying ℕ within the ℤ (as ℤ is defined in
    -- terms of ℕ). This means there are two base cases - those
    -- being: ((pos zero) : ℤ ) ≡ 𝟘 and, ((negsuc zero) : ℤ ) ≡ ─1
    -- ------------------------------------------------------------------
    -- OR 
    ᵇᵒ² {._||𝓿_}  𝟘        ||𝓿ᵇᵒ   𝟘                 _  = ≡𝑭
    ᵇᵒ² {._||𝓿_}  𝟘        ||𝓿ᵇᵒ   ─1                _  = ≡𝑻
    ᵇᵒ² {._||𝓿_}  𝟘        ||𝓿ᵇᵒ   (≤-2 _)           _  = ≡𝑻
    ᵇᵒ² {._||𝓿_}  𝟘        ||𝓿ᵇᵒ   (≥1 _)            _  = ≡𝑻
    
    ᵇᵒ² {._||𝓿_}  ─1       ||𝓿ᵇᵒ   𝟘                 _  = ≡𝑻
    ᵇᵒ² {._||𝓿_}  ─1       ||𝓿ᵇᵒ   ─1                _  = ≡𝑻
    ᵇᵒ² {._||𝓿_}  ─1       ||𝓿ᵇᵒ   (≤-2 _)           _  = ≡𝑻
    ᵇᵒ² {._||𝓿_}  ─1       ||𝓿ᵇᵒ   (≥1 _)            _  = ≡𝑻

    ᵇᵒ² {._||𝓿_}  (≤-2 _)  ||𝓿ᵇᵒ   𝟘                 _  = ≡𝑻
    ᵇᵒ² {._||𝓿_}  (≤-2 _)  ||𝓿ᵇᵒ   ─1                _  = ≡𝑻
    ᵇᵒ² {._||𝓿_}  (≤-2 _)  ||𝓿ᵇᵒ   (≤-2 _)           _  = ≡𝑻
    ᵇᵒ² {._||𝓿_}  (≤-2 _)  ||𝓿ᵇᵒ   (≥1  _)           _  = ≡𝑻

    ᵇᵒ² {._||𝓿_}  (≥1  _)  ||𝓿ᵇᵒ   𝟘                 _  = ≡𝑻
    ᵇᵒ² {._||𝓿_}  (≥1  _)  ||𝓿ᵇᵒ   ─1                _  = ≡𝑻  
    ᵇᵒ² {._||𝓿_}  (≥1  _)  ||𝓿ᵇᵒ   (≤-2 _)           _  = ≡𝑻
    ᵇᵒ² {._||𝓿_}  (≥1  _)  ||𝓿ᵇᵒ   (≥1  _)           _  = ≡𝑻

    -- AND
    ᵇᵒ² {._&&𝓿_}  𝟘       &&𝓿ᵇᵒ   𝟘                  _  = ≡𝑭
    ᵇᵒ² {._&&𝓿_}  𝟘       &&𝓿ᵇᵒ   ─1                 _  = ≡𝑭
    ᵇᵒ² {._&&𝓿_}  𝟘       &&𝓿ᵇᵒ   (≤-2 _)            _  = ≡𝑭
    ᵇᵒ² {._&&𝓿_}  𝟘       &&𝓿ᵇᵒ   (≥1 _)             _  = ≡𝑭

    ᵇᵒ² {._&&𝓿_}  ─1      &&𝓿ᵇᵒ   𝟘                  _  = ≡𝑭
    ᵇᵒ² {._&&𝓿_}  ─1      &&𝓿ᵇᵒ   ─1                 _  = ≡𝑻
    ᵇᵒ² {._&&𝓿_}  ─1      &&𝓿ᵇᵒ   (≤-2 _)            _  = ≡𝑻
    ᵇᵒ² {._&&𝓿_}  ─1      &&𝓿ᵇᵒ   (≥1 _)             _  = ≡𝑻

    ᵇᵒ² {._&&𝓿_}  (≤-2 _) &&𝓿ᵇᵒ   𝟘                  _  = ≡𝑭
    ᵇᵒ² {._&&𝓿_}  (≤-2 _) &&𝓿ᵇᵒ   ─1                 _  = ≡𝑻
    ᵇᵒ² {._&&𝓿_}  (≤-2 _) &&𝓿ᵇᵒ   (≤-2 _)            _  = ≡𝑻
    ᵇᵒ² {._&&𝓿_}  (≤-2 _) &&𝓿ᵇᵒ   (≥1  _)            _  = ≡𝑻
    
    ᵇᵒ² {._&&𝓿_}  (≥1  _) &&𝓿ᵇᵒ   𝟘                  _  = ≡𝑭
    ᵇᵒ² {._&&𝓿_}  (≥1  _) &&𝓿ᵇᵒ   ─1                 _  = ≡𝑻
    ᵇᵒ² {._&&𝓿_}  (≥1  _) &&𝓿ᵇᵒ   (≤-2 _)            _  = ≡𝑻
    ᵇᵒ² {._&&𝓿_}  (≥1  _) &&𝓿ᵇᵒ   (≥1  _)            _  = ≡𝑻

    -- EQUALITY
    ᵇᵒ² {._==𝓿_}  𝟘       ==𝓿ᵇᵒ   𝟘                  _  = ≡𝑻
    ᵇᵒ² {._==𝓿_}  𝟘       ==𝓿ᵇᵒ   ─1                 _  = ≡𝑭
    ᵇᵒ² {._==𝓿_}  𝟘       ==𝓿ᵇᵒ   (≤-2 _)            _  = ≡𝑭
    ᵇᵒ² {._==𝓿_}  𝟘       ==𝓿ᵇᵒ   (≥1 _)             _  = ≡𝑭

    ᵇᵒ² {._==𝓿_}  ─1      ==𝓿ᵇᵒ   𝟘                  _  = ≡𝑭
    ᵇᵒ² {._==𝓿_}  ─1      ==𝓿ᵇᵒ   ─1                 _  = ≡𝑻
    ᵇᵒ² {._==𝓿_}  ─1      ==𝓿ᵇᵒ   (≤-2 _)            _  = ≡𝑭
    ᵇᵒ² {._==𝓿_}  ─1      ==𝓿ᵇᵒ   (≥1 _)             _  = ≡𝑭
    
    ᵇᵒ² {._==𝓿_}  (≤-2 _) ==𝓿ᵇᵒ   𝟘                  _  = ≡𝑭
    ᵇᵒ² {._==𝓿_}  (≤-2 _) ==𝓿ᵇᵒ   ─1                 _  = ≡𝑭
    ᵇᵒ² {._==𝓿_}  (≤-2 n) ==𝓿ᵇᵒ   (≥1  m)            _  = ≡𝑭
    ᵇᵒ² {._==𝓿_}  (≤-2 n) ==𝓿ᵇᵒ   (≤-2 m)            _
        rewrite ==negsuc n m
        with n ≟ⁿ m | m ⊖ n | inspect (_⊖_ m) n
    ... | yes p | _  | _  rewrite p | suc⊖ m  m | n⊖n=0 m = ≡𝑻
    ... | no ¬p | (𝑝 0)      | [ q ] rewrite suc⊖ m n | q = ≡𝑻
    ... | no ¬p | (pos (s x))| [ q ] rewrite suc⊖ m n | q = ≡𝑭
    ... | no ¬p | (ns  y)    | [ q ] rewrite suc⊖ m n | q = ≡𝑭

    ᵇᵒ² {._==𝓿_}  (≥1  _) ==𝓿ᵇᵒ   𝟘                  _  = ≡𝑭
    ᵇᵒ² {._==𝓿_}  (≥1  _) ==𝓿ᵇᵒ   ─1                 _  = ≡𝑭
    ᵇᵒ² {._==𝓿_}  (≥1  n) ==𝓿ᵇᵒ   (≤-2 m)            _  = ≡𝑭
    ᵇᵒ² {._==𝓿_}  (≥1  n) ==𝓿ᵇᵒ   (≥1  m)            _
        rewrite ==possuc n m
        with (𝑝 n + - 𝑝 m) | inspect (λ m → 𝑝 n + - 𝑝 m) m
    ... | (𝑝 0)      | [ q ] rewrite suc⊖ m n | q        = ≡𝑻
    ... | (pos (s _))| [ q ] rewrite suc⊖ m n | q        = ≡𝑭
    ... | (ns  _)    | [ q ] rewrite suc⊖ m n | q        = ≡𝑭

    -- LESS THAN
    ᵇᵒ² {._<𝓿_}    𝟘       <𝓿ᵇᵒ   𝟘                   _ = ≡𝑭
    ᵇᵒ² {._<𝓿_}    𝟘       <𝓿ᵇᵒ   ─1                  _ = ≡𝑭
    ᵇᵒ² {._<𝓿_}    𝟘       <𝓿ᵇᵒ   (≤-2 _)             _ = ≡𝑭
    ᵇᵒ² {._<𝓿_}    𝟘       <𝓿ᵇᵒ   (≥1 _)              _ = ≡𝑻
 
    ᵇᵒ² {._<𝓿_}    ─1      <𝓿ᵇᵒ   𝟘                   _ = ≡𝑻
    ᵇᵒ² {._<𝓿_}    ─1      <𝓿ᵇᵒ   ─1                  _ = ≡𝑭
    ᵇᵒ² {._<𝓿_}    ─1      <𝓿ᵇᵒ   (≤-2 _)             _ = ≡𝑭
    ᵇᵒ² {._<𝓿_}    ─1      <𝓿ᵇᵒ   (≥1 _)              _ = ≡𝑻

    ᵇᵒ² {._<𝓿_}    (≤-2 _) <𝓿ᵇᵒ   𝟘                   _ = ≡𝑻
    ᵇᵒ² {._<𝓿_}    (≤-2 _) <𝓿ᵇᵒ   ─1                  _ = ≡𝑻
    ᵇᵒ² {._<𝓿_}    (≤-2 _) <𝓿ᵇᵒ   (≥1  _)             _ = ≡𝑻
    ᵇᵒ² {._<𝓿_}    (≤-2 n) <𝓿ᵇᵒ   (≤-2 m)             _
        rewrite <negsuc n m
        with  m ⊖ n | inspect  (_⊖_ m) n
    ... | (pos _) | [ q ] rewrite suc⊖ m n | q           = ≡𝑭
    ... | (ns  _) | [ q ] rewrite suc⊖ m n | q           = ≡𝑻

    ᵇᵒ² {._<𝓿_}    (≥1  _) <𝓿ᵇᵒ   𝟘                   _ = ≡𝑭
    ᵇᵒ² {._<𝓿_}    (≥1  _) <𝓿ᵇᵒ   ─1                  _ = ≡𝑭
    ᵇᵒ² {._<𝓿_}    (≥1  _) <𝓿ᵇᵒ   (≤-2 _)             _ = ≡𝑭
    ᵇᵒ² {._<𝓿_}    (≥1  n) <𝓿ᵇᵒ   (≥1  m)             _
        rewrite <possuc n m
        with (𝑝 n + - 𝑝 m) | inspect (λ m' → 𝑝 n + - 𝑝 m') m
    ... | (𝑝 0)    | [ q ] rewrite suc⊖ m n | q          = ≡𝑭
    ... | (pos (s _))| [ q ] rewrite suc⊖ m n | q        = ≡𝑭
    ... | (ns  _)    | [ q ] rewrite suc⊖ m n | q        = ≡𝑻


    -- GEQ
    ᵇᵒ² {._≥𝓿_}    𝟘       ≥𝓿ᵇᵒ   𝟘                   _ = ≡𝑻
    ᵇᵒ² {._≥𝓿_}    𝟘       ≥𝓿ᵇᵒ   ─1                  _ = ≡𝑻
    ᵇᵒ² {._≥𝓿_}    𝟘       ≥𝓿ᵇᵒ   (≤-2 _)             _ = ≡𝑻
    ᵇᵒ² {._≥𝓿_}    𝟘       ≥𝓿ᵇᵒ   (≥1 _)              _ = ≡𝑭
 
    ᵇᵒ² {._≥𝓿_}    ─1      ≥𝓿ᵇᵒ   𝟘                   _ = ≡𝑭
    ᵇᵒ² {._≥𝓿_}    ─1      ≥𝓿ᵇᵒ   ─1                  _ = ≡𝑻
    ᵇᵒ² {._≥𝓿_}    ─1      ≥𝓿ᵇᵒ   (≤-2 _)             _ = ≡𝑻
    ᵇᵒ² {._≥𝓿_}    ─1      ≥𝓿ᵇᵒ   (≥1 _)              _ = ≡𝑭

    ᵇᵒ² {._≥𝓿_}    (≤-2 _) ≥𝓿ᵇᵒ   𝟘                   _ = ≡𝑭
    ᵇᵒ² {._≥𝓿_}    (≤-2 _) ≥𝓿ᵇᵒ   ─1                  _ = ≡𝑭
    ᵇᵒ² {._≥𝓿_}    (≤-2 _) ≥𝓿ᵇᵒ   (≥1  _)             _ = ≡𝑭
    ᵇᵒ² {._≥𝓿_}    (≤-2 n) ≥𝓿ᵇᵒ   (≤-2 m)             _
        rewrite ≥negsuc n m
        with  m ⊖ n | inspect  (_⊖_ m) n
    ... | (pos _) | [ q ] rewrite suc⊖ m n | q           = ≡𝑻
    ... | (ns  _) | [ q ] rewrite suc⊖ m n | q           = ≡𝑭

    ᵇᵒ² {._≥𝓿_}    (≥1  _) ≥𝓿ᵇᵒ   𝟘                   _ = ≡𝑻
    ᵇᵒ² {._≥𝓿_}    (≥1  _) ≥𝓿ᵇᵒ   ─1                  _ = ≡𝑻
    ᵇᵒ² {._≥𝓿_}    (≥1  _) ≥𝓿ᵇᵒ   (≤-2 _)             _ = ≡𝑻
    ᵇᵒ² {._≥𝓿_}    (≥1  n) ≥𝓿ᵇᵒ   (≥1  m)             _
        rewrite ≥possuc n m
        with (𝑝 n + - 𝑝 m) | inspect (λ m' → 𝑝 n + - 𝑝 m') m
    ... | (𝑝 0)      | [ q ] rewrite suc⊖ m n | q        = ≡𝑻
    ... | (pos (s _))| [ q ] rewrite suc⊖ m n | q        = ≡𝑻
    ... | (ns  _)    | [ q ] rewrite suc⊖ m n | q        = ≡𝑭



    -- LEQ
    ᵇᵒ² {._≤𝓿_}    𝟘       ≤𝓿ᵇᵒ   𝟘                   _ = ≡𝑻
    ᵇᵒ² {._≤𝓿_}    𝟘       ≤𝓿ᵇᵒ   ─1                  _ = ≡𝑭
    ᵇᵒ² {._≤𝓿_}    𝟘       ≤𝓿ᵇᵒ   (≤-2 _)             _ = ≡𝑭
    ᵇᵒ² {._≤𝓿_}    𝟘       ≤𝓿ᵇᵒ   (≥1 _)              _ = ≡𝑻
 
    ᵇᵒ² {._≤𝓿_}    ─1      ≤𝓿ᵇᵒ   𝟘                   _ = ≡𝑻
    ᵇᵒ² {._≤𝓿_}    ─1      ≤𝓿ᵇᵒ   ─1                  _ = ≡𝑻
    ᵇᵒ² {._≤𝓿_}    ─1      ≤𝓿ᵇᵒ   (≤-2 _)             _ = ≡𝑭
    ᵇᵒ² {._≤𝓿_}    ─1      ≤𝓿ᵇᵒ   (≥1 _)              _ = ≡𝑻

    ᵇᵒ² {._≤𝓿_}    (≤-2 _) ≤𝓿ᵇᵒ   𝟘                   _ = ≡𝑻
    ᵇᵒ² {._≤𝓿_}    (≤-2 _) ≤𝓿ᵇᵒ   ─1                  _ = ≡𝑻
    ᵇᵒ² {._≤𝓿_}    (≤-2 _) ≤𝓿ᵇᵒ   (≥1  _)             _ = ≡𝑻
    ᵇᵒ² {._≤𝓿_}    (≤-2 n) ≤𝓿ᵇᵒ   (≤-2 m)             _
        rewrite ≤negsuc n m
        with  m ⊖ n   | inspect  (_⊖_ m) n
    ... | (𝑝 0)       | [ q ] rewrite suc⊖ m n | q       = ≡𝑻
    ... | (pos (s _)) | [ q ] rewrite suc⊖ m n | q       = ≡𝑭
    ... | (ns  _)     | [ q ] rewrite suc⊖ m n | q       = ≡𝑻

    ᵇᵒ² {._≤𝓿_}    (≥1  _) ≤𝓿ᵇᵒ   𝟘                   _ = ≡𝑭
    ᵇᵒ² {._≤𝓿_}    (≥1  _) ≤𝓿ᵇᵒ   ─1                  _ = ≡𝑭
    ᵇᵒ² {._≤𝓿_}    (≥1  _) ≤𝓿ᵇᵒ   (≤-2 _)             _ = ≡𝑭
    ᵇᵒ² {._≤𝓿_}    (≥1  n) ≤𝓿ᵇᵒ   (≥1  m)             _
        rewrite ≤possuc n m
        with (𝑝 n + - 𝑝 m) | inspect (λ m' → 𝑝 n + - 𝑝 m') m
    ... | (𝑝 0)    | [ q ] rewrite suc⊖ m n | q          = ≡𝑻
    ... | (pos (s _))| [ q ] rewrite suc⊖ m n | q        = ≡𝑭
    ... | (ns  _)    | [ q ] rewrite suc⊖ m n | q        = ≡𝑻


    
    -- GREATER THAN
    ᵇᵒ² {._>𝓿_}    𝟘       >𝓿ᵇᵒ   𝟘                   _ = ≡𝑭
    ᵇᵒ² {._>𝓿_}    𝟘       >𝓿ᵇᵒ   ─1                  _ = ≡𝑻
    ᵇᵒ² {._>𝓿_}    𝟘       >𝓿ᵇᵒ   (≤-2 _)             _ = ≡𝑻
    ᵇᵒ² {._>𝓿_}    𝟘       >𝓿ᵇᵒ   (≥1 _)              _ = ≡𝑭
 
    ᵇᵒ² {._>𝓿_}    ─1      >𝓿ᵇᵒ   𝟘                   _ = ≡𝑭
    ᵇᵒ² {._>𝓿_}    ─1      >𝓿ᵇᵒ   ─1                  _ = ≡𝑭
    ᵇᵒ² {._>𝓿_}    ─1      >𝓿ᵇᵒ   (≤-2 _)             _ = ≡𝑻
    ᵇᵒ² {._>𝓿_}    ─1      >𝓿ᵇᵒ   (≥1 _)              _ = ≡𝑭

    ᵇᵒ² {._>𝓿_}    (≤-2 _) >𝓿ᵇᵒ   𝟘                   _ = ≡𝑭
    ᵇᵒ² {._>𝓿_}    (≤-2 _) >𝓿ᵇᵒ   ─1                  _ = ≡𝑭
    ᵇᵒ² {._>𝓿_}    (≤-2 _) >𝓿ᵇᵒ   (≥1  _)             _ = ≡𝑭
    ᵇᵒ² {._>𝓿_}    (≤-2 n) >𝓿ᵇᵒ   (≤-2 m)             _
        rewrite >negsuc n m
        with  m ⊖ n | inspect  (_⊖_ m) n
    ... | (𝑝 0)      | [ q ] rewrite suc⊖ m n | q        = ≡𝑭
    ... | (pos (s _))| [ q ] rewrite suc⊖ m n | q        = ≡𝑻
    ... | (ns  y)    | [ q ] rewrite suc⊖ m n | q        = ≡𝑭

    ᵇᵒ² {._>𝓿_}    (≥1  _) >𝓿ᵇᵒ   𝟘                    _ = ≡𝑻
    ᵇᵒ² {._>𝓿_}    (≥1  _) >𝓿ᵇᵒ   ─1                   _ = ≡𝑻
    ᵇᵒ² {._>𝓿_}    (≥1  _) >𝓿ᵇᵒ   (≤-2 _)              _ = ≡𝑻
    ᵇᵒ² {._>𝓿_}    (≥1  n) >𝓿ᵇᵒ   (≥1  m)              _
        rewrite >possuc n m
        with (𝑝 n + - 𝑝 m) | inspect (λ m' → 𝑝 n + - 𝑝 m') m
    ... | (𝑝 0)      | [ q ] rewrite suc⊖ m n | q        = ≡𝑭
    ... | (pos (s _))| [ q ] rewrite suc⊖ m n | q        = ≡𝑻
    ... | (ns  _)    | [ q ] rewrite suc⊖ m n | q        = ≡𝑭

    ᵇᵒ¹ : ∀ {∙} x  → ( α : ᵇᵒOP¹ ∙ )
          → Is-just (∙ x)
          → ∙ x ≡ just 𝑻 ⊎ ∙ x ≡ just 𝑭
    ᵇᵒ¹ {.!𝓿} 𝟘       !𝓿ᵇᵒ _ = ≡𝑻
    ᵇᵒ¹ {.!𝓿} (≥1 _)  !𝓿ᵇᵒ _ = ≡𝑭
    ᵇᵒ¹ {.!𝓿} (≤-1 _) !𝓿ᵇᵒ _ = ≡𝑭

    
    ᶻᵒ² : ∀ {∙} {ᵒᵖ𝑝 : OP² ∙} (α : ᶻᵒOP² ᵒᵖ𝑝 )
            → ( ( x y : Maybe Val) → Is-just x → Is-just y
            → ∙ x y ≡ just 𝑻 ⊎ ∙ x y ≡ just 𝑭  ) → ⊥
    ᶻᵒ² {._+𝓿_} +𝓿ᶻᵒ f with f (just ➋) (just ➋) (any-just tt) (any-just tt)
    ... | inj₁ ()            -- 2 + 2 ≢ 1 V 0
    ... | inj₂ ()
    ᶻᵒ² {._-𝓿_} -𝓿ᶻᵒ f with f (just ➌) (just ➊) (any-just tt) (any-just tt)
    ... | inj₁ ()            -- 3 - 1 ≢ 1 V 0
    ... | inj₂ ()
    ᶻᵒ² {._*𝓿_} *𝓿ᶻᵒ f with f (just ➋) (just ➊) (any-just tt) (any-just tt)
    ... | inj₁ ()            -- 2 * 1 ≢ 1 V 0
    ... | inj₂ ()
    ᶻᵒ² {._%𝓿_} %𝓿ᶻᵒ f with f (just ➌) (just (𝑝 0)) (any-just tt) (any-just tt)
    ... | inj₁ ()            -- 3 % 0 ≢ 1 V 0
    ... | inj₂ ()
    ᶻᵒ² {._/𝓿_} /𝓿ᶻᵒ f with f (just ➌) (just (𝑝 0)) (any-just tt) (any-just tt)
    ... | inj₁ ()            -- 3 ? 0 ≢ 1 V 0
    ... | inj₂ ()
    
    ᶻᵒ²' : ∀ {∙} {ᵒᵖ𝑝 : OP² ∙} ( x y : Maybe Val)
            → (α : ᶻᵒOP² ᵒᵖ𝑝 )
            → (Is-just (∙ x y)
            → ∙ x y ≡ just 𝑻 ⊎ ∙ x y ≡ just 𝑭)  → ⊥
    ᶻᵒ²' {._+𝓿_} x y +𝓿ᶻᵒ f = {!!}
    ᶻᵒ²' {._-𝓿_} x y -𝓿ᶻᵒ f = {!!}
    ᶻᵒ²' {._*𝓿_} x y *𝓿ᶻᵒ f = {!!}
    ᶻᵒ²' {._%𝓿_} x y %𝓿ᶻᵒ f = {!!}
    ᶻᵒ²' {._/𝓿_} x y /𝓿ᶻᵒ f = {!!}



    ᵒᵖ²j→j : ∀ {∙} x (α : OP² ∙ ) y → Is-just (∙ x y)
               → Is-just x × Is-just y
    ᵒᵖ²j→j {._||𝓿_} (𝟘≤ n)  ||𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._||𝓿_} (𝟘≤ n)  ||𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust
    ᵒᵖ²j→j {._||𝓿_} (≤-1 n) ||𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._||𝓿_} (≤-1 n) ||𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust

    ᵒᵖ²j→j {._&&𝓿_} (𝟘≤ n)  &&𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._&&𝓿_} (𝟘≤ n)  &&𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust
    ᵒᵖ²j→j {._&&𝓿_} (≤-1 n) &&𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._&&𝓿_} (≤-1 n) &&𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust

    ᵒᵖ²j→j {._==𝓿_} (𝟘≤ n)  ==𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._==𝓿_} (𝟘≤ n)  ==𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust
    ᵒᵖ²j→j {._==𝓿_} (≤-1 n) ==𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._==𝓿_} (≤-1 n) ==𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust

    ᵒᵖ²j→j {._≤𝓿_}  (𝟘≤ n)  ≤𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._≤𝓿_}  (𝟘≤ n)  ≤𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust
    ᵒᵖ²j→j {._≤𝓿_}  (≤-1 n) ≤𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._≤𝓿_}  (≤-1 n) ≤𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust

    ᵒᵖ²j→j {._<𝓿_}  (𝟘≤ n)  <𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._<𝓿_}  (𝟘≤ n)  <𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust
    ᵒᵖ²j→j {._<𝓿_}  (≤-1 n) <𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._<𝓿_}  (≤-1 n) <𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust
    
    ᵒᵖ²j→j {._≥𝓿_}  (𝟘≤ n)  ≥𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._≥𝓿_}  (𝟘≤ n)  ≥𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust
    ᵒᵖ²j→j {._≥𝓿_}  (≤-1 n) ≥𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._≥𝓿_}  (≤-1 n) ≥𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust
    
    ᵒᵖ²j→j {._>𝓿_}  (𝟘≤ n)  >𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._>𝓿_}  (𝟘≤ n)  >𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust
    ᵒᵖ²j→j {._>𝓿_}  (≤-1 n) >𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._>𝓿_}  (≤-1 n) >𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust
    
    ᵒᵖ²j→j {._+𝓿_}  (𝟘≤ n)  +𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._+𝓿_}  (𝟘≤ n)  +𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust
    ᵒᵖ²j→j {._+𝓿_}  (≤-1 n) +𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._+𝓿_}  (≤-1 n) +𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust
    
    ᵒᵖ²j→j {._-𝓿_}  (𝟘≤ n)  -𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._-𝓿_}  (𝟘≤ n)  -𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust
    ᵒᵖ²j→j {._-𝓿_}  (≤-1 n) -𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._-𝓿_}  (≤-1 n) -𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust
    
    ᵒᵖ²j→j {._*𝓿_}  (𝟘≤ n)  *𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._*𝓿_}  (𝟘≤ n)  *𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust
    ᵒᵖ²j→j {._*𝓿_}  (≤-1 n) *𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._*𝓿_}  (≤-1 n) *𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust

    ᵒᵖ²j→j {._%𝓿_} nothing  %𝓿ᵒᵖ nothing  ()
    ᵒᵖ²j→j {._%𝓿_} nothing  %𝓿ᵒᵖ (just x) ()
    ᵒᵖ²j→j {._%𝓿_} (just x) %𝓿ᵒᵖ nothing  () 
    ᵒᵖ²j→j {._%𝓿_}  (𝟘≤ n)  %𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._%𝓿_}  (𝟘≤ n)  %𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust
    ᵒᵖ²j→j {._%𝓿_}  (≤-1 n) %𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._%𝓿_}  (≤-1 n) %𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust

    ᵒᵖ²j→j {._/𝓿_} nothing  /𝓿ᵒᵖ nothing  ()
    ᵒᵖ²j→j {._/𝓿_} nothing  /𝓿ᵒᵖ (just x) ()
    ᵒᵖ²j→j {._/𝓿_} (just x) /𝓿ᵒᵖ nothing  ()
    ᵒᵖ²j→j {._/𝓿_}  (𝟘≤ n)  /𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._/𝓿_}  (𝟘≤ n)  /𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust
    ᵒᵖ²j→j {._/𝓿_}  (≤-1 n) /𝓿ᵒᵖ (𝟘≤ m)  _ = isJust , isJust
    ᵒᵖ²j→j {._/𝓿_}  (≤-1 n) /𝓿ᵒᵖ (≤-1 m) _ = isJust , isJust
    


  -- Identifier = ℕ
  -- Values = ℤ
  SimpleRep : D-Representation
  SimpleRep = record { SimpleRepresentation  }



