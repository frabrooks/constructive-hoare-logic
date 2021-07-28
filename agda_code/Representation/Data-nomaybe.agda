

-- Abstract out the representation of data (i.e. the Values and Variables)

module Representation.Data where

  open import Relation.Binary.PropositionalEquality
  open import Relation.Binary
  open import Relation.Nullary using ( yes ; no )
  open import Relation.Nullary.Decidable using (False ; True ; isYes ; isNo ; ⌊_⌋ )
  --open import Data.Product using ()
  open import Data.Sum
  open import Data.Maybe
  open import Level
  open import Data.Empty using ( ⊥ )

  open import Data.Integer as Int
  import Data.Nat as Nat  -- renaming (_+_ to _⊕_ ; _*_ to _⊛_ ) using (ℕ; zero; suc; _∸_; _≤_; pred ; _≟_ ; _≤?_)

  open import operators


  record D-Representation : Set₁ where
    field
      Id        : Set
      Val       : Set
      𝔁         : Id
      𝔂         : Id
      𝔃         : Id
      𝔁≢𝔂       : 𝔁 ≡ 𝔂 → ⊥
      𝔁≢𝔃       : 𝔁 ≡ 𝔃 → ⊥
      𝔂≢𝔃       : 𝔂 ≡ 𝔃 → ⊥

      -- Constants
      𝑻         : Val
      𝑭         : Val
      NaN       : Val

      -- More constants (perhaps unnecessary)
      +INF      : Val
      -INF      : Val
      ⓪        : Val
      ➊        : Val
      ➋        : Val
      ➌        : Val

      _?id=_    : Decidable {A = Id} _≡_
      _?val=_   : Decidable {A = Val} _≡_


      -- ᵇᵖ = boolean preserving
      -- i.e. that if x = T/F and y = T/F, then x α y = T/F 
      ᵇᵖbOP²    : (Val → Val → Val) → Set

      _||𝓿_     : Val → Val → Val
      ||𝓿       : ᵇᵖbOP² _||𝓿_
      
      _&&𝓿_     :  Val →   Val →   Val
      &&𝓿       : ᵇᵖbOP² _&&𝓿_

      _==𝓿_     :  Val →   Val →   Val
      ==𝓿       : ᵇᵖbOP² _==𝓿_
      
      ᵇᵖbOP¹    : ( Val →  Val) → Set
      !𝓿        :  Val →   Val
      !𝓿'       : ᵇᵖbOP¹ !𝓿

      -- ACTUALLY, ≤ < etc are ᵇᵖ too. Read as boolean output


      bOP²      : ( Val →  Val →  Val) → Set
      _≤𝓿_      :  Val →   Val →   Val
      ≤𝓿        : bOP² _≤𝓿_
      _<𝓿_      :  Val →   Val →   Val
      <𝓿        : bOP² _<𝓿_
      _≥𝓿_      :  Val →   Val →   Val
      ≥𝓿        : bOP² _≥𝓿_
      _>𝓿_      :  Val →   Val →   Val
      >𝓿        : bOP² _>𝓿_

      zOP²      : ( Val →  Val →  Val) → Set
      _+𝓿_      :  Val →   Val →   Val
      +𝓿        : zOP² _+𝓿_
      _-𝓿_      :  Val →   Val →   Val
      -𝓿        : zOP² _-𝓿_
      _*𝓿_      :  Val →   Val →   Val
      *𝓿        : zOP² _*𝓿_
      _%𝓿_      :  Val →   Val →   Val
      %𝓿        : zOP² _%𝓿_
      _/𝓿_      :  Val →   Val →   Val
      /𝓿        : zOP² _/𝓿_
 
      zOP¹      : ( Val →  Val) →  Set
      ++        :  Val →   Val
      ++'       : zOP¹ ++
      ──        :  Val →   Val
      ──'       : zOP¹ ──

      exp²      : ∀ {∙} →  Val → ᵇᵖbOP² ∙ ⊎ bOP² ∙ ⊎ zOP² ∙ →  Val →  Val
      exp¹      : ∀ {∙} → ᵇᵖbOP¹ ∙ ⊎ zOP¹ ∙ →  Val →  Val

      ᵇᵖ² : ∀ {∙} x y → ( α : ᵇᵖbOP² ∙ )
                → x ≡ 𝑻 ⊎ x ≡ 𝑭
                → y ≡ 𝑻 ⊎ y ≡ 𝑭
                → exp² x (inj₁ α) y ≡ 𝑻 ⊎
                  exp² x (inj₁ α) y ≡ 𝑭

      ᵇᵖ¹ : ∀ {∙} x  → ( α : ᵇᵖbOP¹ ∙ )
                → x ≡ 𝑻 ⊎ x ≡ 𝑭
                → exp¹ (inj₁ α) x ≡ 𝑻 ⊎
                  exp¹ (inj₁ α) x ≡ 𝑭

  
  module SimpleRepresentation where

    open import Agda.Builtin.Unit
    open import Data.Integer.DivMod using (_div_ ; _mod_ )
    
    open ℤ


    Id  = Nat.ℕ
    Val = Int.ℤ

    𝔁 = 0
    𝔂 = 1
    𝔃 = 2


    𝔁≢𝔂 : 𝔁 ≡ 𝔂 → ⊥
    𝔁≢𝔂 ()
    𝔁≢𝔃 : 𝔁 ≡ 𝔃 → ⊥
    𝔁≢𝔃 ()
    𝔂≢𝔃 : 𝔂 ≡ 𝔃 → ⊥
    𝔂≢𝔃 ()

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
    

    _?id=_ : Decidable {A = Id} _≡_ 
    _?id=_ = Nat._≟_

    _?val=_ : Decidable {A = Val} _≡_ 
    _?val=_ = Int._≟_

    private is-neg : ℤ → ℤ
    is-neg (negsuc _) = pos 1
    is-neg (pos    _) = pos 0

    private is-pos : ℤ → ℤ
    is-pos (pos    _) = pos 1
    is-pos (negsuc _) = pos 0


    -- base operations
    private or : Val → Val → Val
    or (pos 0)  (pos 0)  = 𝑭
    or   _        _      = 𝑻
    private and : Val → Val → Val
    and (pos 0)    _      = 𝑭
    and   _      (pos 0)  = 𝑭
    and   _        _      = 𝑻
    private is-zero : ℤ → ℤ
    is-zero (pos 0) = 𝑻
    is-zero  _      = 𝑭
    private eq : Val → Val → Val
    eq a b = is-zero (a - b)
    

    -- Any non-zero value is taken as 𝑻 in
    -- logical statements as per C standard
    _||𝓿_ :  ℤ →  ℤ →  ℤ 
    a ||𝓿 b = or a b
    _&&𝓿_ :  ℤ →  ℤ →  ℤ 
    a &&𝓿 b = and a b
    _==𝓿_ :  ℤ →  ℤ →  ℤ
    a ==𝓿 b = eq a b


    -- 𝔹 operators with ℤ inputs
    _≤𝓿_ :  ℤ →  ℤ →  ℤ 
    a ≤𝓿 b = leq a b
      where
      leq : Val → Val → Val
      leq a b = is-neg ((a - b) - (pos 1))

    _<𝓿_ :  ℤ →  ℤ →  ℤ 
    a <𝓿 b = less  a b 
      where
      less : Val → Val → Val
      less a b = is-neg (a - b)

    _≥𝓿_ :  ℤ →  ℤ →  ℤ 
    a ≥𝓿 b = geq  a b 
      where
      geq : Val → Val → Val
      geq a b = is-pos (a - b)

    _>𝓿_ :  ℤ →  ℤ →  ℤ 
    a >𝓿 b = greater  a b 
      where
      greater : Val → Val → Val
      greater a b = is-pos ((a - b) - (pos 1))


    -- ℤ Operators
    _+𝓿_ :  ℤ →  ℤ →  ℤ
    a +𝓿 b = (_+_)  a b

    _-𝓿_ :  ℤ →  ℤ →  ℤ
    a -𝓿 b = (_-_)  a b

    _*𝓿_ :  ℤ →  ℤ →  ℤ
    a *𝓿 b = (_*_)  a b


    -- Used for divide by zero error
    private 0→nothing : (z : ℤ) →  Maybe ( False ( ∣ z ∣ Nat.≟ 0) )
    0→nothing (pos Nat.zero)         = nothing
    0→nothing (Int.+[1+ n ])         = just tt
    0→nothing (negsuc n)             = just tt

    _/𝓿_ :  ℤ →  ℤ →  ℤ
    a /𝓿 b with 0→nothing b
    ... | nothing  = NaN
    ... | just ≢0  = (a div b) {≢0}

    _%𝓿_ : ℤ → ℤ → ℤ
    a %𝓿 b with 0→nothing b
    ... | nothing = NaN
    ... | just ≢0 = pos ((a mod b) {≢0})

    -- Unary operators
    !𝓿 : ℤ → ℤ
    !𝓿 = (eq (pos 0)) 

    ++ : ℤ → ℤ
    ++ = (_+_ (pos 1))
    
    ── : ℤ → ℤ
    ── = (_-_ (pos 1)) 


    ---------------------------------
    -- Different classes of operations

    -- These definitions are just to
    -- make the following defs terser
    OP² = ℤ → ℤ → ℤ
    OP¹ = ℤ → ℤ

    data zOP²  : OP² → Set where
      +𝓿     : zOP² ( _+𝓿_ )
      -𝓿     : zOP² ( _-𝓿_ ) 
      *𝓿     : zOP² ( _*𝓿_ ) 
      %𝓿     : zOP² ( _%𝓿_ ) 
      /𝓿     : zOP² ( _/𝓿_ ) 
    
    data bOP²  : OP² → Set where
      ≤𝓿     : bOP² ( _≤𝓿_ ) 
      <𝓿     : bOP² ( _<𝓿_ ) 
      ≥𝓿     : bOP² ( _≥𝓿_ ) 
      >𝓿     : bOP² ( _>𝓿_ ) 
      
    data ᵇᵖbOP² : OP² → Set where
      ||𝓿    : ᵇᵖbOP² ( _||𝓿_ ) 
      &&𝓿    : ᵇᵖbOP² ( _&&𝓿_ ) 
      ==𝓿    : ᵇᵖbOP² ( _==𝓿_ ) 

    data ᵇᵖbOP¹  : OP¹ → Set where
      !𝓿'     : ᵇᵖbOP¹ !𝓿

    data zOP¹ : OP¹ → Set where
      ++'     : zOP¹ ++
      ──'     : zOP¹ ── 

    exp² : ∀ {∙} → Val → ᵇᵖbOP² ∙ ⊎ bOP² ∙ ⊎ zOP² ∙ → Val → Val
    exp² {∙} x _ y = ∙ x y
    
    exp¹  : ∀ {∙} → ᵇᵖbOP¹ ∙ ⊎ zOP¹ ∙ → Val → Val
    exp¹ {∙} _ x = ∙ x
    
    ᵇᵖ² : ∀ {∙} x y → ( α : ᵇᵖbOP² ∙ )
                → x ≡ 𝑻 ⊎ x ≡ 𝑭
                → y ≡ 𝑻 ⊎ y ≡ 𝑭
                → exp² {∙} x (inj₁  α) y ≡ 𝑻 ⊎
                  exp² {∙} x (inj₁  α) y ≡ 𝑭
    ᵇᵖ² {.(λ a b → or a b)} .(pos 1) .(pos 1) ||𝓿 (inj₁ refl) (inj₁ refl) = inj₁ refl
    ᵇᵖ² {.(λ a b → or a b)} .(pos 1) .+0 ||𝓿 (inj₁ refl) (inj₂ refl) = inj₁ refl
    ᵇᵖ² {.(λ a b → or a b)} .+0 .(pos 1) ||𝓿 (inj₂ refl) (inj₁ refl) = inj₁ refl
    ᵇᵖ² {.(λ a b → or a b)} .+0 .+0 ||𝓿 (inj₂ refl) (inj₂ refl) = inj₂ refl
    ᵇᵖ² {.(λ a b → and a b)} .(pos 1) .(pos 1) &&𝓿 (inj₁ refl) (inj₁ refl) = inj₁ refl
    ᵇᵖ² {.(λ a b → and a b)} .(pos 1) .+0 &&𝓿 (inj₁ refl) (inj₂ refl) = inj₂ refl
    ᵇᵖ² {.(λ a b → and a b)} .+0 .(pos 1) &&𝓿 (inj₂ refl) (inj₁ refl) = inj₂ refl
    ᵇᵖ² {.(λ a b → and a b)} .+0 .+0 &&𝓿 (inj₂ refl) (inj₂ refl) = inj₂ refl
    ᵇᵖ² {.(λ a b → is-zero (a + - b))} .(pos 1) .(pos 1) ==𝓿 (inj₁ refl) (inj₁ refl) = inj₁ refl
    ᵇᵖ² {.(λ a b → is-zero (a + - b))} .(pos 1) .+0 ==𝓿 (inj₁ refl) (inj₂ refl) = inj₂ refl
    ᵇᵖ² {.(λ a b → is-zero (a + - b))} .+0 .(pos 1) ==𝓿 (inj₂ refl) (inj₁ refl) = inj₂ refl
    ᵇᵖ² {.(λ a b → is-zero (a + - b))} .+0 .+0 ==𝓿 (inj₂ refl) (inj₂ refl) = inj₁ refl

    ᵇᵖ¹ : ∀ {∙} x  → ( α : ᵇᵖbOP¹ ∙ )
                → x ≡ 𝑻 ⊎ x ≡ 𝑭
                → exp¹ (inj₁ α) x ≡ 𝑻 ⊎
                  exp¹ (inj₁ α) x ≡ 𝑭
    ᵇᵖ¹ {.(λ b → is-zero (+0 + - b))} (pos .1) !𝓿' (inj₁ refl) = inj₂ refl
    ᵇᵖ¹ {.(λ b → is-zero (+0 + - b))} (negsuc n) !𝓿' (inj₁ ())
    ᵇᵖ¹ {.(λ b → is-zero (+0 + - b))} (pos .0) !𝓿' (inj₂ refl) = inj₁ refl
    ᵇᵖ¹ {.(λ b → is-zero (+0 + - b))} (negsuc n) !𝓿' (inj₂ ())


  -- Identifier = ℕ
  -- Values = ℤ
  SimpleRep : D-Representation
  SimpleRep = record { SimpleRepresentation  }
  


