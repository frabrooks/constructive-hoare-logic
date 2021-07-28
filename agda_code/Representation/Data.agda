

-- Abstract out the representation of data (i.e. the Values and Variables)



module Representation.Data where

  open import Relation.Binary.PropositionalEquality
  open import Relation.Binary
  open import Relation.Nullary using ( yes ; no )
  open import Relation.Nullary.Decidable using (False ; True ; isYes ; isNo ; ⌊_⌋ )
  --open import Data.Product using ()
  open import Data.Maybe
  open import Level
  open import Data.Empty using ( ⊥ )

  import Data.Integer as Int -- using (ℤ ; pose ; negsuc )
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
      ⓪        : Val
      ➊        : Val
      ➋        : Val
      ➌        : Val
      𝑻         : Val
      𝑭         : Val
      _?id=_    : Decidable {A = Id} _≡_
      _?val=_   : Decidable {A = Val} _≡_
      _||𝓿_      : Maybe Val → Maybe Val → Maybe Val
      _&&𝓿_      : Maybe Val → Maybe Val → Maybe Val
      _==𝓿_      : Maybe Val → Maybe Val → Maybe Val
      _≤𝓿_       : Maybe Val → Maybe Val → Maybe Val
      _<𝓿_       : Maybe Val → Maybe Val → Maybe Val
      _≥𝓿_       : Maybe Val → Maybe Val → Maybe Val
      _>𝓿_       : Maybe Val → Maybe Val → Maybe Val
      _+𝓿_       : Maybe Val → Maybe Val → Maybe Val
      _-𝓿_       : Maybe Val → Maybe Val → Maybe Val
      _*𝓿_       : Maybe Val → Maybe Val → Maybe Val
      _%𝓿_       : Maybe Val → Maybe Val → Maybe Val
      _/𝓿_       : Maybe Val → Maybe Val → Maybe Val
      !𝓿         : Maybe Val → Maybe Val



  module SimpleRepresentation where

    open import Agda.Builtin.Unit
    open import Data.Integer.DivMod using (_div_ ; _mod_ )
    
    open Int 
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
    

    private 0→nothing : (z : ℤ) →  Maybe ( False ( ∣ z ∣ Nat.≟ 0) )
    0→nothing (pos Nat.zero)         = nothing
    0→nothing (Int.+[1+ n ])         = just tt
    0→nothing (negsuc n)             = just tt
    

    _||𝓿_ : Maybe ℤ → Maybe ℤ → Maybe ℤ 
    a ||𝓿 b = or <$> a <*> b
      where
      or : Val → Val → Val
      or (pos 0)  (pos 0)  = pos 0
      or (pos n)    _      = pos 1
      or _        (pos n)  = pos 1
      or _ _               = pos 0

    _&&𝓿_ : Maybe ℤ → Maybe ℤ → Maybe ℤ 
    a &&𝓿 b = and <$> a <*> b
      where
      and : Val → Val → Val
      and (pos 0)    _      = pos 0
      and   _      (pos 0)  = pos 0
      and (pos _)  (pos _)  = pos 1
      and   _        _      = pos 0

    _==𝓿_ : Maybe ℤ → Maybe ℤ → Maybe ℤ
    a ==𝓿 b = eq <$> a <*> b
      where
      is-zero : ℤ → ℤ
      is-zero (pos 0) = pos 1
      is-zero  _      = pos 0
      eq : Val → Val → Val
      eq a b = is-zero (a - b)

    _≤𝓿_ : Maybe ℤ → Maybe ℤ → Maybe ℤ 
    a ≤𝓿 b = leq <$> a <*> b
      where
      leq : Val → Val → Val
      leq a b = is-neg ((a - b) - (pos 1))

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
      greater a b = is-pos ((a - b) - (pos 1))

    _+𝓿_ : Maybe ℤ → Maybe ℤ → Maybe ℤ
    a +𝓿 b = (_+_) <$> a <*> b

    _-𝓿_ : Maybe ℤ → Maybe ℤ → Maybe ℤ
    a -𝓿 b = (_-_) <$> a <*> b

    _*𝓿_ : Maybe ℤ → Maybe ℤ → Maybe ℤ
    a *𝓿 b = (_*_) <$> a <*> b

    _/𝓿_ : Maybe ℤ → Maybe ℤ → Maybe ℤ
    a /𝓿 b = maybeDiv b <*> a
      where
      maybeDiv : Maybe ℤ → Maybe (ℤ → ℤ)
      maybeDiv nothing = nothing
      maybeDiv (just divisor) = (λ not0 → (λ numerator → (numerator div divisor) {not0} )) <$> ( 0→nothing divisor)

    _%𝓿_ : Maybe ℤ → Maybe ℤ → Maybe ℤ
    a %𝓿 b = maybeMod b <*> a
      where
      maybeMod : Maybe ℤ → Maybe (ℤ → ℤ)
      maybeMod nothing = nothing
      maybeMod (just divisor) = (λ not0 → (λ numerator → pos ((numerator mod divisor) {not0} ))) <$> ( 0→nothing divisor)

    !𝓿 : Maybe ℤ → Maybe ℤ
    !𝓿 x = x >>= aux
      where 
      aux : ℤ → Maybe ℤ
      aux (pos Nat.zero) = just (pos 1)
      aux Int.+[1+ Nat.zero ] = just (pos 0)
      aux Int.+[1+ Nat.suc n ] = nothing
      aux (negsuc n) = nothing


  -- Identifier = ℕ
  -- Values = ℤ
  SimpleRep : D-Representation
  SimpleRep = record { SimpleRepresentation  }



