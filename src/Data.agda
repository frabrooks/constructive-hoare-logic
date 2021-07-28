
-- Abstract out the representation of data (i.e. the Values and Variables)

open import Misc

module Data where

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
  
  record Value-Implementation : Set₁ where


    field
      Id        : Set
      Val       : Set

      -- Identifiers for use in the
      -- specification of programs
      𝔁         : Id
      𝔂         : Id
      𝔃         : Id
      𝑿         : Id
      𝒀         : Id
      𝒁         : Id
      
      -- Truth constants
      𝑻         : Maybe Val
      𝑭         : Maybe Val

      -- Truth constants should trivially be WFF
      𝑻isWFF    : WFF 𝑻
      𝑭isWFF    : WFF 𝑭

      -- All WFF (well formed expressions) have
      -- an associated truth value
      toTruthValue  : {v : Maybe Val} → WFF v → Bool

      𝑻is𝑻 : (isWFF : WFF 𝑻) → toTruthValue {𝑻} isWFF ≡ true
      𝑭is𝑭 : (isWFF : WFF 𝑭) → toTruthValue {𝑭} isWFF ≡ false

      -- Constant Values
      ⓪        : Val
      ①        : Val
      ②        : Val
      ③        : Val
      ④        : Val
      ⑤        : Val
      ⑥        : Val
      ⑦        : Val
      ⑧        : Val
      ⑨        : Val
 
      -- Truisms -- maybe not needed?
      𝔁≢𝔂       : 𝔁 ≡ 𝔂 → ⊥
      𝔁≢𝔃       : 𝔁 ≡ 𝔃 → ⊥
      𝔂≢𝔃       : 𝔂 ≡ 𝔃 → ⊥

      {-
      is𝑻 : Maybe Val → Set -- (As a proposition)
      is𝑭 : Maybe Val → Set -- (As a proposition)

      -- is𝑻 f implies that f is a WFF and
      -- the truth value of that WFF is 'true'
      𝑻istrue : ∀ v → is𝑻 v → Σ (WFF v)
             (λ w → ((toTruthValue w) ≡ true)) 

      -- is𝑭 f implies that f is a WFF and
      -- the truth value of that WFF is 'false'
      𝑭isfalse : ∀ v → is𝑭 v → Σ (WFF v)
             (λ w → ((toTruthValue w) ≡ false)) 
      
      
      isProposition : Maybe Val → Set
      


      -- An implementation must prove that
      -- isProposition really does mean so i.e.
      -- f is a proposition if it's range/image  ≃ Bool
      propIsProp : (Σ[ f ∈ Maybe Val ] isProposition f) ≃ Bool
      is𝔹→isProposition : ∀ f → is𝑻 f ⊎ is𝑭 f → isProposition f
      -}

  
      _?id=_    : Decidable {A = Id} _≡_
      --_?val=_   : Val → Val → Bool
    
    ⊨ : Maybe Val → Set
    ⊨ x = Σ (WFF x) (T ∘ toTruthValue)

    ⊭ : Maybe Val → Set
    ⊭ x = Σ (WFF x) (T ∘ not ∘ toTruthValue)

  

  record Operation-Implementation (𝔡 : Value-Implementation) : Set₁ where
      
    open Value-Implementation 𝔡

    𝕍 = Maybe Val

    field 
      --------------------------------------------------------
      -- Operations
      
      -- binary 𝔹 ops
      _||𝓿_     : 𝕍 → 𝕍 → 𝕍
      _&&𝓿_     : 𝕍 → 𝕍 → 𝕍
      _==𝓿_     : 𝕍 → 𝕍 → 𝕍
      _≤𝓿_      : 𝕍 → 𝕍 → 𝕍
      _<𝓿_      : 𝕍 → 𝕍 → 𝕍
      _≥𝓿_      : 𝕍 → 𝕍 → 𝕍
      _>𝓿_      : 𝕍 → 𝕍 → 𝕍

      -- binary 𝕍 ops
      _+𝓿_      : 𝕍 → 𝕍 → 𝕍
      _-𝓿_      : 𝕍 → 𝕍 → 𝕍
      _*𝓿_      : 𝕍 → 𝕍 → 𝕍
      _%𝓿_      : 𝕍 → 𝕍 → 𝕍
      _/𝓿_      : 𝕍 → 𝕍 → 𝕍

      -- unary operations
      ¬𝓿        : 𝕍 → 𝕍
      ++𝓿       : 𝕍 → 𝕍
      ─-𝓿       : 𝕍 → 𝕍
      ──𝓿       : 𝕍 → 𝕍
      --------------------------------------------------------
      -- Operation predicates
      
      -- All binary operations
      OP₂ : (𝕍 → 𝕍 → 𝕍) → Set
      ||𝓿₂  : OP₂ (_||𝓿_) 
      &&𝓿₂  : OP₂ (_&&𝓿_)    
      ==𝓿₂  : OP₂ (_==𝓿_) 
      ≤𝓿₂   : OP₂ (_≤𝓿_ )     
      <𝓿₂   : OP₂ (_<𝓿_ )     
      ≥𝓿₂   : OP₂ (_≥𝓿_ )     
      >𝓿₂   : OP₂ (_>𝓿_ )     
      +𝓿₂   : OP₂ (_+𝓿_ )     
      -𝓿₂   : OP₂ (_-𝓿_ )     
      *𝓿₂   : OP₂ (_*𝓿_ )     
      %𝓿₂   : OP₂ (_%𝓿_ )     
      /𝓿₂   : OP₂ (_/𝓿_ )     

      -- All unary operations
      OP₁ : (𝕍 → 𝕍) → Set
      ¬𝓿₁  :  OP₁ (¬𝓿)
      ++𝓿₁ :  OP₁ (++𝓿)
      ─-𝓿₁ :  OP₁ (─-𝓿)
      ──𝓿₁ :  OP₁ (──𝓿)


      wffₒᵤₜ⇒wffᵢₙ : ∀ {∙} x (α : OP₂ ∙ ) y → WFF (∙ x y)
               → WFF x × WFF y 

      -- WFF preserving
      -- (if inputs are WFF then
      --   outputs are WFF)
      -- Don't need OP₁ version
      -- as all unary ops are
      -- WFF preserving
      OP₂:𝑤𝑓𝑓    : ∀ {∙} → OP₂ ∙ → Set
      ||𝓿:𝑤𝑓𝑓    : OP₂:𝑤𝑓𝑓 ||𝓿₂
      &&𝓿:𝑤𝑓𝑓    : OP₂:𝑤𝑓𝑓 &&𝓿₂
      ==𝓿:𝑤𝑓𝑓    : OP₂:𝑤𝑓𝑓 ==𝓿₂
      ≤𝓿:𝑤𝑓𝑓     : OP₂:𝑤𝑓𝑓 ≤𝓿₂
      <𝓿:𝑤𝑓𝑓     : OP₂:𝑤𝑓𝑓 <𝓿₂
      ≥𝓿:𝑤𝑓𝑓     : OP₂:𝑤𝑓𝑓 ≥𝓿₂
      >𝓿:𝑤𝑓𝑓     : OP₂:𝑤𝑓𝑓 >𝓿₂
      +𝓿:𝑤𝑓𝑓     : OP₂:𝑤𝑓𝑓 +𝓿₂
      -𝓿:𝑤𝑓𝑓     : OP₂:𝑤𝑓𝑓 -𝓿₂
      *𝓿:𝑤𝑓𝑓     : OP₂:𝑤𝑓𝑓 *𝓿₂
      
      :𝑤𝑓𝑓₂ : ∀ {∙} {x} {y} {α : OP₂ ∙} → (𝑤𝑓𝑓 : OP₂:𝑤𝑓𝑓 α)
              → WFF x → WFF y → WFF (∙ x y)

      :𝑤𝑓𝑓₁ : ∀ {∙} {x} (α : OP₁ ∙) → WFF x → WFF (∙ x)

      DeMorgan₁ : ∀ x y → ¬𝓿 (x ||𝓿 y) ≡ (¬𝓿 x) &&𝓿 (¬𝓿 y)

      DeMorgan₂ : ∀ x y → ¬𝓿 (x &&𝓿 y) ≡ (¬𝓿 x) ||𝓿 (¬𝓿 y)
      
      ConjunctionElim₁ : ∀ x y → ⊨ (x &&𝓿 y) → ⊨ x
      ConjunctionElim₂ : ∀ x y → ⊨ (x &&𝓿 y) → ⊨ y

      ConjunctionIntro : ∀ x y → ⊨ x → ⊨ y → ⊨ (x &&𝓿 y)

      NegationIntro : ∀ v → ⊭ v → ⊨ (¬𝓿 v)
      NegationElim  : ∀ v → ⊭ (¬𝓿 v) → ⊨ v


  record Data-Implementation : Set₁ where
    field
      𝔙 : Value-Implementation
      𝒪 : Operation-Implementation 𝔙
      
    open Value-Implementation 𝔙 public
    open Operation-Implementation 𝒪 public



