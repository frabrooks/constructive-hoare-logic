

-- Lib Imports
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

-- Project Imports
open import Misc

module Data-Interface where

  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  -- Abstract out the representation of data and expression language (i.e. the
  -- Values and Variables and operations upon them)


  -- ════════════════════════════════════════════════════════════════════════════
  record Value-Implementation : Set₁ where
  
    field
      Id        : Set
      Val       : Set

    -- Type synonym for values. Not all expressions/operations in a expression
    -- language implementation need to be well-defined (i.e. div by zero error)
    𝕍 = Maybe Val
    WFF = Is-just

    field
      -- Identifiers for use in the formalisation of programs. The fact that
      -- they are fixed here and not generated as needed is a limitation of 
      -- the current system.
      𝒙         : Id
      𝒚         : Id
      𝒛         : Id

      -- Truth constants
      𝑻         : 𝕍
      𝑭         : 𝕍

      -- Truth constants should trivially be WFF
      𝑻isWFF    : WFF 𝑻
      𝑭isWFF    : WFF 𝑭

      -- All WFF (well-formed expressions) have an associated truth value
      toTruthValue  : {v : 𝕍} → WFF v → Bool

      𝑻is𝑻 : (isWFF : WFF 𝑻) → toTruthValue {𝑻} isWFF ≡ true
      𝑭is𝑭 : (isWFF : WFF 𝑭) → toTruthValue {𝑭} isWFF ≡ false

      -- Constant Values
      ⓪        : Val
      ①        : Val
      ②        : Val

      -- Vars are distinct. Ideally wouldn't need this and would have some way
      -- of generating a new variable that is guaranteed to be distinct
      𝒙≢𝒛       : 𝒙 ≡ 𝒛 → ⊥
      𝒚≢𝒛       : 𝒚 ≡ 𝒛 → ⊥

      -- Identifiers can be decidably identified (it's in the name afterall '⌣')
      _?id=_    : Decidable {A = Id} _≡_

    
    ⊢ : 𝕍 → Set
    ⊢ x = Σ (WFF x) (T ∘ toTruthValue)

    ⊬ : 𝕍 → Set
    ⊬ x = Σ (WFF x) (T ∘ not ∘ toTruthValue)

  
  -- ════════════════════════════════════════════════════════════════════════════
  record Operation-Implementation (𝔡 : Value-Implementation) : Set₁ where
      
    open Value-Implementation 𝔡

    ---------------------------------------------------------------------------
    field -- Operations
    
      -- Binary ops that semantically have type Bool
      _||𝓿_     : 𝕍 → 𝕍 → 𝕍
      _&&𝓿_     : 𝕍 → 𝕍 → 𝕍
      _==𝓿_     : 𝕍 → 𝕍 → 𝕍
      _≤𝓿_      : 𝕍 → 𝕍 → 𝕍
      _<𝓿_      : 𝕍 → 𝕍 → 𝕍
      _≥𝓿_      : 𝕍 → 𝕍 → 𝕍
      _>𝓿_      : 𝕍 → 𝕍 → 𝕍

      -- Binary ops that semantically have type Integer
      _+𝓿_      : 𝕍 → 𝕍 → 𝕍
      _-𝓿_      : 𝕍 → 𝕍 → 𝕍
      _*𝓿_      : 𝕍 → 𝕍 → 𝕍
      _%𝓿_      : 𝕍 → 𝕍 → 𝕍
      _/𝓿_      : 𝕍 → 𝕍 → 𝕍

      -- Unary operations
      ¬𝓿        : 𝕍 → 𝕍 -- Negate truth value
      ++𝓿       : 𝕍 → 𝕍 -- Increment
      ─-𝓿       : 𝕍 → 𝕍 -- Decrement
      ──𝓿       : 𝕍 → 𝕍 -- (* - 1)
    
    ---------------------------------------------------------------------------
    field -- Operation Predicates
      
      -- All binary operations. Use this type to add logical rules that will
      -- pertain to all binary predicates.
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

      -- All unary operations. Use this type to add logical rules that will
      -- pertain to all binary predicates.
      OP₁ : (𝕍 → 𝕍) → Set
      ¬𝓿₁  :  OP₁ (¬𝓿)
      ++𝓿₁ :  OP₁ (++𝓿)
      ─-𝓿₁ :  OP₁ (─-𝓿)
      ──𝓿₁ :  OP₁ (──𝓿)


      wffₒᵤₜ⇒wffᵢₙ : ∀ {∙} x (α : OP₂ ∙ ) y → WFF (∙ x y)
               → WFF x × WFF y 

      -- WFF preserving (if inputs are WFF then outputs are WFF)
      -- Don't need OP₁ version as all unary ops are WFF preserving
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


    ---------------------------------------------------------------------------
    field -- Expression Manipulations


      DeMorgan₁ : ∀ x y → ¬𝓿 (x ||𝓿 y) ≡ (¬𝓿 x) &&𝓿 (¬𝓿 y)

      DeMorgan₂ : ∀ x y → ¬𝓿 (x &&𝓿 y) ≡ (¬𝓿 x) ||𝓿 (¬𝓿 y)
      
      ConjunctionElim₁ : ∀ x y → ⊢ (x &&𝓿 y) → ⊢ x
      ConjunctionElim₂ : ∀ x y → ⊢ (x &&𝓿 y) → ⊢ y

      ConjunctionIntro : ∀ x y → ⊢ x → ⊢ y → ⊢ (x &&𝓿 y)

      ConjunctionComm  : ∀ x y → (x &&𝓿 y) ≡ (y &&𝓿 x)

      NegationIntro : ∀ v → ⊬ v → ⊢ (¬𝓿 v)
      NegationElim  : ∀ v → ⊬ (¬𝓿 v) → ⊢ v


  record Data-Implementation : Set₁ where
    field
      𝔙 : Value-Implementation
      𝒪 : Operation-Implementation 𝔙
      
    open Value-Implementation 𝔙 public
    open Operation-Implementation 𝒪 public



