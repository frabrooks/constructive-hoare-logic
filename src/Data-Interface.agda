

-- Lib Imports
open import Relation.Binary.PropositionalEquality using ( _≡_ )
open import Relation.Binary using (Decidable)
open import Data.Maybe.Relation.Unary.Any using (Any)
open import Data.Product as Pr using ( Σ ; Σ-syntax ; _×_ ; _,_ )
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Maybe
open import Data.Unit using ( ⊤ ; tt)
open import Data.Empty using ( ⊥ )
open import Function using ( _∘_ )
open import Data.Bool.Base using (Bool ; T ; not ; true ; false)
open import Data.Integer using ( ℤ ; _≤_ )

-- Local Imports
open import Misc using ( any ; _≃_ )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Data-Interface where

  -- Abstract out the representation of data and expression language (i.e. the
  -- Values and Variables and operations upon them). This interface exists for
  -- two main reasons:
  --
  --     1) To seperate the concerns of reasoning with Hoare-Logic and
  --        of proving trivial lemmas about the mathematical objects
  --        that appear within the expression/assertion language. e.g.
  --        Conjunction Elimination for our boolean && operator. We
  --        want to be able to formalise our reasoning in Hoare-Logic
  --        without necessarily having to formalise obvious results
  --        in our embedded expression/assertion language such as
  --        `(𝑥 ∧ 𝑦) ⇒ 𝑦' or `(𝑧 == 0 ∧ 𝑥 == 𝑦 * 𝑧) ⇒ 𝑥 == 0'.
  --
  --     2) To abstract away the differences in expression language
  --        implementation that may affect execution, and therefore 
  --        should be considered while constructing a proof, viz
  --        finite vs. infinite arithmetic, and in the case of finite
  --        arithmetic the choice of overflow strategy. Here, 
  --        `considered while constructing a proof', really just means
  --        that if the correctness of a program depends on a certain
  --        overflow strategy - say modulo - this should be made clear
  --        in the proof/formalisation and this interface provides a way
  --        to do so while simultaneously preventing - assuming the
  --        interface is being instantiated somewhere - a heedless
  --        application of an expression lemma that depends on a
  --        particular implementation detail. In practice however, most
  --        programs that this library would likely be used to reason
  --        about - if designed by a sensible programmer - will avoid
  --        dependence on say, a certain overflow strategy, and therefore
  --        this second justification can largely be ignored.
  --
  -- n.b. That this entire interface has been implemented/proven in all its
  --      verbosity in 𝐷𝑎𝑡𝑎-𝐼𝑛𝑓𝑖𝑛𝑖𝑡𝑒-𝐴𝑟𝑖𝑡ℎ𝑚𝑒𝑡𝑖𝑐.𝑎𝑔𝑑𝑎 in ./src/Representations/


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

      -- Vars are distinct. Ideally wouldn't need this and would have some way
      -- of generating a new variable that is guaranteed to be distinct
      𝒙≢𝒛       : 𝒙 ≡ 𝒛 → ⊥
      𝒚≢𝒛       : 𝒚 ≡ 𝒛 → ⊥

      -- Identifiers can be decidably identified (it's in the name afterall '⌣')
      _?id=_    : Decidable {A = Id} _≡_

      -- Truth constants
      𝑻         : Val
      𝑭         : Val
      -- Integer constant Values
      ⓪        : Val
      ①        : Val
      ②        : Val

      -- TODO : Change to Val → Bool
      -- All WFF (well-formed expressions) have an associated Boolean value
      toTruthValue : {v : 𝕍} → WFF v → Bool

      -- All WFF (i.e. all Vals) have an associated Integer value
      toIntValue : Val → ℤ

      𝑻is𝑻 : toTruthValue {just 𝑻} (any tt) ≡ true
      𝑭is𝑭 : toTruthValue {just 𝑭} (any tt) ≡ false

    
    ⊢ : 𝕍 → Set
    ⊢ x = Σ (WFF x) (T ∘ toTruthValue)

    ⊬ : 𝕍 → Set
    ⊬ x = Σ (WFF x) (T ∘ not ∘ toTruthValue)

    Int∶ : Val → ℤ
    Int∶ = toIntValue


  -- ════════════════════════════════════════════════════════════════════════════
  record Operation-Implementation (𝔡 : Value-Implementation) : Set₁ where
      
    open Value-Implementation 𝔡

    ---------------------------------------------------------------------------
    field -- Operations
    
      -- Binary ops that semantically have type Bool
      _||ᵥ_     : 𝕍 → 𝕍 → 𝕍
      _&&ᵥ_     : 𝕍 → 𝕍 → 𝕍
      _==ᵥ_     : 𝕍 → 𝕍 → 𝕍
      _≤ᵥ_      : 𝕍 → 𝕍 → 𝕍
      _<ᵥ_      : 𝕍 → 𝕍 → 𝕍
      _≥ᵥ_      : 𝕍 → 𝕍 → 𝕍
      _>ᵥ_      : 𝕍 → 𝕍 → 𝕍

      -- Binary ops that semantically have type Integer
      _+ᵥ_      : 𝕍 → 𝕍 → 𝕍
      _-ᵥ_      : 𝕍 → 𝕍 → 𝕍
      _*ᵥ_      : 𝕍 → 𝕍 → 𝕍
      _%ᵥ_      : 𝕍 → 𝕍 → 𝕍
      _/ᵥ_      : 𝕍 → 𝕍 → 𝕍

      -- Unary operations
      ¬ᵥ        : 𝕍 → 𝕍 -- Negate truth value
      ++ᵥ       : 𝕍 → 𝕍 -- Increment
      ─-ᵥ       : 𝕍 → 𝕍 -- Decrement
      ──ᵥ       : 𝕍 → 𝕍 -- (* - 1)   

    _̇ : ∀ {ℓ} {A : Set ℓ} → (x : A) → Maybe A
    _̇ = just
    infix 50 _̇
    ---------------------------------------------------------------------------
    field -- Expression Lemmas

      -------------------------------------------------------------------------
      -- Table 1 taken straight from [1]
      -------------------------------------------------------------------------
      A1    : ∀ x y → x +ᵥ y ≡ y +ᵥ x                -- addition is commutative
      A2    : ∀ x y → x *ᵥ y ≡ y *ᵥ x          -- multiplication is commutative
      A3    : ∀ x y z → x +ᵥ (y +ᵥ z) ≡ (x +ᵥ y) +ᵥ z     -- associativity of +
      A4    : ∀ x y z → x *ᵥ (y *ᵥ z) ≡ (x *ᵥ y) *ᵥ z     -- associativity of *
      A5    : ∀ x y z → x *ᵥ (y +ᵥ z) ≡ (x *ᵥ y) +ᵥ (x *ᵥ z)   -- * distributes
      A6    : ∀ x y → ⊢ (y ≤ᵥ x) → ⊢ ((x -ᵥ y) +ᵥ y) ≃ ⊢ x      -- + cancels -
      
      A7    : ∀ x → ⊢ (x +ᵥ  ⓪ ̇) ≃ ⊢ x
      A8    : ∀ x → (x ̇ *ᵥ ⓪ ̇) ≡ ⓪ ̇
      A9    : ∀ x → ⊢ (x *ᵥ  ① ̇) ≃ ⊢ x
      -------------------------------------------------------------------------

      -- An implementation's arithmetic strategey (whether the operations are
      -- operating on a bounded or unbounded set of integers - i.e. true
      -- Integers or 32/64-bit-words) must be identified by implementing one of
      -- the following, mutually exclusive axioms
      ARITHMETIC-STRATEGY :

             -- There does 𝑛𝑜𝑡 exist a Value s.t. all other Values are lesser
             ((Σ[ x ∈ Val ] ((y : Val) → (Int∶ y) ≤ (Int∶ x))) → ⊥) -- Infinite 
             -- Or, there does exist such a max value.
           ⊎ (Σ[ max ∈ Val ] ((x : Val) → (Int∶ x) ≤ (Int∶ max)))     -- Finite


      -- In the case that the ARITHMETIC-STRATEGY is finite, there are different
      -- ways in which the value of max + 1 can be handled
      OVERFLOW-STRATEGY :  ( max : Val ) → ((x : Val) → (Int∶ x) ≤ (Int∶ max))
                           →                            
                           ( max ̇ +ᵥ ① ̇ ) ≡ nothing    -- Strict Interpretation
                           ⊎
                           ( max ̇ +ᵥ ① ̇ ) ≡ max ̇               -- Firm Boundary
                           ⊎
                           ( max ̇ +ᵥ ① ̇ ) ≡ ⓪ ̇            -- Modulo Arithmetic


      DeMorgan₁ : ∀ x y → ¬ᵥ (x ||ᵥ y) ≡ (¬ᵥ x) &&ᵥ (¬ᵥ y)

      DeMorgan₂ : ∀ x y → ¬ᵥ (x &&ᵥ y) ≡ (¬ᵥ x) ||ᵥ (¬ᵥ y)
      
      ConjunctionElim₁ : ∀ x y → ⊢ (x &&ᵥ y) → ⊢ x
      ConjunctionElim₂ : ∀ x y → ⊢ (x &&ᵥ y) → ⊢ y

      ConjunctionIntro : ∀ x y → ⊢ x → ⊢ y → ⊢ (x &&ᵥ y)

      ConjunctionComm  : ∀ x y → (x &&ᵥ y) ≡ (y &&ᵥ x)

      NegationIntro : ∀ v → ⊬ v → ⊢ (¬ᵥ v)
      NegationElim  : ∀ v → ⊬ (¬ᵥ v) → ⊢ v

  -- ════════════════════════════════════════════════════════════════════════════
  
  record Data-Implementation : Set₁ where
    field
      𝔙 : Value-Implementation
      𝒪 : Operation-Implementation 𝔙
      
    open Value-Implementation 𝔙 public
    open Operation-Implementation 𝒪 public



  FINITE-ARITHMETIC : Data-Implementation → Set
  FINITE-ARITHMETIC 𝔡 with Data-Implementation.ARITHMETIC-STRATEGY 𝔡
  ... | inj₁ ∞ = ⊥
  ... | inj₂ _ = ⊤


  ∞-ARITHMETIC : Data-Implementation → Set
  ∞-ARITHMETIC 𝔡 with Data-Implementation.ARITHMETIC-STRATEGY 𝔡
  ... | inj₁ ∞ = ⊤
  ... | inj₂ _ = ⊥


  STRICT-OVERFLOW : (𝔡 : Data-Implementation) → FINITE-ARITHMETIC 𝔡 → Set
  STRICT-OVERFLOW 𝔡 _ with Data-Implementation.ARITHMETIC-STRATEGY 𝔡
  ... | inj₂ (max , μ) with Data-Implementation.OVERFLOW-STRATEGY 𝔡 max μ
  ... | inj₁ _ = ⊤
  ... | inj₂ (inj₁ _) = ⊥
  ... | inj₂ (inj₂ _) = ⊥


  FIRM-OVERFLOW : (𝔡 : Data-Implementation) → FINITE-ARITHMETIC 𝔡 → Set
  FIRM-OVERFLOW 𝔡 _ with Data-Implementation.ARITHMETIC-STRATEGY 𝔡
  ... | inj₂ (max , μ) with Data-Implementation.OVERFLOW-STRATEGY 𝔡 max μ
  ... | inj₁ _ = ⊥
  ... | inj₂ (inj₁ _) = ⊤
  ... | inj₂ (inj₂ _) = ⊥


  MODULO-OVERFLOW : (𝔡 : Data-Implementation) → FINITE-ARITHMETIC 𝔡 → Set
  MODULO-OVERFLOW 𝔡 _ with Data-Implementation.ARITHMETIC-STRATEGY 𝔡
  ... | inj₂ (max , μ) with Data-Implementation.OVERFLOW-STRATEGY 𝔡 max μ
  ... | inj₁ _ = ⊥
  ... | inj₂ (inj₁ _) = ⊥
  ... | inj₂ (inj₂ _) = ⊤



  -- Refs
     -- [1] - C. A. R. Hoare, An Axiomatic Basis for Computer Programming 1969
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
