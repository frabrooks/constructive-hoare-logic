

-- Lib imports
open import Data.Maybe using (Maybe ; just ; nothing ; Is-just ; to-witness ; maybe )
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl ; sym ; inspect ; Reveal_·_is_ ; cong ; subst ; [_] )
open import Data.Maybe.Relation.Unary.Any
open import Data.Product using (Σ ; Σ-syntax ; _×_  ; _,_  ; proj₁ ; proj₂ )
open import Data.Bool using (true ; false ; T ; not )
open import Relation.Nullary using ( ¬_  ; yes ; no )
open import Data.Empty using ( ⊥ ; ⊥-elim )
open import Data.Nat using (ℕ ; suc ; zero ; _≤″_  ) renaming (_+_ to _+ᴺ_ ; less-than-or-equal to ≤with )
open _≤″_
open import Data.Nat.Properties using ( +-comm ; +-suc )
open import Agda.Builtin.Nat using ( _-_ )
open import Function using ( _∘_ )
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using ( ⊤ ; tt )

open import Data using (Data-Implementation)
open import State using (State-Implementation)
open import Misc


module Hoare-Logic.Axioms
  (𝔡 : Data-Implementation )
  (𝔖 : State-Implementation 𝔡 ) where

  open Data-Implementation 𝔡
  open State-Implementation 𝔖

  open import Language.Expressions 𝔡 𝔖
  open import Language.Assertions  𝔡 𝔖

  open import Language.Mini-Imp 𝔡 𝔖
  open import Evaluation.Evaluation 𝔡 𝔖
  open import Evaluation.Termination 𝔡 𝔖

  open import Hoare-Logic.Semantics 𝔡 𝔖

-- ═══════════════════════════════════════════════════════════════════════════════ --
-- Axioms / Rules

  D0-Axiom-of-Assignment : ∀ i e P

  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ --
       → ⟪ (sub e i P) ⟫  ( i := e ; ) ⟪ P ⟫


  D1-Rule-of-Consequence-post : ∀ {P} {Q} {R} {S}

      → ⟪ P ⟫ Q ⟪ R ⟫ → R ⇒ S 
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━ --                    
          → ⟪ P ⟫ Q ⟪ S ⟫


  D1-Rule-of-Consequence-pre : ∀ {P} {Q} {R} {S}

      → ⟪ P ⟫ Q ⟪ R ⟫ → S ⇒ P
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━ --                                           
           → ⟪ S ⟫ Q ⟪ R ⟫


  D2-Rule-of-Composition : ∀ {P} {R₁} {R} {Q₁} {Q₂}

        → ⟪ P ⟫ Q₁ ⟪ R₁ ⟫ → ⟪ R₁ ⟫ Q₂ ⟪ R ⟫
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ --
            → ⟪ P ⟫ Q₁ 𝔱𝔥𝔢𝔫 Q₂ ⟪ R ⟫


  D3-While-Rule : ∀ {P} {B} {C}

                 → ⟪ P ∧ B ⟫ C ⟪ P ⟫
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ --
        → ⟪ P ⟫ 𝔴𝔥𝔦𝔩𝔢 B 𝒹ℴ C ; ⟪ (𝑛𝑜𝑡 B) ∧ P ⟫


  D4-Conditional-Rule : ∀ {A} {B} {C} {P} {Q}

      → ⟪ C ∧ P ⟫ A ⟪ Q ⟫ → ⟪ (𝑛𝑜𝑡 C) ∧ P ⟫ B ⟪ Q ⟫
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ --
              → ⟪ P ⟫  𝔦𝔣 C 𝔱𝔥𝔢𝔫 A 𝔢𝔩𝔰𝔢 B ; ⟪ Q ⟫
              

-- ⇩ Implementations / Proofs
-- ═══════════════════════════════════════════════════════════════════════════════ --

  D0-Axiom-of-Assignment i e P s (𝑤𝑓𝑓 , ⊢sub) (suc n , p)
      with evalExp e s | inspect (evalExp e) s
  ... | (just v) | [ eq ] rewrite Is-just-just p = go
      where

      evalExp-Var : (v : Id) (s : S) → evalExp (term (Var v)) s ≡ getVarVal v s
      evalExp-Var v s = refl

      evalExp-updState : (P e : Exp) (i : Id) (v : Val) (s : S)
                         → evalExp e s ≡ just v
                         → evalExp P (updateState i v s) ≡ evalExp (sub e i P) s
      evalExp-updState (op₂ P x P₁) e i v s comp
        rewrite evalExp-updState P e i v s comp
              | evalExp-updState P₁ e i v s comp = refl
      evalExp-updState (op₁ x P) e i v s comp
        rewrite evalExp-updState P e i v s comp = refl
      evalExp-updState (term (Const x)) e i v s comp = refl
      evalExp-updState (term 𝒕) e i v s comp = refl
      evalExp-updState (term 𝒇) e i v s comp = refl
      evalExp-updState (term (Var x)) e i v s comp with i ?id= x
      ... | yes q rewrite evalExp-Var x (updateState i v s)
                          | q | updateGet x v s = sym comp
      ... | no  q rewrite evalExp-Var x (updateState i v s)
                          | ignoreTop i x v q s = refl

      go : Σ⊢ (updateState i v s) P
      go rewrite evalExp-updState P e i v s eq = 𝑤𝑓𝑓 , ⊢sub


-- ═══════════════════════════════════════════════════════════════════════════════ --

  D1-Rule-of-Consequence-post x x₁ s x₂ ϕ = x₁ (to-witness (proj₂ ϕ)) (x s x₂ ϕ)

  D1-Rule-of-Consequence-pre {P} {Q} {R} {S} x x₁ s x₂ ϕ = x s (x₁ s x₂) ϕ


-- ═══════════════════════════════════════════════════════════════════════════════ --

  D2-Rule-of-Composition {_} {_} {_} {Q₁} {Q₂} PQR₁ PQR₂ s ⊢P (ℱ , t₁₂)
    with ⌊ᵗ⌋-split ℱ s Q₁ Q₂ t₁₂
  ... | ϕ rewrite sym (Δ ϕ)
      = let ⊢R₁ = PQR₁ s ⊢P (ℱ , (Lᵗ ϕ))
        in  PQR₂ (″ (Lᵗ ϕ)) ⊢R₁ ((ℱ' ϕ) , (Rᵗ ϕ))


-- ═══════════════════════════════════════════════════════════════════════════════ --

  D3-While-Rule {P} {B} {C} PBCP s Σ⊢P (suc ℱ , ⌊ᵗCᵗ⌋) = go (suc ℱ) Σ⊢P ⌊ᵗCᵗ⌋ 
      where
      ------------------------------------------------------------
      -- Using mutually recursive functions go and go-true      
      go : ∀ {s} ℱ → Σ⊢ s P → (⌊ᵗCᵗ⌋ : ⌊ᵗ ℱ ⸴ (𝔴𝔥𝔦𝔩𝔢 B 𝒹ℴ C ;) ⸴ s ᵗ⌋)
           → Σ⊢ (″ ⌊ᵗCᵗ⌋) (op₂ (op₁ ¬ₒ B) &&ₒ P )
      -- ℱ needs to be an argument by itself outside the Sigma type
      -- so we can recurse on it as Agda can't see it always decrements
      -- with each call if it is inside the product.
      ---------------------------------------------------------------
      -- case where B is true
      go-true : ∀ {s} {ℱ} {v} → Σ⊢ s P → (evalExp B s ≡ just v)
              → (toTruthValue {just v} (just tt) ≡ true)
              → (⌊ᵗCᵗ⌋ : ⌊ᵗ ℱ ⸴ (C 𝔱𝔥𝔢𝔫 𝔴𝔥𝔦𝔩𝔢 B 𝒹ℴ C ;) ⸴ s ᵗ⌋)
              → Σ⊢ (to-witness ⌊ᵗCᵗ⌋) (op₂ (op₁ ¬ₒ B) &&ₒ P)
      go-true {s} {ℱ} Σ⊢P p₁ p₂ ⌊ᵗCᵗ⌋
          with ⌊ᵗ⌋-split ℱ s C (𝔴𝔥𝔦𝔩𝔢 B 𝒹ℴ C ;) ⌊ᵗCᵗ⌋
      ... | record { Lᵗ = Lᵗ ; ℱ' = ℱ' ; Rᵗ = Rᵗ ; lt = lt ; Δ = Δ } = Λ
         where
         Σ⊢B : Σ⊢ s B
         Σ⊢B rewrite p₁ = (just tt , subst T (sym p₂) tt)
         Σ⊢P&B : Σ⊢ s (op₂ P &&ₒ B)
         Σ⊢P&B = ConjunctionIntro _ _ Σ⊢P Σ⊢B  
         Σ⊢P' : Σ⊢ (″ Lᵗ) P
         Σ⊢P' = PBCP s Σ⊢P&B (ℱ , Lᵗ)
         
         -- Proof of termination of rhs of split with ℱ'
         Rᵗ+ : ⌊ᵗ ℱ' +ᴺ (k lt) ⸴ (𝔴𝔥𝔦𝔩𝔢 B 𝒹ℴ C ;) ⸴ (″ Lᵗ) ᵗ⌋
         Rᵗ+ = addFuel' {𝔴𝔥𝔦𝔩𝔢 B 𝒹ℴ C ;} ℱ' (k lt) Rᵗ
         -- ℱ' with (ℱ' ≤ ℱ) implies termination with ℱ fuel
         Rᵗℱ : ⌊ᵗ ℱ ⸴ (𝔴𝔥𝔦𝔩𝔢 B 𝒹ℴ C ;) ⸴ (″ Lᵗ) ᵗ⌋
         Rᵗℱ = let 𝐶 = (𝔴𝔥𝔦𝔩𝔢 B 𝒹ℴ C ;) in subst
               (λ ℱ → ⌊ᵗ ℱ ⸴ 𝐶 ⸴ (″ Lᵗ) ᵗ⌋) (proof lt) Rᵗ+      
         -- This new proof of termination Rᵗℱ has same output
         isDet : ″ Rᵗℱ ≡ ″ Rᵗ
         isDet = EvaluationIsDeterministic (𝔴𝔥𝔦𝔩𝔢 B 𝒹ℴ C ;)
                 (ℱ , Rᵗℱ) (ℱ' , Rᵗ) refl refl                 
         -- and said output is identical to the original output
         Δ' : ″ Rᵗℱ ≡ ″ ⌊ᵗCᵗ⌋
         Δ' rewrite isDet = Δ         
         -- which we can now use in a recursive call: (suc ℱ) ⇒ ℱ
         GO  : Σ⊢ (″ Rᵗℱ) (op₂ (op₁ ¬ₒ B) &&ₒ P)
         GO  = go {″ Lᵗ} ℱ Σ⊢P' Rᵗℱ
         
         -- and finally get the type we need via substitution with Δ'
         Λ : Σ⊢ (″ ⌊ᵗCᵗ⌋) (op₂ (op₁ ¬ₒ B) &&ₒ P) 
         Λ = subst (λ s → Σ⊢ s (op₂ (op₁ ¬ₒ B) &&ₒ P)) Δ' GO
      ---------------------------------------------------------------
      -- case where B is false
      go-false : ∀ {s} {v} → Σ⊢ s P → (evalExp B s ≡ just v)
                 → (toTruthValue {just v} (just tt) ≡ false)
                 → Σ⊢ s (op₂ (op₁ ¬ₒ B) &&ₒ P)            
      go-false {s} {v} Σ⊢P p₁ p₂ = ConjunctionIntro _ _ Σ⊢¬B Σ⊢P
        where
        ⊭B : ⊭ (just v)
        ⊭B rewrite p₁ = (just tt) , subst (T ∘ not) (sym p₂) tt
        Σ⊢¬B : Σ⊢ s (op₁ ¬ₒ B)
        Σ⊢¬B rewrite p₁ = (NegationIntro (just v) (⊭B))
      ---------------------------------------------------------------
      go {s} (suc ℱ) Σ⊢P ⌊ᵗCᵗ⌋ with
          evalExp B s  | inspect (evalExp B) s
      ... | f@(just v) | [ p₁ ] with
          toTruthValue {f} (any tt) | inspect (toTruthValue {f}) (any tt)
      ... | true  | [ p₂ ] = go-true {s} {ℱ} Σ⊢P p₁ p₂ ⌊ᵗCᵗ⌋
      ... | false | [ p₂ ] rewrite Is-just-just ⌊ᵗCᵗ⌋ = go-false Σ⊢P p₁ p₂
      ---------------------------------------------------------------
      -- ════════════════════════════════════════════════════════════


-- ═══════════════════════════════════════════════════════════════════════════════ --

  D4-Conditional-Rule {A} {B} {C} {P} {Q} triple₁ triple₂ s (Pis𝑃 , ⊢P) t = go
      where
      if-then-else-term : {C : Exp} {A B : Block} {s : S}
        (t : ⌊ᵗ (𝔦𝔣 C 𝔱𝔥𝔢𝔫 A 𝔢𝔩𝔰𝔢 B) ; ⸴ s ᵗ⌋)
        → Σ Val (λ v → evalExp C s ≡ just v
        × ((toTruthValue {just v} (any tt) ≡ true
                         × Σ ⌊ᵗ A ⸴ s ᵗ⌋ λ z → ‵ t ≡ ‵ z)
          ⊎ (toTruthValue {just v} (any tt) ≡ false
                         × Σ ⌊ᵗ B ⸴ s ᵗ⌋ λ z → ‵ t ≡ ‵ z)))
      if-then-else-term {C} {A} {B} {s} (suc n , h) with evalExp C s
      if-then-else-term {C} {A} {B} {s} (suc n , ()) | nothing
      ... | just x = x , refl , c
        where
        c : (toTruthValue {just x} (any tt) ≡ true
                 × Σ ⌊ᵗ A ⸴ s ᵗ⌋ λ z → to-witness h ≡ ‵ z)
            ⊎ (toTruthValue {just x} (any tt) ≡ false
                 × Σ ⌊ᵗ B ⸴ s ᵗ⌋ λ z → to-witness h ≡ ‵ z)
        c with toTruthValue {just x} (any tt)
        ... | true = inj₁ (refl , (n , h) , refl)
        ... | false = inj₂ (refl , (n , h) , refl)

      go : Σ⊢ (‵ t) Q
      go with if-then-else-term t
      ... | v , C▵v , inj₁ (⊢v , Σ[ᵗA] , Δ) rewrite Δ = Ω₂ 
        where
          -- C & P is true in state s
          Ω₁ : Σ⊢ s (op₂ C &&ₒ P)
          Ω₁ rewrite C▵v = ConjunctionIntro _ _ 
            ((any tt) , subst T (sym ⊢v) tt) (Pis𝑃 , ⊢P)
 
          -- ∴ Q is true in result of A
          Ω₂ : Σ⊢ (‵ Σ[ᵗA]) Q 
          Ω₂ = triple₁ s Ω₁ Σ[ᵗA]
      
      ... | v , C▵v , inj₂ (¬⊢v , Σ[ᵗB] , Δ)  rewrite Δ = Ω₂ 
        where
          -- ¬C &&ₒ P is true in state s
          Ω₁ : Σ⊢ s (op₂ (op₁ ¬ₒ C) &&ₒ P) 
          Ω₁ rewrite C▵v = ConjunctionIntro _ _
            μ₂ (Pis𝑃 , ⊢P)
              where
              μ₁ : ⊭ (just v)
              μ₁ = (any tt) , subst (T ∘ not) (sym ¬⊢v) tt 

              μ₂ : ⊨ ((¬𝓿 (just v)))
              μ₂ = NegationIntro (just v) μ₁
              
          -- ∴ Q is true in result of B
          Ω₂ : Σ⊢ (‵ Σ[ᵗB] ) Q
          Ω₂ = triple₂ s Ω₁ Σ[ᵗB]


-- ═══════════════════════════════════════════════════════════════════════════════ --

