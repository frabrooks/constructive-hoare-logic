

-- Lib imports
open import Data.Maybe using (Maybe ; just ; nothing ; Is-just ; to-witness ; maybe )
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl ; sym ; inspect ; Reveal_·_is_ ; cong ; subst )
open import Data.Maybe.Relation.Unary.Any renaming ( just to any-just )
open import Data.Product using (Σ ; Σ-syntax ; _×_  ; _,_  ; proj₁ ; proj₂ )
open import Data.Bool using (true ; false ; T )
open import Relation.Nullary using ( ¬_  ; yes ; no )
open import Data.Empty using ( ⊥ ; ⊥-elim )
open import Data.Nat
open import Function using ( _∘_ )
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using ( ⊤ ; tt )
open import Level using (Level)

open import Representation.Data using (Data-Implementation)
open import Representation.State using (S-Representation)


module Hoare-Logic.Axioms (𝔡 : Data-Implementation )
  (sRep : S-Representation 𝔡 ) where

  open Data-Implementation 𝔡
  open S-Representation sRep

  open import Mini-C.Expressions 𝔡 sRep
  open import Assertions.Props 𝔡 sRep

  open import Mini-C.Lang 𝔡 sRep
  open import Mini-C.Evaluation 𝔡 sRep

  open import Hoare-Logic.Semantics 𝔡 sRep
  open import Hoare-Logic.Termination 𝔡 sRep

  
  evalExp-Var : (v : Id) (s : S) → evalExp (term (Var v)) s ≡ getVarVal v s
  evalExp-Var v s = refl

  ⊎-maybe : {A : Set} (m : Maybe A) → m ≡ nothing ⊎ Σ A (λ a → m ≡ just a)
  ⊎-maybe nothing = inj₁ refl
  ⊎-maybe (just x) = inj₂ (x , refl)

  Is-just-nothing : {l : Level} {A : Set l} → Is-just {l} {A} nothing → ⊥
  Is-just-nothing ()

  Is-just-just : {l : Level} {A : Set l} {a : A} (p : Is-just (just a)) → to-witness p ≡ a
  Is-just-just (Any.just x) = refl

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
  ... | yes q rewrite evalExp-Var x (updateState i v s) | q | updateGet x v s = sym comp
  ... | no  q rewrite evalExp-Var x (updateState i v s) | ignoreTop i x v q s = refl

  -- for all i e P, in all states, the Axiom of assignment holds
  D0-axiomOfAssignment : ∀ i e P → S → ⟪ (sub e i P) ⟫  ( i := e ; ) ⟪ P ⟫
  D0-axiomOfAssignment i e P s s' (x₁ , x₂) (suc n , p) with ⊎-maybe (evalExp e s')
  ... | inj₁ q rewrite q = ⊥-elim (Is-just-nothing p)
  ... | inj₂ (v , q) rewrite q | Is-just-just p | evalExp-updState P e i v s' q = x₁ , x₂
  

  D1-Rule-of-Consequence-post : ∀ {P} {Q} {R} {S} → ⟪ P ⟫ Q ⟪ R ⟫ → R ⇒ S → ⟪ P ⟫ Q ⟪ S ⟫
  D1-Rule-of-Consequence-post = λ x x₁ s x₂ ϕ → x₁ (to-witness (proj₂ ϕ)) (x s x₂ ϕ)

  D1-Rule-of-Consequence-pre : ∀ {P} {Q} {R} {S} → ⟪ P ⟫ Q ⟪ R ⟫ → S ⇒ P → ⟪ S ⟫ Q ⟪ R ⟫
  D1-Rule-of-Consequence-pre {P} {Q} {R} {S} = λ x x₁ s x₂ ϕ → x s (x₁ s x₂) ϕ

  ǫ : ∀ {Q₁} {Q₂} {s} → ⌊ᵗ Q₁ ; Q₂ ; ⸴  s ᵗ⌋ → Σ ⌊ᵗ Q₁ ; ⸴ s ᵗ⌋ ( λ μ →  ⌊ᵗ Q₂ ; ⸴ (to-witness (proj₂ μ)) ᵗ⌋ )
  ǫ ψ = {!!}


  D2-Rule-of-Composition : ∀ {P} {Q₁} {R₁} {Q₂} {R} → ⟪ P ⟫ Q₁ ; ⟪ R₁ ⟫ → ⟪ R₁ ⟫ Q₂ ; ⟪ R ⟫ → ⟪ P ⟫ Q₁ ; Q₂ ; ⟪ R ⟫
  D2-Rule-of-Composition PQR₁ PQR₂ s x ϕ with ǫ ϕ
  ... | (Q1ₙ , ijQ1ₙ) , Q2ₙ , ijQ2ₙ = PQR₂ (to-witness ijQ1ₙ) (PQR₁ s x (Q1ₙ , ijQ1ₙ) ) ( Q2ₙ , ijQ2ₙ)



 --PQR₂ (to-witness (proj₂ (proj₁ (ǫ ϕ)))) (PQR₁ s x (proj₁ (ǫ  ϕ))) (proj₂ (ǫ ϕ)) -- (PQR₁  x (proj₁ (ǫ ϕ))) (proj₂ (ǫ ϕ))

{-
  Γ : ∀ i e s → (ϕ : Is-just (evalExp e s)) → Is-just (updateState i (to-witness ϕ) s)
  Γ i e s ij = ?
-}


  {-
  D2-Rule-of-Composition : ∀ {P} {Q₁} {R₁} {Q₂} {R} → ⟪ P ⟫ Q₁ ⟪ R₁ ⟫ → ⟪ R₁ ⟫ Q₂ ⟪ R ⟫ → ⟪ P ⟫ (𝑠𝑒𝑞꞉ (Q₁ ﹔ Q₂)) ⟪ R ⟫
  D2-Rule-of-Composition PQR₁ PQR₂  = λ s x ϕ → {!!}
    where
    ǫ : ∀ {Q₁} {Q₂} {s} → ⌊ᵗ ( 𝑠𝑒𝑞꞉ (Q₁ ﹔ Q₂)) ⸴  s ᵗ⌋ → Σ ⌊ᵗ Q₁ ⸴ s ᵗ⌋ ( λ μ →  ⌊ᵗ Q₂ ⸴ (to-witness (proj₂ μ)) ᵗ⌋ )
    ǫ {𝑎𝑠𝑠𝑖꞉ (i ꞉= e)} {𝑎𝑠𝑠𝑖꞉ (i' ꞉= e')} {s} ( (suc (suc n)) , snd) with evalExp e s | inspect (evalExp e) s
    ... | just x | Eq.[ eq ] with evalExp e' (updateState i x s) | inspect (evalExp e') (updateState i x s)
    ... | just x' | Eq.[ eq' ]  = let δ = subst (λ k → Is-just (Data.Maybe.map (λ v → updateState i v s) k)) (sym eq) (any-just tt) in
                                  ( 4 ,  δ    ) , 
                                  ( 3 ,  {!!} )
    ǫ {𝑎𝑠𝑠𝑖꞉ x} {𝑠𝑒𝑞꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑎𝑠𝑠𝑖꞉ x} {𝑐𝑡𝑟𝑙꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑎𝑠𝑠𝑖꞉ x} {𝑙𝑜𝑜𝑝꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑎𝑠𝑠𝑖꞉ x} {𝑠𝑘𝑖𝑝} (fst , snd) = {!!}
    ǫ {𝑠𝑒𝑞꞉ x} {𝑎𝑠𝑠𝑖꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑠𝑒𝑞꞉ x} {𝑠𝑒𝑞꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑠𝑒𝑞꞉ x} {𝑐𝑡𝑟𝑙꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑠𝑒𝑞꞉ x} {𝑙𝑜𝑜𝑝꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑠𝑒𝑞꞉ x} {𝑠𝑘𝑖𝑝} (fst , snd) = {!!}
    ǫ {𝑐𝑡𝑟𝑙꞉ x} {𝑎𝑠𝑠𝑖꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑐𝑡𝑟𝑙꞉ x} {𝑠𝑒𝑞꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑐𝑡𝑟𝑙꞉ x} {𝑐𝑡𝑟𝑙꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑐𝑡𝑟𝑙꞉ x} {𝑙𝑜𝑜𝑝꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑐𝑡𝑟𝑙꞉ x} {𝑠𝑘𝑖𝑝} (fst , snd) = {!!}
    ǫ {𝑙𝑜𝑜𝑝꞉ x} {𝑎𝑠𝑠𝑖꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑙𝑜𝑜𝑝꞉ x} {𝑠𝑒𝑞꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑙𝑜𝑜𝑝꞉ x} {𝑐𝑡𝑟𝑙꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑙𝑜𝑜𝑝꞉ x} {𝑙𝑜𝑜𝑝꞉ x₁} (fst , snd) = {!!}
    ǫ {𝑙𝑜𝑜𝑝꞉ x} {𝑠𝑘𝑖𝑝} (fst , snd) = {!!}
    ǫ {𝑠𝑘𝑖𝑝} {𝑎𝑠𝑠𝑖꞉ x} (fst , snd) = {!!}
    ǫ {𝑠𝑘𝑖𝑝} {𝑠𝑒𝑞꞉ x} (fst , snd) = {!!}
    ǫ {𝑠𝑘𝑖𝑝} {𝑐𝑡𝑟𝑙꞉ x} (fst , snd) = {!!}
    ǫ {𝑠𝑘𝑖𝑝} {𝑙𝑜𝑜𝑝꞉ x} (fst , snd) = {!!}
    ǫ {𝑠𝑘𝑖𝑝} {𝑠𝑘𝑖𝑝} (fst , snd) = {!!}

-}

{-
  ssEvalwithFuel-evalAssi : (i : Id) (e : Exp) (s : S) → ssEvalwithFuel 1 (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) , just s) ≡ evalAssi s (i ꞉= e)
  ssEvalwithFuel-evalAssi i e s = refl

  ssEvalWithFuel-seq : (n : ℕ) (c₁ c₂ c₃ : 𝐶) (s : S)
                       → ssEvalwithFuel (suc n) (𝑠𝑒𝑞꞉ (𝑠𝑒𝑞꞉ (c₁ ﹔ c₂) ﹔ c₃) , just s)
                          ≡ ssEvalwithFuel (n) (𝑠𝑒𝑞꞉ (c₁ ﹔ (𝑠𝑒𝑞꞉ (c₂ ﹔ c₃))) ,  just s)
  ssEvalWithFuel-seq n c₁ c₂ c₃ s = refl


  Term-asm : {i : Id} {e : Exp} (x : i := e) (s s' : S)
             → evalAssi s x ≡ just s'
             → Σ ⌊ᵗ 𝑎𝑠𝑠𝑖꞉ x ⸴ s ᵗ⌋ λ c → to-witness (proj₂ c) ≡ s'
  Term-asm {i} {e} (i ꞉= e) s s' c rewrite ssEvalwithFuel-evalAssi i e s = (1 , proj₁ z) , proj₂ z
    where
      z₁ : maybe (λ x → just (updateState i x s)) nothing (evalExp e s) ≡ Data.Maybe.map (λ v → updateState i v s) (evalExp e s)
      z₁ = refl

      z : Σ (Is-just (Data.Maybe.map (λ v → updateState i v s) (evalExp e s))) λ c → to-witness c ≡ s'
      z rewrite z₁ | c =  Any.just tt , refl


  ssEvalwithFuel-nothing : (n : ℕ) (c : 𝐶) → ssEvalwithFuel n (c , nothing) ≡ nothing
  ssEvalwithFuel-nothing zero (𝑎𝑠𝑠𝑖꞉ x) = refl
  ssEvalwithFuel-nothing (suc n) (𝑎𝑠𝑠𝑖꞉ (i ꞉= e)) = refl
  ssEvalwithFuel-nothing zero (𝑠𝑒𝑞꞉ x) = refl
  ssEvalwithFuel-nothing (suc n) (𝑠𝑒𝑞꞉ (c₁ ﹔ c₂)) = refl
  ssEvalwithFuel-nothing zero (𝑐𝑡𝑟𝑙꞉ x) = refl
  ssEvalwithFuel-nothing (suc n) (𝑐𝑡𝑟𝑙꞉ (𝑖𝑓 b 𝑡ℎ𝑒𝑛 c₁ 𝑒𝑙𝑠𝑒 c₂)) = refl
  ssEvalwithFuel-nothing zero (𝑙𝑜𝑜𝑝꞉ x) = refl
  ssEvalwithFuel-nothing (suc n) (𝑙𝑜𝑜𝑝꞉ (𝑤ℎ𝑖𝑙𝑒 b 𝑑𝑜 c₁)) = refl
  ssEvalwithFuel-nothing zero 𝑠𝑘𝑖𝑝 = refl
  ssEvalwithFuel-nothing (suc n) 𝑠𝑘𝑖𝑝 = refl

  π : ∀ {ℓ} {A} {a} {s : Maybe {ℓ} A} → s ≡ just a → ( ϕ : Is-just s ) → to-witness ϕ ≡ a
  π {_} {_} {_} .{just _} refl (any-just _) = refl


  Term-comp2 : {c₁ c₂ : 𝐶} {s : S} {n₁ n₂ : ℕ}
               (t₁ : Is-just (ssEvalwithFuel n₁ (c₁ , just s)))
               (t₂ : Is-just (ssEvalwithFuel n₂ (c₂ , just (to-witness t₁))))
               → Is-just (ssEvalwithFuel (suc (n₁ Data.Nat.+ n₂)) (𝑠𝑒𝑞꞉ (c₁ ﹔ c₂) , just s))
  Term-comp2 {𝑎𝑠𝑠𝑖꞉ (i ꞉= e)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = z -- rewrite ssEvalwithFuel-evalAssi i e s 
    where
      z₁ : maybe (λ x → just (updateState i x s)) nothing (evalExp e s) ≡ Data.Maybe.map (λ v → updateState i v s) (evalExp e s)
      z₁ = refl

      z : Is-just (ssEvalwithFuel (suc (n₁ Data.Nat.+ n₂)) (c₂ , maybe (λ x → just (updateState i x s)) nothing (evalExp e s)))
      z  with evalExp e s
      ... | just x  with addFuel (suc n₁) (n₂ , t₂)
      ... | ( _ , ij ) , eq rewrite eq = subst ((λ s →  Any (λ _ → ⊤)
            (ssEvalwithFuel (suc (n₁ Data.Nat.+ n₂)) (c₂ , just s)))) z₃ ij
          where
          z₃ : to-witness t₁ ≡ (updateState i x s)
          z₃ = π refl t₁

  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) ﹔ 𝑎𝑠𝑠𝑖꞉ (i' ꞉= e'))} {c₂} {s} {suc (suc n₁)} {n₂} t₁ t₂ = z
    where
      
      z : Is-just (ssEvalwithFuel (suc (n₁ Data.Nat.+ n₂)) ( 𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i' ꞉= e') ﹔ c₂) , maybe (λ x → just (updateState i x s)) nothing (evalExp e s)))
      z  with evalExp e s
      ... | just x  with addFuel n₁ (n₂ , t₂)
      ... | ( _ , ij ) , eq with evalExp e' (updateState i x s)
      ... | just x₁ rewrite eq  = subst (λ s →  Any (λ _ → ⊤)
            (ssEvalwithFuel (n₁ Data.Nat.+ n₂) ( c₂ , just s ))) z₃ ij
          where
          z₃ : to-witness t₁ ≡ updateState i' x₁ (updateState i x s)
          z₃ = π refl t₁


  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) ﹔ 𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i' ꞉= e') ﹔ 𝑎𝑠𝑠𝑖꞉ (i'' ꞉= e'')))} {c₃} {s} {suc (suc n₁)} {n₂} t₁ t₂ with evalExp e s | n₁
  ... | just v | suc n₁' with addFuel n₁' (n₂ , t₂)
  ... | (.(n₁' Data.Nat.+ n₂) , snd₁) , refl with evalExp e' (updateState i v s)
  ... | just v' with evalExp e'' (updateState i' v' (updateState i v s))
  ... | just v'' with n₂
  ... | zero rewrite 0⇒𝑠𝑘𝑖𝑝 {to-witness t₁} {c₃} t₂ = {!!}
  ... | suc foo = {!!}


    where
    z₃ : to-witness t₁ ≡ updateState i'' v'' (updateState i' v' (updateState i v s))
    z₃ = π refl t₁

-- let foo = subst ((λ s → Is-just (ssEvalwithFuel (n₁' Data.Nat.+ n₂) (c₃ , just s)))) z₃ snd₁ in {!!}

  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) ﹔ 𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i' ꞉= e') ﹔ 𝑠𝑒𝑞꞉ x))} {c₃} {s} {suc (suc n₁)} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) ﹔ 𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i' ꞉= e') ﹔ 𝑐𝑡𝑟𝑙꞉ x))} {c₃} {s} {suc (suc n₁)} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) ﹔ 𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i' ꞉= e') ﹔ 𝑙𝑜𝑜𝑝꞉ x))} {c₃} {s} {suc (suc n₁)} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) ﹔ 𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i' ꞉= e') ﹔ 𝑠𝑘𝑖𝑝))} {c₃} {s} {suc (suc n₁)} {n₂} t₁ t₂ = {!!}

  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) ﹔ 𝑠𝑒𝑞꞉ (𝑠𝑒𝑞꞉ x ﹔ c₂))} {c₃} {s} {suc (suc n₁)} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) ﹔ 𝑠𝑒𝑞꞉ (𝑐𝑡𝑟𝑙꞉ x ﹔ c₂))} {c₃} {s} {suc (suc n₁)} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) ﹔ 𝑠𝑒𝑞꞉ (𝑙𝑜𝑜𝑝꞉ x ﹔ c₂))} {c₃} {s} {suc (suc n₁)} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ (i ꞉= e) ﹔ 𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ c₂))} {c₃} {s} {suc (suc n₁)} {n₂} t₁ t₂ = {!!}



  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ x ﹔ 𝑐𝑡𝑟𝑙꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ x ﹔ 𝑙𝑜𝑜𝑝꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑎𝑠𝑠𝑖꞉ x ﹔ 𝑠𝑘𝑖𝑝)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑠𝑒𝑞꞉ x ﹔ 𝑎𝑠𝑠𝑖꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑠𝑒𝑞꞉ x ﹔ 𝑠𝑒𝑞꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑠𝑒𝑞꞉ x ﹔ 𝑐𝑡𝑟𝑙꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑠𝑒𝑞꞉ x ﹔ 𝑙𝑜𝑜𝑝꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑠𝑒𝑞꞉ x ﹔ 𝑠𝑘𝑖𝑝)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑐𝑡𝑟𝑙꞉ x ﹔ 𝑎𝑠𝑠𝑖꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑐𝑡𝑟𝑙꞉ x ﹔ 𝑠𝑒𝑞꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑐𝑡𝑟𝑙꞉ x ﹔ 𝑐𝑡𝑟𝑙꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑐𝑡𝑟𝑙꞉ x ﹔ 𝑙𝑜𝑜𝑝꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑐𝑡𝑟𝑙꞉ x ﹔ 𝑠𝑘𝑖𝑝)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑙𝑜𝑜𝑝꞉ x ﹔ 𝑎𝑠𝑠𝑖꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑙𝑜𝑜𝑝꞉ x ﹔ 𝑠𝑒𝑞꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑙𝑜𝑜𝑝꞉ x ﹔ 𝑐𝑡𝑟𝑙꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑙𝑜𝑜𝑝꞉ x ﹔ 𝑙𝑜𝑜𝑝꞉ x₁)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑙𝑜𝑜𝑝꞉ x ﹔ 𝑠𝑘𝑖𝑝)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ 𝑎𝑠𝑠𝑖꞉ x)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ 𝑠𝑒𝑞꞉ x)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ 𝑐𝑡𝑟𝑙꞉ x)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ 𝑙𝑜𝑜𝑝꞉ x)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑒𝑞꞉ (𝑠𝑘𝑖𝑝 ﹔ 𝑠𝑘𝑖𝑝)} {c₂} {s} {suc n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑐𝑡𝑟𝑙꞉ x} {c₂} {s} {n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑙𝑜𝑜𝑝꞉ x} {c₂} {s} {n₁} {n₂} t₁ t₂ = {!!}
  Term-comp2 {𝑠𝑘𝑖𝑝} {c₂} {s} {n₁} {n₂} t₁ t₂ = {!!}

  Term-comp : {c₁ c₂ : 𝐶} {s : S} → (t₁ : ⌊ᵗ c₁ ⸴ s ᵗ⌋) (t₂ : ⌊ᵗ c₂ ⸴ to-witness (proj₂ t₁) ᵗ⌋)
              → ⌊ᵗ 𝑠𝑒𝑞꞉ (c₁ ﹔ c₂) ⸴ s ᵗ⌋
  Term-comp {c₁} {c₂} {s} (n₁ , t₁) (n₂ , t₂) = suc (n₁ Data.Nat.+ n₂) , Term-comp2 {c₁} {c₂} {s} {n₁} {n₂} t₁ t₂


  ǫ : ∀ {Q₁} {Q₂} {s} → ⌊ᵗ ( 𝑠𝑒𝑞꞉ (Q₁ ﹔ Q₂)) ⸴  s ᵗ⌋ → Σ ⌊ᵗ Q₁ ⸴ s ᵗ⌋ ( λ μ →  ⌊ᵗ Q₂ ⸴ (to-witness (proj₂ μ)) ᵗ⌋ )
  ǫ {𝑎𝑠𝑠𝑖꞉ x} {Q₂} {s} (suc n , snd) with ⊎-maybe (evalAssi s x)
  ... | inj₁ q rewrite q | ssEvalwithFuel-nothing n Q₂ = ⊥-elim (Is-just-nothing snd)
  ... | inj₂ (a , q) rewrite q = proj₁ (Term-asm x s a q) , n , z
      where
        z : Is-just (ssEvalwithFuel n (Q₂ , just (to-witness (proj₂ (proj₁ (Term-asm x s a q))))))
        z rewrite (proj₂ (Term-asm x s a q)) = snd

  ǫ {𝑠𝑒𝑞꞉ (c₁ ﹔ c₂)} {Q₂} {s} (suc n , snd) rewrite ssEvalWithFuel-seq n c₁ c₂ Q₂ s = Term-comp z₁ z₄ , {!!}
      where
        z : Σ ⌊ᵗ c₁ ⸴ s ᵗ⌋ ( λ μ →  ⌊ᵗ 𝑠𝑒𝑞꞉ (c₂ ﹔ Q₂) ⸴ (to-witness (proj₂ μ)) ᵗ⌋ )
        z = ǫ (n , snd)

        z₁ : ⌊ᵗ c₁ ⸴ s ᵗ⌋
        z₁ = proj₁ z

        z₂ : ⌊ᵗ 𝑠𝑒𝑞꞉ (c₂ ﹔ Q₂) ⸴ (to-witness (proj₂ z₁)) ᵗ⌋
        z₂ = proj₂ z

        z₃ : Σ ⌊ᵗ c₂ ⸴ to-witness (proj₂ z₁) ᵗ⌋ ( λ μ →  ⌊ᵗ Q₂ ⸴ to-witness (proj₂ μ) ᵗ⌋ )
        z₃ = ǫ z₂

        z₄ : ⌊ᵗ c₂ ⸴ to-witness (proj₂ z₁) ᵗ⌋
        z₄ = proj₁ z₃

        z₅ : ⌊ᵗ Q₂ ⸴ to-witness (proj₂ z₄) ᵗ⌋
        z₅ = proj₂ z₃


  ǫ {𝑐𝑡𝑟𝑙꞉ x} {Q₂} (suc n , snd) = {!!} , {!!}
  ǫ {𝑙𝑜𝑜𝑝꞉ x} {Q₂} (suc n , snd) = {!!} , {!!}
  ǫ {𝑠𝑘𝑖𝑝} {Q₂} (suc n , snd) = {!!} , {!!}

  D2-Rule-of-Composition : ∀ {P} {Q₁} {R₁} {Q₂} {R} → ⟪ P ⟫ Q₁ ⟪ R₁ ⟫ → ⟪ R₁ ⟫ Q₂ ⟪ R ⟫ → ⟪ P ⟫ (𝑠𝑒𝑞꞉ (Q₁ ﹔ Q₂)) ⟪ R ⟫
  D2-Rule-of-Composition {P} {Q₁} {R₁} {Q₂} {R} PQR₁ PQR₂ s x ϕ = {!!}
    -- PQR₂ (to-witness j₁) {!!} {!!} -- PQR₂ (to-witness (proj₂ (proj₁ (ǫ ϕ)))) (PQR₁ s x (proj₁ (ǫ ϕ))) {!!}
    --PQR₂ (to-witness (proj₂ (proj₁ (ǫ ϕ)))) (PQR₁ s x (proj₁ (ǫ ϕ))) (proj₂ (ǫ ϕ)) -- (PQR₁  x (proj₁ (ǫ ϕ))) (proj₂ (ǫ ϕ))
    where
      z₁ : ⌊ᵗ Q₁ ⸴ s ᵗ⌋
      z₁ = proj₁ (ǫ ϕ)

      n₁ : ℕ
      n₁ = proj₁ z₁

      j₁ : Is-just (ssEvalwithFuel n₁ ( Q₁ , just s ))
      j₁ = proj₂ z₁

      z₂ : ⌊ᵗ Q₂ ⸴ to-witness (proj₂ (proj₁ (ǫ ϕ))) ᵗ⌋
      z₂ = proj₂ (ǫ ϕ)



  -}

  {-
  axiomOfAssignment : ∀ {i} {v} {e} (p  :  𝑃) → ( a :  i := e )
                        → ( ( s : S ) →  evalExp e s ≡ (just v))
                        → ⟪ (sub v i p) ⟫ ( 𝑎𝑠𝑠𝑖꞉ a ) ⟪ p ⟫
  axiomOfAssignment {i} {v} {e} p (.i ꞉= .e) pr s pre s' eval =  {!!}
  
 
  axiomOfAssignment : ∀ {i} {e}  (p  :  𝑃) → ( a :  i := e )
                        → ⟪ (sub e i  p) ⟫ ( 𝑎𝑠𝑠𝑖꞉ a ) ⟪ p ⟫
  axiomOfAssignment {i} {e} p (.i ꞉= .e) s pre s' eval with p | (sub e i p)
  ... | ᶻ⇉ᵇ x x₁ x₂     | ᶻ⇉ᵇ x₃ x₄ x₅ = {!!}
  ... | ᶻ⇉ᵇ x x₁ x₂     | ⇉ᵇ bar x₃ bar₁ = {!!}
  ... | ᶻ⇉ᵇ x x₁ x₂     | ⇾ᵇ x₃ bar = {!!}
  ... | ᶻ⇉ᵇ x x₁ x₂     | term𝔹 x₃ = {!!}
  ... | ⇉ᵇ foo x foo₁  | ᶻ⇉ᵇ x₁ x₂ x₃ = {!!}
  ... | ⇉ᵇ foo x foo₁  | ⇉ᵇ bar x₁ bar₁ = {!!}
  ... | ⇉ᵇ foo x foo₁  | ⇾ᵇ x₁ bar = {!!}
  ... | ⇉ᵇ foo x foo₁  | term𝔹 x₁ = {!!}
  ... | ⇾ᵇ x foo       | ᶻ⇉ᵇ x₁ x₂ x₃ = {!!}
  ... | ⇾ᵇ x foo       | ⇉ᵇ bar x₁ bar₁ = {!!}
  ... | ⇾ᵇ x foo       | ⇾ᵇ x₁ bar = {!!}
  ... | ⇾ᵇ x foo       | term𝔹 x₁ = {!!}
  ... | term𝔹 x        | ᶻ⇉ᵇ x₁ x₂ x₃ = {!!}
  ... | term𝔹 x        | ⇉ᵇ bar x₁ bar₁ = {!!}
  ... | term𝔹 x        | ⇾ᵇ x₁ bar = {!!}
  ... | term𝔹 x        | term𝔹 x₁ = {!!}
-}


{-
  -- Axioms
  axiom-of-assignment : ∀ {i} {v} {p} {s s'} {e}
                        → ((sub v i p) ← s)
                        -- Proof that assignment terminates
                        → (i := e |evalExp= v USING s GIVES s') 
                        → ( p ← s' ) 
  axiom-of-assignment {i} {v} {p} {s} {.(updateState i v s)}
                          (holdsBecause eval→𝑻)
                          ((.i :=' _ w/ .s andPExp) x)
                          rewrite sym (s⇔u i v s p)
                          = holdsBecause eval→𝑻



   -- R⊃S → P{Q}R → P{Q}S
  
   -- {Q} S {R}

  


  -- Not sure about these, probs need to have Hoare triple (i.e.  ⊢P{Q}R ) for these to make sense 

  rule-of-consequence1 : ∀ {i} {v} {p q r} {s s'} {e}

                         → ((Assert q ∵ s') → (Assert r ∵ s' ))          --       R ⊃ S
                         
                         → (Assert p ∵ s')                                --        P
                         
                         -- Proof that program terminates
                         -- TODO: All program kinds need to go here, not just
                         -- assignment (i.e. while, block, ifelse etc.)
                         → (i := e |evalExp= v USING s GIVES s')                  -- {Q}

                         → (Assert q ∵ s')                                    -- R

                         → (Assert r ∵ s')
  rule-of-consequence1 {i} {v} {p} {q} {r} {s} {s'} q⊃r a prog b = q⊃r b



  rule-of-consequence2 : ∀ {i} {v} {p q r} {s s'} {e}

                         → ((Assert p ∵ s) → (Assert r ∵ s' ))
                         
                         → (Assert p ∵ s)
                         
                         -- Proof that program terminates
                         -- TODO: All program kinds need to go here, not just
                         -- assignment (i.e. while, block, ifelse etc.)
                         → (i := e |evalExp= v USING s GIVES s')

                         → (Assert q ∵ s')

                         → (Assert r ∵ s)
  rule-of-consequence2 {i} {v} {p} {q} {r} {s} {s'} q⊃r a prog b = {!!}

-}




