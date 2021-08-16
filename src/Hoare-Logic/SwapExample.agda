
-- Lib Imports
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl ; sym ; subst )
open import Relation.Nullary using ( yes ;  no )
open import Data.Empty using ( ⊥ ; ⊥-elim )

-- Local Imports
open import Data-Interface using (Data-Implementation)
open import State-Interface using (State-Implementation)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Hoare-Logic.SwapExample ( 𝔡 : Data-Implementation )
  (𝔖 : State-Implementation 𝔡 ) where

  -- Local Dependent Imports
  open Data-Implementation 𝔡
  open State-Implementation 𝔖
  open import Language.Expressions 𝔡 𝔖
  open import Language.Assertions 𝔡 𝔖
  open import Language.ExampleProgs 𝔡 𝔖
  open import Language.Mini-Imp 𝔡 𝔖
  open import Evaluation.Termination 𝔡 𝔖
  open import Hoare-Logic.Semantics 𝔡 𝔖
  open import Hoare-Logic.Rules 𝔡 𝔖

  -- ════════════════════════════════════════════════════════════════════════════
  -- Example of using this library to prove the correctness of the swap program:

  SWAP : ∀ 𝑿 𝒀 →
                 ⟪ 𝒙 =̌= (𝑐𝑜𝑛𝑠𝑡 𝑿) ∧ 𝒚 =̌= (𝑐𝑜𝑛𝑠𝑡 𝒀) ⟫            -- Precondition
    
                            𝒛 := 𝑣𝑎𝑙 𝒙 ;
                            𝒙 := 𝑣𝑎𝑙 𝒚 ;
                            𝒚 := 𝑣𝑎𝑙 𝒛 ;

                 ⟪ 𝒙 =̌= (𝑐𝑜𝑛𝑠𝑡 𝒀) ∧ 𝒚 =̌= (𝑐𝑜𝑛𝑠𝑡 𝑿) ⟫           -- Postcondition
  SWAP 𝑿 𝒀 = ∎
     where
     
     -- Reasoning backwards from Postcondition Q to Precondition P
     
     PRE : Assertion
     PRE = 𝒙 =̌= (𝑐𝑜𝑛𝑠𝑡 𝑿) ∧ 𝒚 =̌= (𝑐𝑜𝑛𝑠𝑡 𝒀)

     POST : Assertion
     POST = 𝒙 =̌= (𝑐𝑜𝑛𝑠𝑡 𝒀) ∧ 𝒚 =̌= (𝑐𝑜𝑛𝑠𝑡 𝑿)
     
     A₁ : Assertion
     A₁ = ((sub (𝑣𝑎𝑙 𝒛) 𝒚 (𝑣𝑎𝑙 𝒙)) == (𝑐𝑜𝑛𝑠𝑡 𝒀)) ∧ ( 𝒛 =̌= (𝑐𝑜𝑛𝑠𝑡 𝑿))
     
     s₁ : ⟪ A₁ ⟫ 𝒚 := 𝑣𝑎𝑙 𝒛 ; ⟪ POST ⟫
     s₁ = let Ψ = D0-Axiom-of-Assignment 𝒚 (𝑣𝑎𝑙 𝒛) POST in go Ψ
          where
          go : ⟪ ((sub (𝑣𝑎𝑙 𝒛) 𝒚 (𝑣𝑎𝑙 𝒙)) == (𝑐𝑜𝑛𝑠𝑡 𝒀))
               ∧ ((sub (𝑣𝑎𝑙 𝒛) 𝒚 (𝑣𝑎𝑙 𝒚)) == (𝑐𝑜𝑛𝑠𝑡 𝑿)) ⟫
               𝒚 := 𝑣𝑎𝑙 𝒛 ; ⟪ POST ⟫ →
               ⟪ A₁ ⟫ 𝒚 := 𝑣𝑎𝑙 𝒛 ; ⟪ POST ⟫
          go t with 𝒚 ?id= 𝒙
          go t | yes p rewrite p with 𝒙 ?id= 𝒙
          go t | yes p | yes q = t
          go t | yes p | no ¬q = ⊥-elim (¬q refl)         
          go t | no ¬p with 𝒚 ?id= 𝒚
          go t | no ¬p | yes q = t
          go t | no ¬p | no ¬q = ⊥-elim (¬q refl)                 

     A₂ : Assertion
     A₂ = ((sub (𝑣𝑎𝑙 𝒚) 𝒙 (sub (𝑣𝑎𝑙 𝒛) 𝒚 (𝑣𝑎𝑙 𝒙))) == (𝑐𝑜𝑛𝑠𝑡 𝒀)) ∧ ( 𝒛 =̌= (𝑐𝑜𝑛𝑠𝑡 𝑿))

     s₂ : ⟪ A₂ ⟫ 𝒙 := 𝑣𝑎𝑙 𝒚 ; ⟪ A₁ ⟫
     s₂ = let Ψ = D0-Axiom-of-Assignment 𝒙 (𝑣𝑎𝑙 𝒚) A₁ in go Ψ
          where
          go : ⟪ ((sub (𝑣𝑎𝑙 𝒚) 𝒙 (sub (𝑣𝑎𝑙 𝒛) 𝒚 (𝑣𝑎𝑙 𝒙))) == (𝑐𝑜𝑛𝑠𝑡 𝒀))
               ∧ ((sub (𝑣𝑎𝑙 𝒚) 𝒙 (𝑣𝑎𝑙 𝒛)) == (𝑐𝑜𝑛𝑠𝑡 𝑿)) ⟫
               𝒙 := 𝑣𝑎𝑙 𝒚 ; ⟪ A₁ ⟫ →
               ⟪ A₂ ⟫ 𝒙 := 𝑣𝑎𝑙 𝒚 ; ⟪ A₁ ⟫
          go t with 𝒙 ?id= 𝒛
          go t | yes p = ⊥-elim (𝒙≢𝒛 p)
          go t | no  _ = t

     A₃ : Assertion
     A₃ =   ((sub (𝑣𝑎𝑙 𝒙) 𝒛 (sub (𝑣𝑎𝑙 𝒚) 𝒙 (sub (𝑣𝑎𝑙 𝒛) 𝒚 (𝑣𝑎𝑙 𝒙)))) == (𝑐𝑜𝑛𝑠𝑡 𝒀))
          ∧ ( 𝒙 =̌= (𝑐𝑜𝑛𝑠𝑡 𝑿) )

     s₃ : ⟪ A₃ ⟫ 𝒛 := 𝑣𝑎𝑙 𝒙 ; ⟪ A₂ ⟫
     s₃ = let Ψ = D0-Axiom-of-Assignment 𝒛 (𝑣𝑎𝑙 𝒙) A₂ in go Ψ
          where
          go : ⟪ ((sub (𝑣𝑎𝑙 𝒙) 𝒛 (sub (𝑣𝑎𝑙 𝒚) 𝒙 (sub (𝑣𝑎𝑙 𝒛) 𝒚 (𝑣𝑎𝑙 𝒙)))) == (𝑐𝑜𝑛𝑠𝑡 𝒀))
               ∧ ((sub (𝑣𝑎𝑙 𝒙) 𝒛 (𝑣𝑎𝑙 𝒛)) == (𝑐𝑜𝑛𝑠𝑡 𝑿)) ⟫
               𝒛 := 𝑣𝑎𝑙 𝒙 ; ⟪ A₂ ⟫ →
               ⟪ A₃ ⟫ 𝒛 := 𝑣𝑎𝑙 𝒙 ; ⟪ A₂ ⟫
          go t with 𝒛 ?id= 𝒛
          go t | yes _ = t 
          go t | no ¬p = ⊥-elim (¬p refl) 

     s₄ : A₃ ≡ ( 𝒚 =̌= (𝑐𝑜𝑛𝑠𝑡 𝒀) ∧ 𝒙 =̌= (𝑐𝑜𝑛𝑠𝑡 𝑿) )
     s₄ with 𝒚 ?id= 𝒙
     s₄ | yes _ with 𝒙 ?id= 𝒛
     s₄ | yes _ | yes q = ⊥-elim (𝒙≢𝒛 q)
     s₄ | yes _ | no  _ with 𝒛 ?id= 𝒛
     s₄ | yes p | no  _ | yes _ rewrite p = refl
     s₄ | yes _ | no  _ | no  w = ⊥-elim (w refl)
     s₄ | no ¬p with 𝒙 ?id= 𝒙
     s₄ | no  _ | no ¬q = ⊥-elim (¬q refl)
     s₄ | no  _ | yes _ with 𝒛 ?id= 𝒚
     s₄ | no  _ | yes _ | yes w = ⊥-elim (𝒚≢𝒛 (sym w))
     s₄ | no  _ | yes _ | no  _ = refl


     s₅ : ⟪ A₂ ⟫ 𝒙 := 𝑣𝑎𝑙 𝒚 ;  𝒚 := 𝑣𝑎𝑙 𝒛 ; ⟪ POST ⟫
     s₅ = D2-Rule-of-Composition {A₂} {A₁} {POST} s₂ s₁


     s₆ : ⟪ A₃ ⟫ 𝒛 := 𝑣𝑎𝑙 𝒙 ;  𝒙 := 𝑣𝑎𝑙 𝒚 ;  𝒚 := 𝑣𝑎𝑙 𝒛 ; ⟪ POST ⟫
     s₆ = D2-Rule-of-Composition {A₃} {A₂} {POST} s₃ s₅


     ∎ : ⟪ PRE ⟫ 𝒛 := 𝑣𝑎𝑙 𝒙 ;  𝒙 := 𝑣𝑎𝑙 𝒚 ;  𝒚 := 𝑣𝑎𝑙 𝒛 ; ⟪ POST ⟫
     ∎ = D1-Rule-of-Consequence-pre {A₃} {swap} {POST} {PRE}  s₆ go
          where
          go : PRE ⇒ A₃
          go s x rewrite ConjunctionComm
                           (evalExp (𝒙 =̌= 𝑐𝑜𝑛𝑠𝑡 𝑿) s )
                           (evalExp (𝒚 =̌= 𝑐𝑜𝑛𝑠𝑡 𝒀) s )
                 = subst (λ p → s ⊨ p ) (sym s₄) x


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
