
import Relation.Binary.PropositionalEquality as Eq
open Eq using ( _≡_ ; refl ; sym ; subst ; cong)
open import Relation.Nullary using (  yes ; no ; ¬_ ) 
open import Data.Maybe using (Maybe ; map ; ap ; _>>=_ ; Is-just ; nothing ; just ; to-witness)
open import Data.Maybe.Relation.Unary.Any using (Any )
open import Data.Empty using (⊥ ; ⊥-elim )
open import Data.Product using ( Σ ; _,_ )
open import Function using ( _∘_ )
open import Data.Bool
open import Data.Nat using (ℕ ; suc ; zero ; _≤″_ ; less-than-or-equal)
open _≤″_
open import Data.Nat.Properties using ( +-comm )
open import Level using (Level )

module Misc where

  pattern any tt = Any.just tt

  Is-just-just : {l : Level} {A : Set l} {a : A} (p : Is-just (just a)) → to-witness p ≡ a
  Is-just-just (Any.just x) = refl

  Is-just-nothing : {l : Level} {A : Set l} → Is-just {l} {A} nothing → ⊥
  Is-just-nothing ()

  suc≤″ : ∀ {x} {y} → x ≤″ y → x ≤″ suc y
  suc≤″ {x} {y} lt =
  
    -- Derive `x '≤″ suc y` from `x ≤″ y`
    
    let γ = (subst (_≡ y) (+-comm x (k lt)) (proof lt))
    --   (proof lt) : x + (k lt) ≡ y
    --  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ ● (+-commutativity)
    --      γ :  ((k lt) + x) ≡ y        
    in let ψ = cong suc γ
    --        γ :  ((k lt) + x) ≡ y
    --  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ ≡-congruence
    --    ψ : suc ((k lt) + x )  ≡ suc y 
    in let χ = subst (_≡ suc y) (+-comm (suc (k lt)) x) ψ
    --    ψ : suc ((k lt) + x )  ≡ suc y
    --  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ ● (+-commutativity)
    --     χ : x + suc (k lt) ≡ suc y  
    in less-than-or-equal χ

  sym¬ : ∀ {ℓ} {A : Set ℓ} {a : A} {b : A} → ¬ a ≡ b → ¬ b ≡ a
  sym¬ {A} {a} {b} p = λ x → ⊥-elim (p (sym x))

  Ij⊥ : ∀ {ℓ} {A : Set ℓ} → Is-just {ℓ} {A} nothing → ⊥
  Ij⊥ ()

  
  infixl 18 _<$>_
  _<$>_ : {A B : Set} → (A → B) → Maybe A → Maybe B
  f <$> m = map f m

  infixl 18 _<*>_
  _<*>_ : {A B : Set} → Maybe (A → B) → Maybe A → Maybe B
  f <*> m = ap f m

 
  -- Isomorphism
  infix 0 _≃_
  record _≃_ (A B : Set) : Set where
    field
      to   : A → B
      from : B → A
      
  open _≃_ public
