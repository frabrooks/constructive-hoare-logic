
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; sym )
open import Relation.Nullary using (  yes ; no ; ¬_ ) 
open import Data.Maybe using (Maybe ; map ; ap ; _>>=_ ; Is-just ; nothing)
open import Data.Empty using (⊥ ; ⊥-elim )
open import Data.Product using ( Σ ; _,_ )
open import Function using ( _∘_ )
open import Data.Bool

module Misc where

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

  {-
  counterExample : ∀ {ℓ} {A B : Set ℓ} {a b d : A} { f : A → A }
                   → ( b ≡ d → ⊥ ) → ((a : A) → ( f a ≡ b )) → Σ A ((d ≡_) ∘ f) → ⊥
  counterExample ¬eq ∀a (fst , snd) rewrite snd = ⊥-elim (¬eq (sym (∀a fst)))


  counter' : ∀ {ℓ} {A : Set ℓ} {P : A → Set} → ((a : A) → P a) → Σ A (λ a → (P a → ⊥)) → ⊥
  counter' {_} {A} {P} p (fst , snd) = ⊥-elim (snd (p fst))
  -}

  -- Isomorphism
  infix 0 _≃_
  record _≃_ (A B : Set) : Set where
    field
      to   : A → B
      from : B → A
      from∘to : ∀ (x : A) → from (to x) ≡ x
      to∘from : ∀ (y : B) → to (from y) ≡ y

  open _≃_ public
