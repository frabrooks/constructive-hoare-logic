open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Level
open import Data.Maybe using (Maybe ; map ; ap ; _>>=_ )
open import Agda.Builtin.Unit

module operators where

  infixl 18 _<$>⟨_⟩_
  _<$>⟨_⟩_ : {ℓ : Level} → { F : Set ℓ → Set ℓ } → {A B : Set ℓ}
                         → (A → B)
                         → (RawFunctor {ℓ} F )
                         → F A → F B
  f <$>⟨ funRec ⟩ m  = (funRec RawFunctor.<$> f) m


  infixl 18 _⊛⟨_⟩_
  _⊛⟨_⟩_ : {ℓ : Level} → { F : Set ℓ → Set ℓ } → {A B : Set ℓ}
                       → F (A → B)
                       → (RawApplicative {ℓ} F )
                       → F A → F B
  mf ⊛⟨ appRec ⟩ mg  = (appRec RawApplicative.⊛ mf) mg

  infix 18 _>>=⟨_⟩_
  _>>=⟨_⟩_ : {ℓ : Level} → { F : Set ℓ → Set ℓ} → {A B : Set ℓ}
                         → F A
                         → (RawMonad {ℓ} F)
                         → (A → F B) → F B
  ma >>=⟨ monRec ⟩ a→mb = (monRec RawMonad.>>= ma) a→mb 

  infixl 18 _<$>ₘ_
  _<$>ₘ_ : {A B : Set} → (A → B) → Maybe A → Maybe B
  f <$>ₘ m = map f m

  infixl 18 _⊛ₘ_
  _⊛ₘ_ : {A B : Set} → Maybe (A → B) → Maybe A → Maybe B
  f ⊛ₘ m = ap f m

  infixl 18 _>>=ₘ_
  _>>=ₘ_ : {A B : Set} → Maybe A → ( A → Maybe B ) → Maybe B
  ma >>=ₘ a→mb = ma >>= a→mb 
