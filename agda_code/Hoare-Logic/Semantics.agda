
-- Lib Imports
open import Data.Product using (Σ ; Σ-syntax ; _×_  ; _,_  ; proj₁ ; proj₂ )
open import Data.Maybe using ( Maybe ; just ; nothing ; _>>=_ ; Is-just ; to-witness )

-- Project Imports
open import Representation.Data using (D-Representation)
open import Representation.State using (S-Representation)


module Hoare-Logic.Semantics (dRep : D-Representation )
  (sRep : S-Representation dRep ) where

  open D-Representation dRep
  open S-Representation sRep

  open import Mini-C.Expressions dRep sRep
  open import Assertions.Props dRep sRep

  open import Mini-C.Lang dRep sRep

  open import Hoare-Logic.Termination dRep sRep


--  data Π (A : Set) (B : A → Set) : Set where
--    Λ : ((a : A) → B a) → Π A B


  WP : S → 𝐶 → 𝑃 → Set
  WP s C P = ( s' : S ) →  Eval s C s' → ( P ← s' )
--  WP C P = Σ[ s ∈ S ] Π S (λ s' → Eval s C s' → ( P ← s' ))


  -- Hoare's Notation: {P}C{Q}   P → wp C P   ( Partial Correctness )
  ⟪_⟫_⟪_⟫ :  𝑃 → 𝐶 → 𝑃 → Set
  ⟪ P ⟫ C ⟪ Q ⟫ = ( s : S ) → ( P ← s ) → WP s C Q

  -- Total Correctness 
  ⟦_⟧_⟦_⟧ :  𝑃 → 𝐶 → 𝑃 → Set
  ⟦ P ⟧ C ⟦ Q ⟧ = Σ[ s ∈ S ] Terminates C s ×  ⟪ P ⟫ C ⟪ Q ⟫ 


  




  -- Π S (λ(s : S) → ( P ← s ) × Terminates C s s' → ( Q ← s' ) )


  --              P ⇒ wp( C , Q ) 
  --              i.e. P = X = 6
  --                   wp = X != 0
  --                 ∴  P → wp 
  --
  --              Terminates → eval C P s = s' → Q s'











