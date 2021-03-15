{-# OPTIONS --allow-unsolved-metas #-}


-- Module for Store and Heap simple representation as List
------------------------------------------------------------------

-- Lib imports
open import Relation.Binary.Definitions using ( Decidable )
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym )
open import Relation.Nullary.Decidable using (False ; True ; isYes ; isNo ; ⌊_⌋ )
open import Relation.Nullary using ( yes ; no ; ¬_ )
open import Data.Maybe using (Maybe)
open import Data.Bool using ( true ; false)
open import Data.List as List using (List; _∷_; [] ; map ; _++_ )
open import Data.Maybe using (Maybe ; nothing ; just )
open import Data.Product
open import Data.Empty


-- Local imports
open import Representation.Data using (D-Representation)
open import List-Patterns


module State-List-Rep (dRep : D-Representation) where

  open D-Representation dRep

  S = List (Id × Val)
  -- H = ?
  ● : S
  ● = []

  updateState : Id → Val → S → S
  updateState i z  []  = [ ( i , z ) ]
  updateState i e ((fst , snd) ∷ zs)  with fst ?id= i
  ...                                 | yes _ = (i , e) ∷ zs
  ...                                 | no _ = (fst , snd ) ∷ updateState i e zs
  

  getVarVal : Id → S → Maybe Val
  getVarVal i [] = nothing
  getVarVal i ((fst , snd) ∷ zs) with ⌊ i ?id= fst ⌋
  ...                                 | true =  just snd 
  ...                                 | false = getVarVal i zs


  dropValue : S → Id → S
  dropValue []  _  = []
  dropValue ((fst , snd) ∷ s) id with ⌊ fst ?id= id ⌋
  ... | true  = s
  ... | false = (fst , snd) ∷ (dropValue s id)


  data hasVarVal : Id → Val → S → Set where
    atthehead : ∀ i z s → hasVarVal i z ((i , z) ∷ s)
    elsewhere : ∀ i j z w s s' → i ≡ j → ⊥ → hasVarVal i z s → s' ≡ ((j , w) ∷ s ) → hasVarVal i z s'
  
  private removeFromTop : ∀ i x w s  → (¬ i ≡ x ) → getVarVal i ((x , w ) ∷  s ) ≡ getVarVal i s
  removeFromTop i x w s n with i ?id= x
  ... | yes p  = ⊥-elim (n p)
  removeFromTop i x w []      n | no _ = refl
  removeFromTop i x w (_ ∷ s) n | no _ = refl

  private getFromTop :  ∀ i x w s  → ( i ≡ x ) → getVarVal i ((x , w ) ∷  s ) ≡ just w
  getFromTop i x w s p with i ?id= x
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p p)


  updateGet : ∀ i v s → getVarVal i (updateState i v s) ≡ just v
  updateGet i v [] with i ?id= i
  ... | yes p = refl
  ... | no ¬p = ⊥-elim (¬p refl)
  updateGet i v ( (x , w )  ∷ s) with x ?id= i
  updateGet i v ( (x , w )  ∷ s) | yes p with i ?id= i
  updateGet i v ( (x , w )  ∷ s) | yes p | yes q = refl
  updateGet i v ( (x , w )  ∷ s) | yes p | no ¬q = ⊥-elim (¬q refl)
  updateGet i v ( (x , w )  ∷ s) | no ¬p with i ?id= x
  updateGet i v ( (x , w )  ∷ s) | no ¬p | yes q = ⊥-elim (¬p (sym q))
  updateGet i v ( (x , w )  ∷ s) | no ¬p | no ¬q = updateGet i v s


  irrelUpdate : ∀ i x v y → ¬ i ≡ x → (s : S) →  getVarVal x (updateState i v s) ≡ y → getVarVal x s ≡ y
  irrelUpdate i x v y n [] pr with x ?id= i
  ... | yes p = ⊥-elim (n (sym p))
  ... | no ¬p = pr
  irrelUpdate i x v y n ((fst , snd) ∷ s) pr with x ?id= fst | fst ?id= i 
  ... | yes p | yes p₁ rewrite p = ⊥-elim (n (sym p₁))
  ... | yes p | no ¬p  rewrite p | getFromTop fst fst snd (updateState i v s) refl  = pr
  ... | no ¬p | yes p  rewrite p | removeFromTop x i v s ¬p =  pr
  ... | no ¬p | no ¬p₁ rewrite     removeFromTop x fst snd (updateState i v s) ¬p
                                   = irrelUpdate i x v y n s pr


  nothingRec : ∀ x i v s → getVarVal x (updateState i v s) ≡ nothing → getVarVal x s ≡ nothing
  nothingRec x i v [] p = refl
  nothingRec x i v ((fst , snd) ∷ s) pr with x ?id= fst | fst ?id= i
  nothingRec x i v ((fst , snd) ∷ s) pr | yes p | yes q rewrite p | q with i ?id= i 
  ... | no ¬p = ⊥-elim (¬p refl)
  nothingRec x i v ((fst , snd) ∷ s) pr | yes p | no ¬q rewrite p with fst ?id= fst
  ... | no ¬p = ⊥-elim (¬p refl)
  nothingRec x i v ((fst , snd) ∷ s) pr | no ¬p | yes q rewrite q | removeFromTop x i v s ¬p = pr
  nothingRec x i v ((fst , snd) ∷ s) pr | no ¬p | no ¬q rewrite removeFromTop x fst snd (updateState i v s) ¬p
                                                                = nothingRec x i v s pr


  hasValueSame : ∀ x y f s → hasVarVal x y (updateState x f s) → y ≡ f
  hasValueSame x y f s hv =  aux x y f s (updateState x f s) refl hv
    where
    aux : ∀ x y f s s' → s' ≡ (updateState x f s) → hasVarVal x y s' → y ≡ f
    aux x y .y [] .([ (x , y) ]) refl (atthehead .x .y .[]) = refl
    aux x y f (x₁ ∷ s) .((x , y) ∷ s₁) w (atthehead .x .y s₁) with proj₁ x₁ ?id= x
    aux x y .y (x₁ ∷ s) ((.x , .y) ∷ .s) refl (atthehead .x .y .s) | yes _ = refl
    aux x y f (.(x , y) ∷ s) ((.x , .y) ∷ .(updateState x f s)) refl (atthehead .x .y .(updateState x f s)) | no p = ⊥-elim (p refl)


  hasValueDiff : ∀ x x' y f s → ¬ x ≡ x' → hasVarVal x y (updateState x' f s) → hasVarVal x y s
  hasValueDiff x x' y f s d hv =  aux x x' y f s (updateState x' f s) d refl hv
    where
    aux : ∀ x x' y f s s' → ¬ x ≡ x' → s' ≡ (updateState x' f s) → hasVarVal x y s' → hasVarVal x y s
    aux x .x y .y [] .([( x , y )]) d refl (atthehead .x .y .[]) = ⊥-elim (d refl)
    aux x x' y f ((fst , snd) ∷ s) .((x , y) ∷ s₁) d e (atthehead .x .y s₁) with fst ?id= x'
    aux .x' x' y .y ((fst , snd) ∷ s) ((.x' , .y) ∷ .s) d refl (atthehead .x' .y .s)
      | yes p = ⊥-elim (d refl)
    aux .fst x' y f ((fst , .y) ∷ s) ((.fst , .y) ∷ .(updateState x' f s)) d refl (atthehead .fst .y .(updateState x' f s))
      | no p = atthehead fst y s


  updateState¬● : ∀ i f s → updateState i f s ≡ ● → ⊥
  updateState¬● i f ((fst , snd) ∷ s) p with (fst ?id= i) | p
  ...                        | yes _  | ()
  ...                        | no  _  | ()


