


module List-Patterns where

  open import Data.List as List using (_∷_ ; [] )

  pattern [_] z = z ∷ []
  pattern [_؛_] y z = y ∷ z ∷ []
  pattern [_؛_؛_] x y z = x ∷ y ∷ z ∷ []
  pattern [_؛_؛_؛_] w x y z = w ∷ x ∷ y ∷ z ∷ []
  pattern [_؛_؛_؛_؛_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
  pattern [_؛_؛_؛_؛_؛_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []






