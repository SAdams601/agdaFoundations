module plfa.Equality where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_


sym : ∀ {A : Set} {x y : A}
  → x ≡ y
  ---------
  → y ≡ x
sym refl = refl


