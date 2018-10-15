module basics.list where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import basics.nat
open import basics.bool
data 𝕃 {ℓ} (A : Set ℓ) : Set ℓ where
  [] : 𝕃 A
  _∷_ : (x : A) (xs : 𝕃 A) → 𝕃 A

length : ∀{ℓ}{A : Set ℓ} → 𝕃 A → ℕ
length [] = 0
length (x ∷ xs) = suc (length xs)

_++_ : ∀ {ℓ} {A : Set ℓ} → 𝕃 A → 𝕃 A → 𝕃 A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → 𝕃 A → 𝕃 B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

filter : ∀ {ℓ}{A : Set ℓ} → (A → 𝔹) → 𝕃 A → 𝕃 A
filter p [] = []
filter p (x ∷ xs) = let r = filter p xs in
                     if p x then x ∷ r else r

