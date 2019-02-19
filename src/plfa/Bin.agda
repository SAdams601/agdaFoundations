module plfa.Bin where
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import plfa.Induction using (+-*-suc)
open import plfa.Isomorphism using (_≲_)

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

-- "0" = inc (x0 nil) => (x1 nil)
-- "1" = inc (x1 nil) => (x0 x1 nil)
-- "2" = inc (x0 x1 nil) => (x1 x1 nil)
-- "3" = inc (x1 x1 nil) => (x0 x0 x1 nil)

inc : Bin → Bin
inc nil = x1 nil
inc (x1 x) = x0 (inc x)
inc (x0 x) = x1 x

to : ℕ → Bin
to zero = x0 nil
to (suc x) = inc (to x)

from : Bin → ℕ
from nil = 0
from (x0 x) = 2 * (from x)
from (x1 x) = 1 + 2 * (from x)

fromInc-suc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
fromInc-suc nil = refl
fromInc-suc (x0 b) = refl
fromInc-suc (x1 b) = 
  begin
    from (inc (x1 b))
  ≡⟨⟩
    from (x0 (inc b))
  ≡⟨⟩
     2 * (from (inc b))
  ≡⟨ cong (2 *_) (fromInc-suc b) ⟩
    2 * suc (from b)
  ≡⟨ +-*-suc (from b) 2 ⟩
     2 + 2 * (from b)
  ∎

--to-from-id : ∀ (b : Bin) → to (from b) ≡ b
{-
  Not true because

  to (from nil) ≡ x0 nil
-}

from-to-id : ∀(n : ℕ) → from (to n) ≡ n
from-to-id zero = refl
from-to-id (suc n) = 
  begin
    from (to (suc n))
  ≡⟨⟩
    from (inc (to n))
  ≡⟨ fromInc-suc (to n) ⟩
    suc (from (to n))
  ≡⟨ cong suc (from-to-id n) ⟩
    suc n
  ∎


ℕ≲Bin : ℕ ≲ Bin
ℕ≲Bin =
  record
    { to      = to
    ; from    = from
    ; from∘to = from-to-id
    }

--The isomorphism ℕ≃Bin is not possible because to∘from
--is not possible since to (from nil) ≡ x0 nil

data One : Bin → Set
data Can : Bin → Set


data Can where

  zero : Can (x0 nil)
  can : ∀ {b : Bin} → One b → Can b

data One where

  one :
    One (x1 nil) 

  rex0 : ∀ {b : Bin} → One b → One (x0 b)
  rex1 : ∀ {b : Bin} → One b → One (x1 b)
  

incCan : ∀ {b : Bin} → Can b → Can (inc b)
incOne : ∀ {b : Bin} → One b → One (inc b)

incOne one = rex0 one
incOne (rex0 o) = rex1 o
incOne (rex1 o) = rex0 (incOne o)

incCan zero = can one
incCan {b} (can x) = can (incOne x)


toCan : ∀ (n : ℕ) → Can (to n)
toCan zero = zero
toCan (suc n) = incCan (toCan n)

postulate
  toFromOne : ∀ {b : Bin} → One b → to (from b) ≡ b


toFromCan : ∀ {b : Bin} → Can b → to (from b) ≡ b

{-
toFromOne one = refl
toFromOne ob with incOne ob
toFromOne one | p = refl
toFromOne (rex0 ob) | p = toFromOne {!!}
toFromOne (rex1 ob) | p = toFromOne {!!}
-}

toFromCan zero = refl
toFromCan (can x) = toFromOne x

open import plfa.Isomorphism using (_≃_;extensionality)
open import plfa.Quantifiers using (⟨_,_⟩;∃-syntax;∃-elim)

to-CanBin : ℕ → ∃[ b ](Can b)
to-CanBin x = ⟨ (to x) , (toCan x) ⟩

from-CanBin : ∃[ b ](Can b) → ℕ
from-CanBin = λ { x → ∃-elim (λ b _ → from b) x }

postulate 
  to∘from-lemma :  ∀ (y : ∃-syntax (λ b₁ → Can b₁))
    → (to-CanBin) (from-CanBin y) ≡ y

canBin-Iso-ℕ :  ℕ ≃ (∃[ b ] (Can b))
canBin-Iso-ℕ = record
  { to      = to-CanBin
  ; from    = from-CanBin
  ; from∘to = λ x → from-to-id x
  ; to∘from = to∘from-lemma
  }
