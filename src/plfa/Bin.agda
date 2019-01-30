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
