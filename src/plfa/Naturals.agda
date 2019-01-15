module plfa.Naturals where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ = refl

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + (m * n)

_^_ : ℕ → ℕ → ℕ
n ^ 0       = 1
n ^ (suc m) = n * (n ^ m)

_ : 3 ^ 4 ≡ 81
_ = refl

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero  = m
zero  ∸ suc n = zero
suc m ∸ suc n = m ∸ n

_ : 5 ∸ 3 ≡ 2
_ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

_ : 3 ∸ 5 ≡ 0
_ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎

infixl 6 _+_ _∸_
infixl 7 _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

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

_ : inc (x0 nil) ≡ x1 nil
_ = refl

_ : inc (x1 nil) ≡ x0 x1 nil
_ = refl

_ : inc (x0 x1 nil) ≡ x1 x1 nil
_ = refl

_ : inc (x1 x1 nil) ≡ x0 x0 x1 nil
_ = refl

_ : inc (x0 x0 x1 nil) ≡ x1 x0 x1 nil
_ = refl

_ : inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil
_ = refl

to : ℕ → Bin
to zero = x0 nil
to (suc x) = inc (to x)

from : Bin → ℕ
from nil = 0
from (x0 x) = 2 * (from x)
from (x1 x) = 1 + 2 * (from x)

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) = 
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎


idemLemma : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
idemLemma nil = refl
idemLemma (x0 b) = refl
idemLemma (x1 b) = 
  begin
    from (inc b) + (from (inc b) + zero)
  ≡⟨ cong (from (inc b) +_ ) (+-identityʳ (from (inc b))) ⟩
     from (inc b) + from (inc b)
  ≡⟨ cong (from (inc b) +_ ) (idemLemma b) ⟩
     from (inc b) + suc (from b)
  ≡⟨ cong (_+ (suc (from b))) (idemLemma b) ⟩
     suc (from b) + suc (from b)
  ≡⟨⟩
    {!!}
    

toCompfromIdem : ∀(n : ℕ) → (from (to n)) ≡ n
toCompfromIdem zero = refl
toCompfromIdem (suc n) =
  begin
    from (to (suc n))
  ≡⟨⟩
    from (inc (to n))
  ≡⟨ (idemLemma (to n)) ⟩
    suc (from (to n))
  ≡⟨ cong suc (toCompfromIdem n) ⟩
    suc n
  ∎
   
