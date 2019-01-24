module plfa.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = 
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p = 
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p)⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

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


+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = 
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n = 
  begin
    (suc m) + (suc n)
  ≡⟨⟩
    suc (m + (suc n))
  ≡⟨ cong suc (+-suc m n) ⟩
     suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = 
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) = 
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    m + (n + p) + q
  ∎

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc m n p) | +-comm m n | +-assoc n m p = refl

*-distrib-+ : ∀(m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p = 
  begin
    (suc m + n) * p
  ≡⟨⟩
    p + (m + n) * p
  ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    (p + m * p) + n * p
  ≡⟨⟩
    suc m * p + n * p
  ∎

*-assoc : ∀(m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p = 
  begin
    (suc m * n) * p
  ≡⟨⟩  
    (n + m * n) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    (n * p) + (m * n * p)
  ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
    (n * p) + (m * (n * p))
  ≡⟨⟩
    suc m * (n * p)
  ∎

*-zero : ∀(n : ℕ) → n * zero ≡ zero
*-zero zero = refl
*-zero (suc n) = 
  begin
    (suc n) * zero
  ≡⟨⟩
    zero + n * zero
  ≡⟨ cong (zero +_) (*-zero n) ⟩
    zero + zero
  ≡⟨⟩
    zero
  ∎

+-*-suc : ∀(m n : ℕ) → n * suc m ≡ n + n * m
+-*-suc m zero = refl
+-*-suc m (suc n) = 
  begin
    suc n * suc m
  ≡⟨⟩
    suc (m + n * suc m)
  ≡⟨ cong suc (cong (m +_) (+-*-suc m n)) ⟩
    suc (m + (n + n * m))
  ≡⟨ cong suc (sym (+-assoc m n (n * m))) ⟩
    suc (m + n + n * m)
  ≡⟨ cong (λ x → suc ( x + n * m)) (+-comm m n) ⟩
    suc (n + m + n * m)
  ≡⟨ cong suc (+-assoc n m (n * m)) ⟩
     suc (n + (m + n * m))
  ≡⟨⟩
    suc n + suc n * m
  ∎

*-comm : ∀(m n : ℕ) → m * n ≡ n * m
*-comm zero n = 
  begin
    zero * n
  ≡⟨⟩
    zero
  ≡⟨ sym (*-zero n) ⟩
    n * zero
  ∎
*-comm (suc m) n = 
  begin
    suc m * n
  ≡⟨⟩
    n + m * n
  ≡⟨ cong (n +_) (*-comm m n) ⟩
    n + n * m
  ≡⟨ sym (+-*-suc m n) ⟩
    n * suc m
  ∎ 

0∸n≡0 : ∀(n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero = refl
0∸n≡0 (suc x) = refl 

∸-+-assoc : ∀(m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m n zero = 
  begin
    m ∸ n ∸ zero
  ≡⟨⟩
    m ∸ n
  ≡⟨⟩
    m ∸ (zero + n)
  ≡⟨ cong (m ∸_) (+-comm zero n) ⟩
   m ∸ (n + zero)
  ∎
∸-+-assoc zero zero (suc p) = refl
∸-+-assoc (suc m) zero (suc p) = refl
∸-+-assoc zero (suc n) (suc p) = refl
∸-+-assoc (suc m) (suc n) (suc p) = ∸-+-assoc m n (suc p)

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

--+-*-suc : ∀(m n : ℕ) → n * suc m ≡ n + n * m


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


--is can x1 x1 x0 x1 nil
--not ca x1 x1 x0 x1 x0 x0 nil

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
incOne {x0 x} (rex0 b) = incOne {!!}
incOne {x1 x} (rex1 b) = incOne {!!}

incCan zero = can one
incCan {b} (can x) = can (incOne x)


toCan : ∀ (n : ℕ) → Can (to n)
toCan zero = zero
toCan (suc n) = incCan (toCan n)

toFromCan : ∀ {b : Bin} → Can b → to (from  b) ≡ b
toFromCan zero = refl
toFromCan {.(x1 nil)} (can one) = refl
toFromCan {.(x0 _)} (can (rex0 x)) = {!!}
toFromCan {.(x1 _)} (can (rex1 x)) = {!!}
