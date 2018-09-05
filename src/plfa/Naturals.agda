module plfa.Naturals where


data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

seven = suc (suc (suc (suc (suc (suc (suc zero))))))

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
{-
_+_ : ℕ → ℕ → ℕ
zero    + n = n
(suc m) + n = suc (m + n)
-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

2plus3 : 2 + 3 ≡ 5
2plus3 =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

2plus3Simp : 2 + 3 ≡ 5
2plus3Simp = refl

  
+-example :  3 + 4 ≡ 7
+-example =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc 4))
  ≡⟨⟩
    suc (suc 5)
  ≡⟨⟩
    suc 6
  ≡⟨⟩
    7
  ∎

_*_ : ℕ → ℕ → ℕ
zero    * n = zero
(suc m) * n = n + (m * n)
  
2times3 =
  begin
    2 * 3
  ≡⟨⟩
    3 + (1 * 3)
  ≡⟨⟩
    3 + (3 + (0 * 3))
  ≡⟨⟩
    3 + (3 + 0)
  ≡⟨⟩
    6
  ∎

3times4 =
  begin
    3 * 4
  ≡⟨⟩
    3 + (3 * 3)
  ≡⟨⟩
    3 + (3 + (2 * 3))
  ≡⟨⟩
    3 + (3 + (3 + (1 * 3)))
  ≡⟨⟩
    3 + (3 + (3 + (3 + (0 * 3))))
  ≡⟨⟩
    3 + (3 + (3 + (3 + 0)))
  ≡⟨⟩
    3 + (3 + (3 + 3))
  ≡⟨⟩
    3 + (3 + 6)
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    12
  ∎

_^_ : ℕ → ℕ → ℕ
n ^ 0       = 1
n ^ (suc m) = n * (n ^ m)

3to4 : 3 ^ 4 ≡ 81
3to4 = refl

_∸_ : ℕ → ℕ → ℕ
m       ∸ zero    = m
zero    ∸ (suc n) = zero
(suc m) ∸ (suc n) = m ∸ n

3sub2 =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

2sub3 =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎

5sub3 =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ∎

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

inc : Bin → Bin
inc nil = x1 nil
inc (x0 b) = x1 (inc b)
inc (x1 b) = x1 (inc b)

to : ℕ → Bin
to zero    = x0 nil
to (suc x) = inc (to x)

{-
_ : to 2 ≡ x1 x0 nil
_ = {!refl!}
-}
