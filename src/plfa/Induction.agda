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
    suc ((m + n) + n * m)
  ≡⟨ cong suc (cong (_+ n * m) (+-comm m n)) ⟩
    suc (n + m + n * m)
  ≡⟨⟩
    {!suc (n + suc n * m)
  ≡⟨⟩
    ?!} 

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
