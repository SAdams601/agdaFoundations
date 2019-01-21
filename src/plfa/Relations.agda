module plfa.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties using (+-comm; +-suc; *-comm)
open import Data.List using (List; []; _∷_)
open import Function using (id; _∘_)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)


data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
    -------------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
    ----------------
    → suc m ≤ suc n

infix 4 _≤_

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)


≤-refl : ∀ {n : ℕ}
  ------
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s (≤-refl {n})


≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
  --------
  → m ≤ p
  
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
  ---------
  → m ≡ n

≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

data Total (m n : ℕ) : Set where

  forward :
    m ≤ n
    ---------
    → Total m n

  flipped :
    n ≤ m
    --------
    → Total m n

≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                     | forward m≤n = forward (s≤s m≤n)
...                     | flipped n≤m = flipped (s≤s n≤m)



+-monoʳ-≤ : ∀ (m p q : ℕ)
  → p ≤ q
  ----------------
  → m + p ≤ m + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc m) p q p≤q = s≤s (+-monoʳ-≤ m p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
  ----------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
  ----------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)


*-monoʳ-≤ : forall (m p q : ℕ)
  → p ≤ q
  --------------
  → m * p ≤ m * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc m) p q p≤q = +-mono-≤ p q (m * p) (m * q) p≤q (*-monoʳ-≤ m p q p≤q)

*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
  -----------
  → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p  = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
  ----------------
  → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
   ----------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
    ----------------
    → suc m < suc n

{-
  Transitivity :

      m < n
      n < p
    ----------
      m < p
-}

<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
  --------
  → m < p
<-trans z<s (s<s _)  = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)   

{-
 trochotomy
 m < n or
 m ≡ n or
 m > n
-}

data Trichotomy (m n : ℕ) : Set where
  equals :
    m ≡ n
    -------
    → Trichotomy m n

  m<n :
    m < n
    -----------------
    → Trichotomy m n

  n<m :
    n < m
    -----------------
    → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero zero = equals refl
<-trichotomy zero (suc n) = m<n z<s
<-trichotomy (suc m) zero = n<m z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n
...     | equals p = equals (cong suc p)
...     | m<n    p = m<n (s<s p)
...     | n<m    p = n<m (s<s p)


+-monoʳ-< : ∀ (m p q : ℕ)
            → p < q
            ----------------
            → m + p < m + q
+-monoʳ-< zero p q pltq = pltq
+-monoʳ-< (suc m) p q pltq = s<s (+-monoʳ-< m p q pltq)

+-monoˡ-< : ∀ (m n p : ℕ)
            → m < n
            ----------------
            → m + p < n + p
+-monoˡ-< m n p mltn rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n mltn

+-mono-< : ∀ (m n p q : ℕ)
           → m < n
           → p < q
           --------
           → m + p < n + q
+-mono-< m n p q mltn pltq = <-trans (+-monoˡ-< m n p mltn) (+-monoʳ-< n p q pltq)

≤-iff-< : ∀ (m n : ℕ) → suc m ≤ n → m < n
≤-iff-< zero n (s≤s prf) = z<s
≤-iff-< (suc m) (suc n) (s≤s prf) = s<s (≤-iff-< m n prf)

<-iff-≤ : ∀ (m n : ℕ) → m < n → suc m ≤ n
<-iff-≤ zero zero ()
<-iff-≤ (suc m) zero ()
<-iff-≤ zero (suc n) prf = s≤s z≤n
<-iff-≤ (suc m) (suc n) (s<s prf) with <-iff-≤ m n prf
...            | s≤s prf2 = s≤s (s≤s prf2)


-- Want to prove transitivity through the relationship between strict inequality and inequality
--≤-trans : ∀ {m n p : ℕ}  → m ≤ n → n ≤ p → m ≤ p

<-iff-≤' : ∀ (m n : ℕ) → m < n → m ≤ n
<-iff-≤' zero zero ()
<-iff-≤' zero (suc n) z<s = z≤n
<-iff-≤' (suc m) zero ()
<-iff-≤' (suc m) (suc n) prf = s≤s (<-iff-≤' m n {!prf!})

<-trans-revisited : ∀ (m n p : ℕ)
  → m < n
  → n < p
  --------
  → m < p
<-trans-revisited zero n p z<s (s<s _) = ≤-iff-< zero p (s≤s z≤n)
<-trans-revisited (suc m) zero p () nltp
<-trans-revisited (suc m) (suc n) zero _ ()
<-trans-revisited (suc m) (suc n) (suc p) mltn (s<s nltp) =

  -- trans : suc (suc m) ≤ suc p
    -- 1st - 
  let
    mltn' = (<-iff-≤ (suc m) (suc n) mltn)
  in
  ≤-iff-< (suc m) (suc p) (≤-trans mltn' (<-iff-≤' (suc n) (suc p) (s<s nltp)))
