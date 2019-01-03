module agdaStructures.flipper where
open import Data.Product
open import Data.Bool

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{- record Flipper : Set where
  constructor _&_
  field
    space : ℕ
    val   : ℕ

suc-flip : Flipper → Flipper × Bool
suc-flip (zero & n) = (suc n & zero), true
suc-flip (suc m & n) = (m & suc n), false
-}

data Val (base : ℕ) : ℕ → Set where
  zero-case : Val base base
  suc-case  : ∀ {space} → Val base (suc space) → Val base space

record Flipper (base : ℕ) : Set where
  constructor _&_
  field
    space : ℕ
    val : Val base space

suc-flip : ∀ {n} → Flipper n → Flipper n × Bool
suc-flip (zero & val) = (_ & zero-case) , true
suc-flip (suc space & val) = (space & suc-case val), false

