module basics.nat where
open import basics.bool
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

infixl 10 _*_
infixl 9 _+_
infixl 8 _<_ _=ℕ_ 

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

0+ : ∀ (x : ℕ) → 0 + x ≡ x
0+ x = refl

+0 : ∀ (x : ℕ) → x + 0 ≡ x
+0 zero = refl
+0 (suc x) rewrite +0 x = refl 

+assoc : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+assoc zero y z = refl
+assoc (suc x) y z rewrite +assoc x y z = refl

+suc : ∀ (x y : ℕ) → x + (suc y) ≡ suc(x + y)
+suc zero y = refl
+suc (suc x) y rewrite +suc x y = refl 

+comm : ∀ (x y : ℕ) → x + y ≡ y + x
+comm zero y rewrite +0 y = refl
+comm (suc x) y rewrite +suc y x | +comm x y = refl 

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + (m * n)

*distribr : ∀ (x y z : ℕ) → (x + y) * z ≡ (x * z) + (y * z)
*distribr zero y z = refl
*distribr (suc x) y z rewrite *distribr x y z = +assoc z (x * z) (y * z)

*0 : ∀ (x : ℕ) → x * 0 ≡ 0
*0 zero = refl
*0 (suc x) rewrite *0 x = refl

*suc : ∀ (x y : ℕ) → x * (suc y) ≡ x + x * y
*suc zero y = refl
*suc (suc x) y rewrite *suc x y | +assoc y x (x * y) | +assoc x y (x * y) | +comm y x = refl

*comm : ∀ (x y : ℕ) → x * y ≡ y * x
*comm zero y rewrite *0 y = refl
*comm (suc x) y rewrite *suc y x | *comm x y = refl 

*assoc : ∀ (x y z : ℕ) → x * (y * z) ≡ (x * y) * z
*assoc zero y z = refl
*assoc (suc x) y z rewrite *assoc x y z | *distribr y (x * y) z = refl

_<_ : ℕ → ℕ → 𝔹
0 < 0 = ff
0 < (suc y) = tt
(suc x) < (suc y) = x < y
(suc x) < 0 = ff

<-trans : ∀ {x y z : ℕ} → x < y ≡ tt → y < z ≡ tt → x < z ≡ tt
<-trans {zero} {zero} {zero} ()
<-trans {zero} {zero} {suc z} ()
<-trans {zero} {suc y} {zero} p1 ()
<-trans {zero} {suc y} {suc z} p1 p2 = refl
<-trans {suc x} {zero} {zero} ()
<-trans {suc x} {zero} {suc z} ()
<-trans {suc x} {suc y} {zero} p1 ()
<-trans {suc x} {suc y} {suc z} p1 p2 = <-trans {x} {y} {z} p1 p2

<-0 : ∀ (x : ℕ) → x < 0 ≡ ff
<-0 zero = refl
<-0 (suc x) = refl

𝔹-contra : ff ≡ tt → ∀ {P : Set} → P
𝔹-contra ()

_=ℕ_ : ℕ → ℕ → 𝔹
0     =ℕ 0 = tt
suc x =ℕ suc y = x =ℕ y
_     =ℕ _ = ff

=ℕ-refl : ∀ (x : ℕ) → (x =ℕ x) ≡ tt
=ℕ-refl zero = refl
=ℕ-refl (suc x) = =ℕ-refl x

=ℕ-to-≡ : ∀ {x y : ℕ} → x =ℕ y ≡ tt → x ≡ y
=ℕ-to-≡ {zero} {zero} p = refl
=ℕ-to-≡ {zero} {suc y} ()
=ℕ-to-≡ {suc x} {zero} ()
=ℕ-to-≡ {suc x} {suc y} p
  rewrite =ℕ-to-≡ {x} {y} p = refl 

=ℕ-from≡ : ∀ {x y : ℕ} → x ≡ y → x =ℕ y ≡ tt
=ℕ-from≡ {x} refl = =ℕ-refl x

is-even : ℕ → 𝔹
is-odd : ℕ → 𝔹
is-even 0 = tt
is-even (suc x) = is-odd x
is-odd 0 = ff
is-odd (suc x) = is-even x

even-odd : ∀ (x : ℕ) → is-even x ≡ ~ is-odd x
odd-even : ∀ (x : ℕ) → is-odd x ≡ ~ is-even x
even-odd zero = refl
even-odd (suc x) = odd-even x
odd-even zero = refl
odd-even (suc x) = even-odd x


