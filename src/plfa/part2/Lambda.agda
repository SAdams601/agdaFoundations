module plfa.part2.Lambda where

open import Relation.Binary.PropositionalEquality using(_≡_; _≢_; refl)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List using (List; _∷_; [])

Id : Set
Id = String

infix 5 ƛ_⇒_
infix 5 μ_⇒_
infix 7 _·_
infix 8 ‵suc_
infix 9 ‵_

data Term : Set where
  ‵_                   : Id → Term
  ƛ_⇒_                 : Id → Term → Term
  _·_                  : Term → Term → Term
  ‵zero                : Term
  ‵suc_                : Term → Term
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
  μ_⇒_                 : Id → Term → Term

two : Term
two = ‵suc ‵suc ‵zero

plus : Term
plus = μ "+" ⇒
    ƛ "m"
  ⇒ ƛ "n"
  ⇒ case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒ ‵suc (‵ "+" · (‵ "m" · ‵ "n")) ]

twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ‵ "s" · (‵ "s" · ‵ "z")

plusᶜ : Term
plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
  ‵ "m" · (‵ "s" · (‵ "n" · (‵ "s" · ‵ "z")))

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ ‵suc (‵ "n")

mul : Term
mul = μ "*" ⇒ (ƛ "m" ⇒ ƛ "n" ⇒ case ‵ "m" [zero⇒ ‵zero |suc "m" ⇒ plus · (‵ "n" · (‵ "*" · (‵ "m" · ‵ "n"))) ])

four : Term
four = mul · (two · two)

ƛ′_⇒_ : Term → Term → Term
ƛ′ (‵ x) ⇒ N = ƛ x ⇒ N
ƛ′ _ ⇒ _ = ⊥-elim impossible
  where posulate impossible : ⊥

