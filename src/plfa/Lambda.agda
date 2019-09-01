module plfa.Lambda where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String)
open import Data.String.Properties using (_≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (¬?)

Id : Set
Id = String

infix  5 ƛ_⇒_ 
infix  5 μ_⇒_
infixl 7 _·_
infix  8 `suc_
infix  9 `_

data Term : Set where
 `_                     : Id → Term
 ƛ_⇒_                  : Id → Term → Term
 _·_                    : Term → Term → Term
 `zero                  : Term
 `suc_                  : Term → Term
 case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
 μ_⇒_                  : Id → Term → Term

two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
        ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
          [zero⇒ `zero
          |suc "m" ⇒ plus · ` "n" · ( ` "*" · ` "m" · ` "n") ]

mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
   ` "m" · (plusᶜ · ` "m" · ` "n" · ` "s" · ` "z" )  

ƛ′_⇒_ : Term → Term → Term
ƛ′(` x) ⇒ N = ƛ x ⇒ N
ƛ′ _ ⇒ _ = ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ] = case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc _ ⇒ _ ]     = ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (` x) ⇒ N = μ x ⇒ N
μ′ _ ⇒ _     = ⊥-elim impossible
  where postulate impossible : ⊥

plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n) ]
        where
          + = ` "+"
          m = ` "m"
          n = ` "n"

mul′ : Term
mul′ = μ′ * ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ `zero
            |suc m ⇒ (plus′ · n · (* · m · n)) ]
          where
            * = ` "*"
            m = ` "m"
            n = ` "n"

data Value : Term → Set where

  V-ƛ : ∀ {x N}
  ---------------------
    → Value (ƛ x ⇒ N)

  V-zero :
  -------------
    Value `zero

  V-suc : ∀ {V}
    → Value V
  -------------
    → Value (`suc V)

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _           = V
... | no  _           = ` x 
(L · M) [ y := V ]    = L [ y := V ] · M [ y := V ]
(`zero) [ y := V ]    = `zero
(`suc M) [ y := V ]   = `suc M [ y := V ]
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          = ƛ x ⇒ N
... | no  _          = ƛ x ⇒ N [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _           = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _           =  case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _           = μ x ⇒ N
... | no _            = μ x ⇒ N [ y := V ] 

infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
    ------------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
      -----------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
      -------------------------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M —→ M′
    ---------------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
    ---------------------------------------------------------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
       -----------------------------------------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
       ------------------------------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
      ---------------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
     -------------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
      ---------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
    -------
  → M —↠ N
begin M—↠N = M—↠N

data _—↠′_ : Term → Term → Set where

  step′ : ∀ {M N}
    → M —→ N
      --------
    → M —↠′ N

  refl′ : ∀ {M}
    ----------
    → M —↠′ M

  trans′ : ∀ {L M N}
    → L —↠′ M
    → M —↠′ N
     ---------
    → L —↠′ N

open import plfa.Isomorphism using (_≲_;_≃_)

private
  —↠-trans : ∀ {L M N : Term} → L —↠ M → M —↠ N → L —↠ N
  —↠-trans {.M} (M ∎) N↠L = N↠L
  —↠-trans {L} (L —→⟨ x ⟩ L→M) N↠L = L —→⟨ x ⟩ —↠-trans L→M N↠L

—↠≲—↠′ : ∀ {M M′} → M —↠ M′ ≲ M —↠′ M′
—↠≲—↠′ {M} {N} = record { to = to ; from = from ; from∘to = from∘to }
  where
    to : ∀ {M N : Term} → M —↠ N → M —↠′ N
    to (M ∎) = refl′
    to (L —→⟨ x ⟩ M) = trans′ (step′ x) (to M)

    from : ∀ {M N : Term} → M —↠′ N → M —↠ N
    from {M} {N} (step′ x) = M —→⟨ x ⟩ N ∎
    from {M} {N} refl′ = M ∎
    from {M} {N} (trans′ M→L L→N) = —↠-trans (from M→L) (from L→N)

    from∘to : ∀ {M N : Term} (x : M —↠ N) → from (to x) ≡ x
    from∘to (M ∎) = refl
    from∘to (M —→⟨ M↠L ⟩ L↠N) rewrite from∘to L↠N = refl


infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ  : Type


infixl 5 _,_∶_

data Context : Set where
  ∅ : Context
  _,_∶_ : Context → Id → Type → Context

open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List; _∷_; [])

Context-≃ : Context ≃ List (Id × Type)
Context-≃ = record {to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from}
  where
    to : Context → List (Id × Type)
    to ∅ = []
    to (C , id ∶ type) = ⟨ id , type ⟩ ∷ to C

    from : List (Id × Type) → Context 
    from [] = ∅
    from (⟨ id , type ⟩ ∷ L) = (from L) , id ∶ type

    from∘to : (C : Context) → from (to C) ≡ C
    from∘to ∅ = refl
    from∘to (C₁ , id ∶ type) rewrite from∘to C₁ = refl

    to∘from : (L : List (Id × Type)) → to (from L) ≡ L
    to∘from [] = refl
    to∘from (⟨ id , type ⟩ ∷ L′) rewrite to∘from L′ = refl

infix 4 _∋_∶_

data _∋_∶_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
    --------------------
    → Γ , x ∶ A ∋ x ∶ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ∶ A
    -------------------
    → Γ , y ∶ B ∋ x ∶ A

infix 4 _⊢_∶_

data _⊢_∶_ : Context → Term → Type → Set where

  --Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ∶ A
     -----------
    → Γ ⊢ ` x ∶ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ∶ A ⊢ N ∶ B
      ------------------
    → Γ ⊢ ƛ x ⇒ N ∶ A ⇒ B
    
  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ∶ A ⇒ B
    → Γ ⊢ M ∶ A
    -----------------
    → Γ ⊢ L · M ∶ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
      -------------
    → Γ ⊢ `zero ∶ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ∶ `ℕ
    --------------
    → Γ ⊢ `suc M ∶ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ∶ `ℕ
    → Γ ⊢ M ∶ A
    → Γ , x ∶ `ℕ ⊢ N ∶ A
    ----------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ∶ A

  ⊢μ : ∀ {Γ x M A}
    → Γ , x ∶ A ⊢ M ∶ A
    -------------------
    → Γ ⊢ μ x ⇒ M ∶ A
  
_≠_ : ∀ (x y : Id) → x ≢ y
x ≠ y with x ≟ y
...      | no x≢y = x≢y
...      | yes _  = ⊥-elim impossible
  where postulate impossible : ⊥

Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

⊢twoᶜ : ∀ {Γ A} → Γ ⊢ twoᶜ ∶ Ch A
⊢twoᶜ = ⊢ƛ (⊢ƛ (⊢` ∋s · (⊢` ∋s · ⊢` ∋z)))
  where
    ∋s = S ("s" ≠ "z") Z
    ∋z = Z

⊢two : ∀ {Γ} → Γ ⊢ two ∶ `ℕ
⊢two = ⊢suc (⊢suc ⊢zero)

⊢plus : ∀ {Γ} → Γ ⊢ plus ∶ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) (⊢` ∋n) (⊢suc (⊢` ∋+ · ⊢` Z · ⊢` ∋n′)))))
  where
    ∋m = S ("m" ≠ "n") Z
    ∋n = Z
    ∋+ = S ("+" ≠ "m") (S ("+" ≠ "n") (S ("+" ≠ "m") Z))
    ∋n′ = S ("n" ≠ "m") Z

⊢2+2 : ∅ ⊢ plus · two · two ∶ `ℕ
⊢2+2 = ⊢plus · ⊢two · ⊢two

⊢sucᶜ : ∅ ⊢ sucᶜ ∶ `ℕ ⇒ `ℕ
⊢sucᶜ = ⊢ƛ (⊢suc (⊢` Z))

∋-injective : ∀ {Γ x A B} → Γ ∋ x ∶ A → Γ ∋ x ∶ B → A ≡ B
∋-injective Z          Z       = refl
∋-injective Z         (S x≢ _) = ⊥-elim (x≢ refl)
∋-injective (S x≢ _)   Z       = ⊥-elim (x≢ refl)
∋-injective (S x ∋xA) (S x₁ ∋xB) = ∋-injective ∋xA ∋xB

⊢mul : ∀ {Γ} → Γ ⊢ mul ∶ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢mul = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) ⊢zero (⊢plus · ⊢` ∋n · (∋* · ∋m′ · ∋n′)))))
  where
    ∋m  = S ("m" ≠ "n") Z
    ∋n  = S ("n" ≠ "m") Z
    ∋*  = ⊢` (S ("*" ≠ "m") (S ("*" ≠ "n") (S ("*" ≠ "m") Z)))
    ∋m′ = ⊢` Z
    ∋n′ = ⊢` (S ("n" ≠ "m") Z)
