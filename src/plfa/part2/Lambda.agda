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
infixl 7 _·_
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
  ⇒ case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒ ‵suc (‵ "+" · ‵ "m" · ‵ "n") ]

twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ‵ "s" · (‵ "s" · ‵ "z")

plusᶜ : Term
plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
  ‵ "m" · (‵ "s" · (‵ "n" · (‵ "s" · ‵ "z")))

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ ‵suc (‵ "n")

mul : Term
mul = μ "*" ⇒ (ƛ "m" ⇒ ƛ "n" ⇒
              case ‵ "m" [zero⇒ ‵zero
              |suc "m" ⇒ plus · (‵ "n" · (‵ "*" · (‵ "m" · ‵ "n"))) ])

four : Term
four = mul · (two · two)

ƛ′_⇒_ : Term → Term → Term
ƛ′ (‵ x) ⇒ N = ƛ x ⇒ N
ƛ′ _ ⇒ _ = ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (‵ x) ⇒ N ] = case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc _ ⇒ _ ] = ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (‵ x) ⇒ N = μ x ⇒ N
μ′ _ ⇒ _     = ⊥-elim impossible
  where postulate impossible : ⊥

plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
  case′ m
    [zero⇒ n
    |suc m ⇒ ‵suc (+ · (m · n)) ]
  where
  + = ‵ "+"
  m = ‵ "m"
  n = ‵ "n"

mul′ : Term
mul′ = μ′ * ⇒ ƛ′ m ⇒ ƛ′ n ⇒
  case′ m
    [zero⇒ ‵zero
    |suc m ⇒  plus′ · ((* · (m · n)) · n) ]
  where
    *  = ‵ "*"
    m  = ‵ "m"
    n  = ‵ "n"

data Value : Term → Set where
  V-ƛ : ∀ {x N}
  --------------
    → Value (ƛ x ⇒ N)

  V-zero :
    ----------
    Value ‵zero

  V-suc : ∀ {V}
    → Value V
    ----------
    → Value (‵suc V)

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(‵ x) [ y := V ] with x ≟ y
... | yes _    = V
... | no  _    = ‵ x 
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _    = ƛ x ⇒ N
... | no  _    = ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ] = (L [ y := V ]) · (M [ y := V ])
‵zero [ y := V ] = ‵zero
(‵suc M) [ y := V ] = ‵suc (M [ y := V ])
case L [zero⇒ M |suc x ⇒ N ] [ y := V ] with x ≟ y
... | yes _    = case L [ y := V ] [zero⇒  M [ y := V ] |suc x ⇒ N ]
... | no  _    = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _    = μ x ⇒ N
... | no  _    = μ x ⇒ N [ y := V ]

_ : (ƛ "z" ⇒ ‵ "s" · (‵ "s" · ‵ "z")) [ "s" := sucᶜ ] ≡ ƛ "z" ⇒ sucᶜ · (sucᶜ · ‵ "z")
_ = refl

_ : (ƛ "y" ⇒ ‵ "x" · (ƛ "x" ⇒ ‵ "x")) [ "x" := ‵zero ] ≡ (ƛ "y" ⇒ ‵zero · (ƛ "x" ⇒ ‵ "x"))
_ = refl

[_≣_]_↔_ : Id → Id → Term → Term → Term

_[_:=_]′ : Term → Id → Term → Term
(‵ x) [ y := V ]′ with x ≟ y
... | yes _  = V
... | no  _  = ‵ x
(ƛ x ⇒ M) [ y := V ]′                      = ƛ x ⇒ [ x ≣ y ] V ↔ M
(M · L) [ y := V ]′                        = (M [ y := V ]′) · (L [ y := V ]′)
‵zero [ y := V ]′                          = ‵zero
(‵suc M) [ y := V ]′                       = ‵suc (M [ y := V ]′)
(μ x ⇒ M) [ y := V ]′                      = μ x ⇒ [ x ≣ y ] V ↔ M
case L [zero⇒ M |suc x ⇒ N ] [ y := V ]′   = case (L [ y := V ]′)
                                             [zero⇒ (M [ y := V ]′)
                                             |suc x ⇒ [ x ≣ y ] V ↔ N ]


[ x ≣ y ] V ↔ M  with x ≟ y
... | yes _ = M
... | no  _ = M [ y := V ]′

infix 4 _—→_

data _—→_ : Term → Term → Set where

  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
    ---------------
    → L · M —→ L′ · M 

  ξ-·₂ : ∀ {V M M′}
    → M —→ M′
    ---------------
    → V · M —→ V · M′

  β-ƛ : ∀ {x N V}
    → Value V
    -------------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M′}
    → M —→ M′
    ---------
    → ‵suc M —→ ‵suc M′
  
  ξ-case : ∀ {x L L′ M N}
    → L —→ L′
    ----------------------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
  -----------------------------------------
    → case ‵zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
    ------------------
    → case ‵suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
    -------------------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]

_ : (ƛ "x" ⇒ ‵ "x") · (ƛ "x" ⇒ ‵ "x") —→ (ƛ "x" ⇒ ‵ "x")
_ = β-ƛ V-ƛ

_ : (ƛ "x" ⇒ ‵ "x") · ((ƛ "x" ⇒ ‵ "x") · (ƛ "x" ⇒ ‵ "x")) —→ (ƛ "x" ⇒ ‵ "x") · (ƛ "x" ⇒ ‵ "x")
_ = ξ-·₂ (β-ƛ V-ƛ)

_ : (twoᶜ · sucᶜ) · ‵zero —→ (ƛ "z" ⇒ sucᶜ · (sucᶜ · ‵ "z")) · ‵zero
_ = ξ-·₁ (β-ƛ V-ƛ) 

infix 2 _—↠_
infix 1 begin_
infixr 2 _—→⟨_⟩_
infix 3 _∎

data _—↠_ : Term → Term → Set where

  _∎ : ∀ M
  ------------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
    ----------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
    ------
  → M —↠ N
begin M–↠N = M–↠N

data _—↠′_ : Term → Term → Set where

  step′ : ∀ {M N}
    → M —→ N
      -------
    → M —↠′ N

  refl′ : ∀ {M}
      -------
    → M —↠′ M

  trans′ : ∀ {L M N}
    → L —↠′ M
    → M —↠′ N
      -------
    → L —↠′ N

open import plfa.Isomorphism using (_≲_)

private —↠-trans : ∀ {L M N} → L —↠ M → M —↠ N → L —↠ N
        —↠-trans (_ ∎) L—↠N = L—↠N
        —↠-trans (L —→⟨ L—→M₁ ⟩ L—↠M) M—↠N = L —→⟨ L—→M₁ ⟩ —↠-trans L—↠M M—↠N

—↠≲—↠′ : ∀ {M N} → (M —↠ N) ≲ (M —↠′ N)
—↠≲—↠′ {M} {N} =
  record
  { to      = to′ 
  ; from    = from′
  ; from∘to = from∘to′ 
  }
  where
    to′ : ∀ {M N} → (M —↠ N) → (M —↠′ N)
    to′ (_ ∎) = refl′
    to′ (m —→⟨ x ⟩ M—↠N) = trans′ (step′ x) (to′ M—↠N)
    from′ : ∀ {M N} → (M —↠′ N) → (M —↠ N)
    from′ {M₁} {N₁} (step′ x) = M₁ —→⟨ x ⟩ N₁ ∎
    from′ {M₁} refl′ = M₁ ∎
    from′ (trans′ {L} {M} {N} L—↠′M M—↠′N) = —↠-trans (from′ L—↠′M) (from′ M—↠′N)
    from∘to′ : ∀ {M N} → (M—↠N : M —↠ N) → from′ (to′ (M—↠N)) ≡ M—↠N
    from∘to′ (_ ∎) = refl
    from∘to′ (L —→⟨ L—→M₁ ⟩ M—↠N) rewrite from∘to′ M—↠N = refl

one : Term
one = ‵suc ‵zero

_ : (plus · one) · one —↠ two
_ = begin 
          plus · one · one
    —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
      (ƛ "m" ⇒
       (ƛ "n" ⇒
        case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒
        ‵suc
        ((μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒ ‵suc (‵ "+" · ‵ "m" · ‵ "n")
            ])))
         · ‵ "m"
         · ‵ "n")
        ])) · one · one
       —→⟨ ξ-·₁ (β-ƛ (V-suc V-zero)) ⟩
         (ƛ "n" ⇒
       case one [zero⇒ ‵ "n" |suc "m" ⇒
       ‵suc
       ((μ "+" ⇒
         (ƛ "m" ⇒
          (ƛ "n" ⇒
           case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒ ‵suc (‵ "+" · ‵ "m" · ‵ "n")
           ])))
        · ‵ "m"
        · ‵ "n")
       ])· one
       —→⟨ β-ƛ (V-suc V-zero)⟩
         case ‵suc ‵zero [zero⇒ one |suc "m" ⇒
      ‵suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒ ‵suc (‵ "+" · ‵ "m" · ‵ "n")
          ]))) · ‵ "m" · one)]
      —→⟨ β-suc V-zero ⟩ 
        ‵suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒ ‵suc (‵ "+" · ‵ "m" · ‵ "n")
          ]))) · ‵zero · ‵suc ‵zero)
      —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩ 
      ‵suc
      ((ƛ "m" ⇒
        (ƛ "n" ⇒
         case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒
         ‵suc
         ((μ "+" ⇒
           (ƛ "m" ⇒
            (ƛ "n" ⇒
             case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒ ‵suc (‵ "+" · ‵ "m" · ‵ "n")
             ])))
          · ‵ "m"
          · ‵ "n")])) · ‵zero · ‵suc ‵zero)
      —→⟨ ξ-suc (ξ-·₁ (β-ƛ V-zero)) ⟩ 
        ‵suc
      ((ƛ "n" ⇒
        case ‵zero [zero⇒ ‵ "n" |suc "m" ⇒
        ‵suc
        ((μ "+" ⇒
          (ƛ "m" ⇒
           (ƛ "n" ⇒
            case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒ ‵suc (‵ "+" · ‵ "m" · ‵ "n")
            ])))
         · ‵ "m"
         · ‵ "n")]) · ‵suc ‵zero)
      —→⟨ ξ-suc (β-ƛ (V-suc V-zero)) ⟩ 
        ‵suc
      case ‵zero [zero⇒ ‵suc ‵zero |suc "m" ⇒
      ‵suc
      ((μ "+" ⇒
        (ƛ "m" ⇒
         (ƛ "n" ⇒
          case ‵ "m" [zero⇒ ‵ "n" |suc "m" ⇒ ‵suc (‵ "+" · ‵ "m" · ‵ "n")
          ]))) · ‵ "m" · ‵suc ‵zero)]
      —→⟨ ξ-suc β-zero ⟩ {!
        ‵suc (‵suc ‵zero) ∎
      !} 
      
    
