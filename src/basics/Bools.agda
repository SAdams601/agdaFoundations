module basics.Bools where

data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true  = false
not false = true

_∨_ : Bool → Bool → Bool
false ∨ x     = x
_     ∨ _     = true

_∧_ : Bool → Bool → Bool
true ∧ true = true
_    ∧ _    = false

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else _ = x
if false then _ else y = y

