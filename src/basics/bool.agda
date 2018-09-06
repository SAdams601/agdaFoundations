module basics.bool where
--open import level

data 𝔹 : Set where
  tt : 𝔹
  ff : 𝔹

~_ : 𝔹 → 𝔹
~ tt = ff
~ ff = tt

_&&_ : 𝔹 → 𝔹 → 𝔹
tt && b = b
ff && b = ff

_||_ : 𝔹 → 𝔹 → 𝔹
tt || b = tt
ff || b = b

if_then_else_ : ∀ {ℓ} {A : Set ℓ} → 𝔹 → A → A → A
if tt then t else f = t
if ff then t else f = f

_xor_ : 𝔹 → 𝔹 → 𝔹
tt xor tt = ff
x xor y   = x || y

infix 7 ~_
infixr 6 _&&_
infixr 6 _xor_
infixr 6 _||_

data Day : Set where
  Monday    : Day
  Tuesday   : Day
  Wednesday : Day
  Thursday  : Day
  Friday    : Day
  Saturday  : Day
  Sunday    : Day

nextDay : Day -> Day
nextDay Monday    = Tuesday
nextDay Tuesday   = Wednesday
nextDay Wednesday = Thursday
nextDay Thursday  = Friday
nextDay Friday    = Saturday
nextDay Saturday  = Sunday
nextDay Sunday    = Monday

data Suit : Set where
  Heart   : Suit
  Diamond : Suit
  Spade   : Suit
  Club    : Suit

isRed : Suit -> 𝔹
isRed Heart = tt
isRed Diamond = tt
isRed _ = ff
