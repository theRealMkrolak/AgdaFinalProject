module BuiltIn where

-- Falsity
data ⊥ : Set where

absurd : {A : Set} → ⊥ → A
absurd ()

-- Products
data _×_ (A B : Set) : Set where
 _^_ : A -> B -> A × B

fst : {A B : Set} -> A × B -> A
fst  (a ^ b) = a

snd : {A B : Set} -> A × B -> B
snd (a ^ b) = b

data Σ (A : Set) (B : A -> Set) : Set where
  _,_ : (x : A)  -> B x -> Σ A B

car : {A : Set} {B : A -> Set}  -> Σ A B -> A
car (a , b) = a

cdr : {A : Set} {B : A -> Set} -> (a : Σ A B) -> (B (car a))
cdr (a , b) = b

-- Equivalence
data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x
infix 4 _≡_

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- Naturals
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
zero    + y = y
(suc x) + y = suc (x + y)

_*_ : Nat → Nat → Nat
zero    * y = 0
(suc x) * y = y + (x * y)

_≤_ : Nat → Nat → Set
n ≤ m = Σ (Nat) (λ i → ((i + n) ≡ m))

divides : Nat → Nat → Set
divides a b = (b ≡ 0 -> ⊥) × (Σ Nat (λ n →  (a * n) ≡ b))



-- Either
data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

indEither : {A B C : Set} -> Either A B -> (A -> C) -> (B -> C) -> C
indEither (left a)  f _ = f a
indEither (right b) _ g = g b



-- Maybe
data Maybe (A : Set) : Set where
  just     : A → Maybe A
  nothing  : Maybe A

indMaybe : {A B : Set} → (A → B) → Maybe A → Maybe B
indMaybe f (just a) = just (f a)
indMaybe _ nothing  = nothing

-- Miscellaneous
id : {A : Set} → A → A
id x = x

const : {A B : Set} → A → B → A
const x _ = x

_$_ : {A B : Set} → (A → B) → A → B
a $ b = a b

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = (λ x → f (g x))
