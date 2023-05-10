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

-- Either
data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

indEither : {A B C : Set} -> Either A B -> (A -> C) -> (B -> C) -> C
indEither (left a)  f _ = f a
indEither (right b) _ g = g b

-- Equivalence
data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x
infix 4 _≡_

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl


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
