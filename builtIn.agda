module BuiltIn where

data ⊥ : Set where

absurd : {A : Set} -> ⊥ -> A
absurd ()

id : {A : Set} -> A -> A
id x = x

const : {A B : Set} -> A -> B -> A  
const x _ = x

_$_ : {A B : Set} -> (A -> B) -> A -> B
a $ b = a b

_∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
f ∘ g = (λ x -> f (g x))

data _×_ (A B : Set) : Set where
  [_,_] : A -> B -> A × B

data Σ (A : Set) (B : A -> Set) : Set where
  _,_ : (x : A) -> B x -> Σ A B

car : {A : Set} {B : A -> Set}  -> Σ A B -> A
car (a , b) = a

cdr : {A : Set} {B : A -> Set} -> (a : Σ A B) -> (B (car a))
cdr (a , b) = b

data _≡_ {A : Set} : A -> A -> Set where
  refl : {x : A} -> x ≡ x
infix 4 _≡_

cong : {A B : Set} {x y : A} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B 

data Maybe (A : Set) : Set where
  just : A -> Maybe A
  nothing  : Maybe A

maybeMap : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B
maybeMap f (just a) = just (f a)
maybeMap _ nothing = nothing
