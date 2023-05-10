module Arithmetic where
open import BuiltIn

_+_ : Nat ->  Nat ->  Nat
zero + y = y
(suc x) + y = suc (x + y)

_*_ : Nat -> Nat -> Nat
zero * y = 0
(suc x) * y = y + (x * y)

_≤_ : Nat -> Nat -> Set
n ≤ m =  Σ (Nat) (λ i -> ((i + n) ≡ m))

divides : Nat -> Nat -> Set
divides a b = Σ Nat (λ n -> (n * a) ≡ b)

{- only≤Divides : (a b : Nat) -> (((a ≡ b -> ⊥) -> (b ≤ a -> ⊥)) -> ⊥) -> (divides a b) -> ⊥
only≤Divides a b f a|b = f (λ nota=b -> {!!}) -}
