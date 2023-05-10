module Arithmetic where

open import BuiltIn


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
divides a b = Σ Nat (λ n → (n * a) ≡ b)

only≤Divides : (a b : Nat) -> ((a ≡ b -> ⊥) × (b ≤ a)) -> (divides a b) -> ⊥
only≤Divides a b f a|b = {!!}

0DoesNotDivide : (n : Nat) -> (divides 0 n) -> ⊥
0DoesNotDivide n evidence = {!!}

≤EitherRefl : (a b : Nat) -> Either (a ≤ b) (b ≤ a)
≤EitherRefl = {!!}

{- only≤Divides : (a b : Nat) → (((a ≡ b → ⊥) → (b ≤ a → ⊥)) → ⊥) → (divides a b) → ⊥
only≤Divides a b f a|b = f (λ nota=b → {!!}) -}
