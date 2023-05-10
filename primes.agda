module Primes where

open import BuiltIn
open import Arithmetic
open import List

aInRangeB : (a b : Nat) -> a ≤ b -> (isIn Nat a (range b))
aInRangeB a b = {!!} 

isPrime : Nat -> Set
isPrime n = (x : Nat) -> (((x ≡ n -> ⊥) -> (divides x n -> ⊥)) -> ⊥) -> x ≡ 1

2isPrime : (isPrime 2)
2isPrime = (λ x f ->  {!!})
-- either x is greater than 2 in which case we use only div otherwise 

--FIX
fakeSub : (n : Nat) -> Nat -> Nat -> Maybe (isPrime n)
fakeSub p (suc a) (suc b) = fakeSub p a b
fakeSub p (suc a) 0 = just
fakeSub p 0 (suc b) = just
fakeSub p 0 0 = maybe (λ x f -> {!!})

maybePrime : (n : Nat) -> Nat -> Nat -> Maybe (isPrime n)  -> Maybe (isPrime n)
maybePrime p i j just = fakeSub p p (i * j) 
maybePrime p i j  = id  

--May need to be Maybe (isPrimeNat n)
naivePrimeCheck : (n : Nat) -> Nat -> Nat -> Maybe (isPrime n)
naivePrimeCheck p i (suc (suc j)) = maybePrime p i (suc j) $ naivePrimeCheck p i (suc j)
naivePrimeCheck p (suc (suc i)) 1 = naivePrimeCheck p (suc i) p
naivePrimeCheck p 1 1 = just
naivePrimeCheck p _ _ = just

maybe:: : {A : Set} -> Maybe A -> List A -> List A
maybe:: (maybe a) l = (:: a l)
maybe:: just = id


primeList : (n : Nat) -> Σ (List Nat) (λ l -> (x : Nat) -> ((isIn Nat x l) -> (( x ≤ n -> (isPrime x -> ⊥)) -> ⊥)))
primeList 0 = (nil , {!!})
primeList (suc n) = let
                    primeListn = primeList n
                    n-1List  = car primeListn
                    n-1Proof = cdr primeListn
                    in ((maybe::  (maybeMap (const $ suc n) (naivePrimeCheck (suc n) n n)) n-1List) , (λ x xisIn x≤nAndisPrime -> {!!}))


infinitePrimes : (n : Nat) -> Σ Nat (λ x -> ((x ≤ n -> (isPrime x -> ⊥)) -> ⊥))
infinitePrimes n = {!!}
