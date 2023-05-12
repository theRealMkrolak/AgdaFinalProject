module Primes where

open import BuiltIn
open import Arithmetic
open import List


isPrime : Nat → Set
isPrime n = (x : Nat) -> ((x ≡ n -> ⊥) × (divides x n)) -> x ≡ 1

2isPrime : (isPrime 2)
2isPrime = (λ x t -> indEither
                     (≤EitherRefl 2 x)
                     (λ 2≤x -> absurd (only≤Divides x 2  ((fst t) ^ 2≤x) (snd t)))
                     (λ x≤2 -> {!!}))
-- either x is greater than 2 in which case we use only div otherwise


0isPrime : (isPrime 0)
0isPrime = (λ x xNeq0&x|0 -> absurd $ indEither
                             (≤EitherRefl x 0)
                             (λ x≤0 -> (fst xNeq0&x|0) (aIsIn[b]a=b x 0 (aInRangeB x 0 x≤0)))
                             (λ 0≤x -> only≤Divides x 0 (fst xNeq0&x|0 ^  0≤x) (snd xNeq0&x|0)))



divDec : (p n : Nat) -> Either (divides p n) (divides p n -> ⊥)
divDec p n = {!!}

primeDecHelper : (p n r : Nat) -> (divides n p -> isIn Nat n (range r)) ->  Either (isPrime n) (isPrime n -> ⊥)
primeDecHelper p n r n|p=>nInl = {!!}

--Use Naive Prime Check as template
primeDec : (n : Nat) -> Either (isPrime n) (isPrime n -> ⊥)
primeDec 0 = (left 0isPrime)
primeDec (suc n) = {!!} -- primeDecHelper (suc n) n ((1 , refl) : n ≤ (suc n)) 

--if x|n then 
 


--FIX
--fakeSub : (n : Nat) -> Nat -> Nat -> Maybe (isPrime n)
--fakeSub p (suc a) (suc b) = fakeSub p a b
--fakeSub p (suc a) 0 = nothing
--fakeSub p 0 (suc b) = nothing
--fakeSub p 0 0 = just (λ x f -> {!!})

--maybePrime : (n : Nat) -> Nat -> Nat -> Maybe (isPrime n)  -> Maybe (isPrime n)
--maybePrime p i j just = fakeSub p p (i * j)
--maybePrime p i j  = id

--May need to be Maybe (isPrimeNat n)
--naivePrimeCheck : (n : Nat) -> Nat -> Nat -> Maybe (isPrime n)
--naivePrimeCheck p i (suc (suc j)) = maybePrime p i (suc j) $ naivePrimeCheck p i (suc j)
--naivePrimeCheck p (suc (suc i)) 1 = naivePrimeCheck p (suc i) p
--naivePrimeCheck p 1 1 = just
--naivePrimeCheck p _ _ = just

--maybe:: : {A : Set} -> Maybe A -> List A -> List A
--maybe:: (maybe a) l = (:: a l)
--maybe:: just = id

primeList : (n : Nat) -> Σ (List Nat) (λ l -> (x : Nat)  -> ((x ≤ n) × (isPrime x)) -> (isIn Nat x l))
--primeList 0 = (nil , (λ x x≤n&isPrimeX -> aInRangeB x 0 (fst x≤n&isPrimeX)  {!!}))
primeList 0 = {!!}
primeList (suc n) = let
                    primeListn = primeList n
                    n-1List  = car primeListn
                    n-1Proof = cdr primeListn
                    in {!!}


infinitePrimes : (n : Nat) -> Σ Nat (λ x -> ((x ≤ n -> (isPrime x -> ⊥)) -> ⊥))
infinitePrimes n = {!!}
