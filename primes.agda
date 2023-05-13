module Primes where

open import BuiltIn
open import Arithmetic
open import List


isPrime : Nat → Set
isPrime n = (x : Nat) -> ((x ≡ n -> ⊥) × (divides x n)) -> x ≡ 1

--2isPrime : (isPrime 2)
--2isPrime = (λ x t -> indEither
--                     (≤EitherRefl 2 x)
                     ---(λ 2≤x -> absurd (only≤Divides x 2  ((fst t) ^ 2≤x) (snd t)))
--                    (λ x≤2 -> {!!}))
-- either x is greater than 2 in which case we use only div otherwise


--0isPrime : (isPrime 0)
--0isPrime = (λ x xNeq0&x|0 -> absurd $ indEither
--                             (≤EitherRefl x 0)
--                             (λ x≤0 -> (fst xNeq0&x|0) (aIsIn[b]a=b x 0 (aInRangeB x 0 x≤0)))
--                             (λ 0≤x -> only≤Divides x 0 (fst xNeq0&x|0 ^  0≤x) (snd xNeq0&x|0)))


indIsNotInRange : (n m : Nat) -> (isIn Nat n (range m) × Fin (λ x -> n ≡ x -> ⊥) (suc m)) -> ⊥
indIsNotInRange n (suc m) (nisInm ^ (body n!=m finm-1)) = indIsNotInRange n m (aIsInbL&a!=b=>aIsInL n (suc m)  (nisInm ^ n!=m) ^ finm-1) 
indIsNotInRange n 0 (nIsIn0 ^ (body n!=0 end)) = n!=0 $ aIsIn[b]a=b n 0 nIsIn0

natDec : (a b : Nat) -> Either (a ≡ b) (a ≡ b -> ⊥)
natDec a b = {!!}

--if n≤p then if n|p ∃x≤p x|p xn=p ->
--This is some of the worst and least readable code I have ever written in my life
divDecHelper : (n p q m : Nat) -> ((m + q) ≡ p) -> (Either ((n * m)  ≡ p) ((n * m) ≡ p -> ⊥) × Fin (λ x -> (n * x) ≡ p -> ⊥) m) -> Either (divides n p) (divides n p -> ⊥)
divDecHelper n p       q m m+q=p  (left  n*m=p  ^ finNeq) = left (m , n*m=p)
divDecHelper n p (suc q) m m+q=p  (right n*m!=p ^ finNeq) = divDecHelper n p q (suc m) (trans (suc+=+suc m q) m+q=p)  (natDec (n * (suc m)) p ^ body n*m!=p finNeq)  
divDecHelper n p       0 m m+q=p  (right n*m!=p ^ finNeq) = right (λ n|p -> indEither (≤EitherRefl (car n|p) p)
                                                                                      (λ c≤p -> indIsNotInRange (car n|p) m
                                                                                        (aInRangeB
                                                                                          (car n|p)
                                                                                          m
                                                                                          (car c≤p , trans (cdr c≤p)
                                                                                          (sym $ trans (+0= m) m+q=p)) ^
                                                                                                                       finMap
                                                                                                                         (λ n*m!=p c=m -> n*m!=p $ trans (cong (λ x -> n * x) (sym c=m)) (cdr n|p))
                                                                                                                         (body n*m!=p finNeq)))
                                                                                      (λ p≤c -> indEither (natDec (car n|p) p)
                                                                                                          (λ p=c  -> n*m!=p $ trans (cong (λ x -> n * x) (trans (trans (+0= m) m+q=p) (sym p=c))) (cdr n|p))
                                                                                                          (λ c!=p -> only≤Divides
                                                                                                                     (car n|p)
                                                                                                                     p
                                                                                                                     (λ p=0 -> n*m!=p $ trans
                                                                                                                                        (trans
                                                                                                                                            (cong (λ x -> n * x) $
                                                                                                                                              trans
                                                                                                                                                (trans (+0= m) m+q=p)
                                                                                                                                                p=0)
                                                                                                                                            (n*0=0 n))
                                                                                                                                            (sym p=0))
                                                                                                                     (c!=p ^ p≤c)
                                                                                                                     (n , trans (comm* (car n|p) n) (cdr n|p)))))


divDec : (n p : Nat) -> Either (divides n p) (divides n p -> ⊥)
divDec n p = divDecHelper n p p 0 (refl) (natDec (n * 0) p ^ end)

primeDecHelper : (p n r : Nat) -> (divides n p -> isIn Nat n (range r)) ->  Either (isPrime n) (isPrime n -> ⊥)
primeDecHelper p n r n|p=>nInl = {!!}

--Use Naive Prime Check as template
primeDec : (n : Nat) -> Either (isPrime n) (isPrime n -> ⊥)
primeDec 0 = {!!}
primeDec (suc n) = {!!} 
                                                 
                             
-- primeDecHelper (suc n) n ((1 , refl) : n ≤ (suc n)) 
--if x|n then 
 


--FIX
--fakeSub : (n : Nat) -> Nat -> Nat -> Maybe (isPrime n)
--fakeSub p (suc a) (suc b) = fakeSub p a b
--fakeSub p (suc a) 0 = nothing
--fakeSub p 0 (suc b) = nothing
--fakeSub p 0 0 = just (λ x f -> {!!})

--maybePrime : (n : Nat) -> Nat -> Nat -> Maybe (isPrime n)  -> Maybe (isPrime n
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
