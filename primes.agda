module Primes where

open import BuiltIn
open import Arithmetic
open import List 




isPrime : Nat → Set
isPrime n = (x : Nat) -> ((x ≡ n -> ⊥) × (divides x n)) -> x ≡ 1

--Very powerful function! Essentially given that something is in a range and evidence that for every item is not in that list returns false
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


-- Look at divDecHelper before attempting
primeDecHelper : (p q m : Nat) -> ((m + q) ≡ p) -> (Either (divides m p) (divides m p -> ⊥) × Fin (λ x -> Either (x ≡ p) (divides x p -> ⊥)) m) -> Either (isPrime p) (isPrime p -> ⊥)
primeDecHelper p (suc q) (suc (suc m)) m+q=p (left   m|p ^ finN-1) = right (λ pIsPrime -> (λ ()) $ pIsPrime (suc (suc m)) ({!!} ^ m|p))
primeDecHelper p (suc q) m             m+q=p (right !m|p ^ finN-1) = {!!}
primeDecHelper p (suc q) 0             m+q=p (left   m|p ^ finN-1) = {!!}
primeDecHelper p (suc q) 1             m+q=p (left   m|p ^ finN-1) = {!!}
primeDecHelper p 0       m             m+q=p (left   m|p ^ finN-1) = {!!}
primeDecHelper p 0       m             m+q=p (right !m|p ^ finN-1) = right (λ pIsPrime -> !m|p (1 ,  trans (sym (*1= m)) (trans (+0= m) m+q=p)))



0isNotPrime : isPrime 0 -> ⊥
0isNotPrime isPrime0 = ((0!=Sn 0 ∘ cong sub1) ∘ sym) $ isPrime0 2 ((0!=Sn 1 ∘ sym)  ^ 0DividesAll 2)

--I think this has to do with the fact that nothing fits the criteria so false implies true. This is most likely due to our definition of primeness.
1isPrime : isPrime 1 
1isPrime x (x!=1 ^ x|1) = absurd $ indEither (≤EitherRefl x 1)
                                                (λ x≤1 -> indIsNotInRange x 1 (aInRangeB x 1 x≤1 ^ (body x!=1
                                                                                                         (body (λ x=0 -> (0!=Sn 0) (sym $ only0Divides0
                                                                                                                                          1
                                                                                                                                          (car x|1 , (trans (sym $ cong (λ y -> y * (car x|1)) x=0) (cdr x|1)))))
                                                                                                           (end)))))
                                                (λ 1≤x -> only≤Divides x 1  (0!=Sn 0 ∘ sym) (x!=1 ^ 1≤x) x|1)



primeDec : (n : Nat) -> Either (isPrime n) (isPrime n -> ⊥)
primeDec 0 = right 0isNotPrime
primeDec 1 = left  1isPrime
primeDec (suc (suc n)) = {!!} 
                                                 

primeList : (n : Nat) -> Σ (List Nat) (λ l -> (x : Nat)  -> ((x ≤ n) × (isPrime x)) -> (isIn Nat x l))
primeList 0 = {!!}
primeList (suc n) = let
                    primeListn = primeList n
                    n-1List  = car primeListn
                    n-1Proof = cdr primeListn
                    in {!!}


infinitePrimes : (n : Nat) -> Σ Nat (λ x -> ((x ≤ n -> (isPrime x -> ⊥)) -> ⊥))
infinitePrimes n = {!!}
