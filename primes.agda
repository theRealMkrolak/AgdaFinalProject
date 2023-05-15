module Primes where

open import BuiltIn
open import Arithmetic
open import List 

isPrime : Nat → Set
isPrime n = (x : Nat) → (x ≡ n → ⊥) × (x div n) → x ≡ 1

-- Very powerful function! Essentially, can't have something is in a range 0-m AND evidence that it's not equal to each 0-m
indIsNotInRange : (n m : Nat) → isIn Nat n (range m) × Fin (λ x → n ≡ x → ⊥) (suc m) → ⊥
indIsNotInRange n 0       (nIsIn0 , body n!=0 end)  = n!=0 $ singletonIsItself n 0 nIsIn0
indIsNotInRange n (suc m) (nisInm , body n!=m rest) = indIsNotInRange n m (notHeadThenInRest n (suc m) (nisInm , n!=m) , rest) 

natDec : (a b : Nat) → Either (a ≡ b) (a ≡ b -> ⊥)
natDec 0       0       = left refl
natDec 0       (suc b) = right $ 0!=Sn b
natDec (suc a) 0       = right $ Sn!=0 a
natDec (suc a) (suc b) = cases (natDec a b) (left ∘ cong suc) (λ a!=b → right $ λ Sa=Sb → a!=b $ cong sub1 Sa=Sb)

-- Most beautiful code ever written
divDecHelperLeft : (n p m : Nat) → m + 0 ≡ p → (n * m ≡ p → ⊥) × Fin (λ x → n * x ≡ p → ⊥) m → (n|p : n div p) → car n|p ≤ p → ⊥
divDecHelperLeft n p m m+0=p (n*m!=p , finNeq) n|p k≤p = indIsNotInRange k m
  (aInRangeB k m k≤m , finMap (λ n*m!=p k=m → n*m!=p $ trans (cong (n *_) (sym k=m)) n*k=p) (body n*m!=p finNeq))
  where
    k = car n|p
    n*k=p = cdr n|p
    k≤m = eqAlso≤ k p m (k≤p , sym (trans (+0= m) m+0=p))

divDecHelperRight : (n p m : Nat) → m + 0 ≡ p → (n * m ≡ p → ⊥) → (n|p : n div p) → p ≤ car n|p → ⊥
divDecHelperRight n p m m+0=p n*m!=p n|p p≤k = cases (natDec k p)
  (λ k=p → n*m!=p $ trans (cong (n *_) (trans m=p (sym k=p))) n*k=p)
  (λ k!=p → only≤Divides k p p!=0 (k!=p , p≤k) (n , trans (comm* k n) n*k=p))
  where
    k = car n|p
    n*k=p = cdr n|p
    m=p = trans (+0= m) m+0=p
    p!=0 = λ p=0 → n*m!=p $ trans (trans (cong (n *_) $ trans m=p p=0) (n*0=0 n)) (sym p=0)

divDecHelper : (n p q m : Nat) → m + q ≡ p → Either (n * m ≡ p) (n * m ≡ p → ⊥) × Fin (λ x → n * x ≡ p → ⊥) m → Either (n div p) (n div p → ⊥)
divDecHelper n p q       m m+q=p  (left  n*m=p  , finNeq) = left (m , n*m=p)
divDecHelper n p (suc q) m m+Sq=p (right n*m!=p , finNeq) = divDecHelper n p q (suc m) Sm+q=p (nSm=?p , body n*m!=p finNeq)
  where
    Sm+q=p = trans (suc+=+suc m q) m+Sq=p
    nSm=?p = natDec (n * (suc m)) p
divDecHelper n p 0       m m+0=p  (right n*m!=p , finNeq) = right $ λ n|p → cases (≤Dec (car n|p) p)
  (divDecHelperLeft n p m m+0=p (n*m!=p , finNeq) n|p)
  (divDecHelperRight n p m m+0=p n*m!=p n|p)

divDec : (n p : Nat) → Either (n div p) (n div p → ⊥)
divDec n p = divDecHelper n p p 0 refl (natDec (n * 0) p , end)

-- Decidability of primes
0isNotPrime : isPrime 0 → ⊥
0isNotPrime isPrime0 = (0!=Sn 0 ∘ cong sub1 ∘ sym) $ isPrime0 2 ((0!=Sn 1 ∘ sym) , AllDivide0 2)

--I think this has to do with the fact that nothing fits the criteria so false implies true. So this is most likely due to our definition of primeness.
1isPrime : isPrime 1 
1isPrime x (x!=1 , x|1) = absurd $ cases (≤Dec x 1)
  (λ x≤1 → indIsNotInRange x 1 (aInRangeB x 1 x≤1 ,
    (body x!=1 (body (λ x=0 → (0!=Sn 0) (sym $ only0Divides0 1 (car x|1 , (trans (sym $ cong (_* car x|1) x=0) (cdr x|1))))) (end)))))
  (λ 1≤x → only≤Divides x 1  (0!=Sn 0 ∘ sym) (x!=1 , 1≤x) x|1)

-- Laura stopped about here
primeDecHelper : (p q m : Nat) -> ((+2 m) + q) ≡ (+2 p)
                               -> Either ((+2 m) div (+2 p)) ((+2 m) div (+2 p) -> ⊥) × Fin (λ x -> Either (+2 x ≡ +2 p) ((+2 x) div (+2 p) -> ⊥)) m
                               -> Either (Fin (λ x -> Either ((+2 x) ≡ (+2 p)) ((+2 x) div (+2 p) -> ⊥))  (suc p)) (isPrime (+2 p) -> ⊥)
primeDecHelper p (suc q) m  m+q=p (right !m|p , finN-1) = primeDecHelper p q (suc m) (trans (suc+=+suc (+2 m) q) m+q=p) (divDec (suc (+2 m)) (+2 p) , body (right !m|p) finN-1)
primeDecHelper p (suc q) m  m+q=p (left   m|p , finN-1) = right (λ pIsPrime -> (λ ()) $ pIsPrime (+2 m) ({!!} , m|p))
primeDecHelper p 0       m  m+q=p (right !m|p , finN-1) = right (λ pIsPrime -> !m|p (1 , trans (sym (*1= (+2 m)))  (trans (+0= (+2 m)) m+q=p)))
primeDecHelper p 0       m  m+q=p (left   m|p , finN-1) = left $ replace
                                                                            (cong (sub1) (trans (+0= (+2 m)) m+q=p))
                                                                            (λ y -> Fin (λ x → Either (+2 x ≡ +2 p) ((+2 x) div (+2 p) → ⊥)) y)
                                                                            (body (left $ (trans (+0= (+2 m)) m+q=p)) finN-1)

-- Ok the strategy here is use only≤Divides for the case where p≤x and then for the other case use aInRageB to get the list of possible entries for a
-- Then because, from fin, that all but 0 and 1 are not possible we can then eliminate those. Thats as far as I got. Look at list for inspiration
primeDec : (n : Nat) -> Either (isPrime n) (isPrime n -> ⊥)
primeDec 0 = right 0isNotPrime
primeDec 1 = left  1isPrime
primeDec (suc (suc n)) = let p = (+2 n) in cases (primeDecHelper n n 0 refl (divDec (+2 0) (+2 n) , end))
                                                   (λ fin -> left (λ x x!=p&x|p -> cases (≤Dec x p)
                                                                                                          {!!}
                                                                                                          {!!}))
                                                   (right ∘ id)
                                                 
primeList : (n : Nat) -> Σ (List Nat) (λ l -> (x : Nat)  -> ((x ≤ n) × (isPrime x)) -> (isIn Nat x l))
primeList = {!!}

infinitePrimes : (n : Nat) -> Σ Nat (λ x -> ((x ≤ n -> (isPrime x -> ⊥)) -> ⊥))
infinitePrimes n = {!!}
