module Primes where

open import BuiltIn
open import Arithmetic
open import List

isPrime : Nat → Set
isPrime 1 = ⊥
isPrime n = (x : Nat) → (x ≡ n → ⊥) × (x div n) → x ≡ 1

natDec : (a b : Nat) → Either (a ≡ b) (a ≡ b -> ⊥)
natDec 0       0       = left refl
natDec 0       (suc b) = right $ 0!=Sn b
natDec (suc a) 0       = right $ Sn!=0 a
natDec (suc a) (suc b) = cases (natDec a b) (left ∘ cong suc) (λ a!=b → right $ λ Sa=Sb → a!=b $ cong sub1 Sa=Sb)

-- Very powerful function! Essentially, can't have something is in a range 0-m AND evidence that it's not equal to each 0-m
indIsNotInRange : (n m : Nat) → isIn Nat n (range m) × Fin (λ x → n ≡ x → ⊥) (suc m) → ⊥
indIsNotInRange n 0       (nIsIn0 , body n!=0 end)  = n!=0 $ singletonIsItself n 0 natDec nIsIn0
indIsNotInRange n (suc m) (nisInm , body n!=m rest) = indIsNotInRange n m (notHeadThenInRest n (suc m) (nisInm , n!=m) , rest)

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
divDec n p = divDecHelper n p p 0 refl (natDec (n * 0) p , stop)

-- Decidability of primes
0isNotPrime : isPrime 0 → ⊥
0isNotPrime isPrime0 = (0!=Sn 0 ∘ cong sub1 ∘ sym) $ isPrime0 2 ((0!=Sn 1 ∘ sym) , AllDivide0 2)

1isNotPrime : isPrime 1 → ⊥
1isNotPrime = id

--1isPrime : isPrime 1
--1isPrime x (x!=1 , x|1) = absurd $ cases (≤Dec x 1)
--  (λ x≤1 → indIsNotInRange x 1 (aInRangeB x 1 x≤1 ,
--    (body x!=1 (body (λ x=0 → (0!=Sn 0) (sym $ only0Divides0 1 (car x|1 , (trans (sym $ cong (_* car x|1) x=0) (cdr x|1))))) (end)))))
--  (λ 1≤x → only≤Divides x 1  (0!=Sn 0 ∘ sym) (x!=1 , 1≤x) x|1)

primeDecHelper : (p q m : Nat) -> ((+2 m) + q) ≡ (+2 p)
                               -> Either ((+2 m) div (+2 p)) ((+2 m) div (+2 p) -> ⊥) × Fin (λ x -> Either (+2 x ≡ +2 p) ((+2 x) div (+2 p) -> ⊥)) m
                               -> Either (Fin (λ x -> Either ((+2 x) ≡ (+2 p)) ((+2 x) div (+2 p) -> ⊥))  (suc p)) (isPrime (+2 p) -> ⊥)
primeDecHelper p (suc q) m  m+q=p (right !m|p , finN-1) = primeDecHelper p q (suc m) (trans (suc+=+suc (+2 m) q) m+q=p) (divDec (suc (+2 m)) (+2 p) , body (right !m|p) finN-1)
primeDecHelper p (suc q) m  m+q=p (left   m|p , finN-1) = right (λ pIsPrime -> (λ ()) $ pIsPrime (+2 m) ({!!}  , m|p))
primeDecHelper p 0       m  m+q=p (right !m|p , finN-1) = right (λ pIsPrime -> !m|p (1 , trans (sym (*1= (+2 m)))  (trans (+0= (+2 m)) m+q=p)))
primeDecHelper p 0       m  m+q=p (left   m|p , finN-1) = left $ replace
                                                                            (cong (sub1) (trans (+0= (+2 m)) m+q=p))
                                                                            (λ y -> Fin (λ x → Either (+2 x ≡ +2 p) ((+2 x) div (+2 p) → ⊥)) y)
                                                                            (body (left $ (trans (+0= (+2 m)) m+q=p)) finN-1)

-- Ok the strategy here is use only≤Divides for the case where p≤x and then for the other case use aInRageB to get the list of possible entries for a
-- Then because, from fin, that all but 0 and 1 are not possible we can then eliminate those. Thats as far as I got. Look at list for inspiration

only1Divides=>isPrimeHelper : (p x n : Nat) -> (x ≡ (+2 p) → ⊥) × (x div (+2 p)) -> (isIn Nat x (range $ +2 n)) -> Fin (λ y -> Either (+2 y ≡ +2 p) ((+2 y) div (+2 p) -> ⊥)) (suc n) -> x ≡ 1
only1Divides=>isPrimeHelper p x 0       (x!=p , x|p) isInRange2 (body (left n=p)     stop) = cases (natDec x  2)
                                                                                             (λ x=n -> absurd $ (x!=p $ trans x=n n=p))
                                                                                             (λ x!=n -> cases (natDec x 1)
                                                                                                              id
                                                                                                              (λ x!=1 -> absurd $ indIsNotInRange  x 2 (isInRange2 ,
                                                                                                              (body x!=n
                                                                                                              (body x!=1
                                                                                                              (body (λ x=0 -> (Sn!=0 (suc p)) $
                                                                                                                              only0Divides0
                                                                                                                              (+2 p)
                                                                                                                              (replace x=0 (λ y -> y div (+2 p)) x|p)) stop))))))
only1Divides=>isPrimeHelper p x 0       (x!=p , x|p) isInRange2 (body (right notn|p) stop) = cases (natDec x 2)
                                                                                             (λ x=n -> absurd $ ((replace (sym x=n) (λ y -> y div (+2 p) -> ⊥) notn|p) x|p))
                                                                                             (λ x!=n -> cases (natDec x 1)
                                                                                                              id
                                                                                                              (λ x!=1 -> absurd $ indIsNotInRange  x 2 (isInRange2 ,
                                                                                                              (body x!=n
                                                                                                              (body x!=1
                                                                                                              (body (λ x=0 -> (Sn!=0 (suc p)) $
                                                                                                                              only0Divides0
                                                                                                                              (+2 p)
                                                                                                                              (replace x=0 (λ y -> y div (+2 p)) x|p)) stop))))))
                                                                                                              
only1Divides=>isPrimeHelper p x (suc n) (x!=p , x|p) isInRangeN (body (left  n=p)     fin) = cases (natDec x  (+2 (suc n)))
                                                                                             (λ x=n -> absurd $ (x!=p $ trans x=n n=p))
                                                                                             (λ x!=n -> only1Divides=>isPrimeHelper p x n (x!=p , x|p) (notHeadThenInRest x (+2 (suc n)) (isInRangeN , x!=n)) fin)
only1Divides=>isPrimeHelper p x (suc n) (x!=p , x|p) isInRangeN (body (right notn|p)  fin) = cases (natDec x  (+2 (suc n)))
                                                                                             (λ x=n -> absurd $ ((replace (sym x=n) (λ y -> y div (+2 p) -> ⊥) notn|p) x|p))
                                                                                             (λ x!=n -> only1Divides=>isPrimeHelper p x n (x!=p , x|p) (notHeadThenInRest x (+2 (suc n)) (isInRangeN , x!=n)) fin)


only1Divides=>isPrime : (p : Nat) -> Fin (λ x -> Either (+2 x ≡ +2 p) ((+2 x) div (+2 p) -> ⊥)) (suc p) -> isPrime (+2 p)
only1Divides=>isPrime p fin x (x!=p , x|p)  =  cases (≤Dec  x (+2 p))
                                                     (λ x≤p -> only1Divides=>isPrimeHelper p x p (x!=p , x|p) (aInRangeB x (+2 p) x≤p) fin)
                                                     (λ p≤x -> absurd $ only≤Divides x (+2 p) ((0!=Sn (suc p)) ∘ sym) (x!=p , p≤x) x|p)

primeDec : (n : Nat) -> Either (isPrime n) (isPrime n -> ⊥)
primeDec 0 = right 0isNotPrime
primeDec 1 = right 1isNotPrime
primeDec (suc (suc n)) = let p = (+2 n) in cases (primeDecHelper n n 0 refl (divDec (+2 0) (+2 n) , stop))
                                                 (left  ∘ only1Divides=>isPrime n)
                                                 (right ∘ id)

2IsPrime : isPrime 2
2IsPrime = only1Divides=>isPrime 0 (body (left refl) (stop))

primeList : (n : Nat) -> Σ (List Nat) (λ l -> (x : Nat)  -> ((x ≤ n) × (isPrime x)) -> (isIn Nat x l))
primeList 0 = ([] , (λ x x≤nisPrimeX -> let
                                        x≤n      = fst x≤nisPrimeX
                                        isPrimeX = snd x≤nisPrimeX
                                        in
                                          absurd $ cases (natDec x 0)
                                                (λ x=0 -> 0isNotPrime $ replace x=0 (λ y -> isPrime y) isPrimeX)
                                                (λ x!=0 -> notInNil x $ notHeadThenInRest x 0 (aInRangeB x 0 x≤n , x!=0))))
primeList (suc n) = let primeListN = primeList n in cases (primeDec (suc n))
                                                          (λ isPrimeSn -> (((suc n) :: car primeListN)  , (λ x x≤Sn&isPrimeX -> let
                                                                             x≤Sn      = fst x≤Sn&isPrimeX
                                                                             isPrimeX  = snd x≤Sn&isPrimeX
                                                                             in
                                                                             cases (natDec x (suc n))
                                                                                   (λ x=Sn  ->  replace
                                                                                                (sym x=Sn)
                                                                                                (λ y -> isIn Nat y ((suc n) :: car primeListN))
                                                                                                ([] , (car primeListN , (nilConcat ((suc n) :: car primeListN)))))
                                                                                   (λ x!=Sn -> let
                                                                                               isInPrimeListN = (cdr primeListN) x ((a≤Sb&a!=Sb=>a≤b x n x≤Sn x!=Sn) , isPrimeX)
                                                                                               crInList       = car isInPrimeListN
                                                                                               cdInList       = cdr isInPrimeListN
                                                                                               crcdInList     = car cdInList
                                                                                               cdcdInList     = cdr cdInList
                                                                                               in
                                                                                               ((suc n :: crInList) , (crcdInList , cong (λ x -> ((suc n) :: x)) cdcdInList))))))
                                                          (λ isNotPrimeSn -> (car primeListN , (λ x x≤Sn&isPrimeX -> let
                                                                             x≤Sn     = fst x≤Sn&isPrimeX
                                                                             isPrimeX = snd x≤Sn&isPrimeX
                                                                             in
                                                                             cases (natDec x (suc n))
                                                                                   (λ x=Sn  -> absurd (isNotPrimeSn $ replace x=Sn (λ y -> isPrime y) isPrimeX))
                                                                                   (λ x!=Sn -> (cdr primeListN) x ((a≤Sb&a!=Sb=>a≤b x n x≤Sn x!=Sn) , isPrimeX)))))

ftaHelper : (n p : Nat) -> Either (Fin (λ x -> Either (+2 x ≡ +2 n) ((+2 x) div (+2 n) -> ⊥)) (suc p)) (Σ Nat (λ x -> isPrime (+2 x) × ((+2 x) div (+2 n))))
ftaHelper m 0 = cases (divDec 2 (+2 m))
                      (λ 2|n -> right (0 , (2IsPrime , 2|n)))
                      (λ not2|n -> left $ body (right not2|n) (stop))
ftaHelper m (suc q) = let p = (+2 $ suc q)
                          n = (+2 m)
                      in
                      cases (natDec p n)
                      (λ p=n ->  cases (ftaHelper m q)
                                 (λ fin -> left (body (left p=n) fin))
                                 right)
                      (λ p!=n -> cases (divDec p n)
                                 (λ p|n -> cases (primeDec p)
                                           (λ isPrimep -> right ((suc q) , (isPrimep , p|n)))
                                           (λ isNotPrime -> cases (ftaHelper (suc q) q)
                                                            (λ fin -> right (suc q , (only1Divides=>isPrime (suc q) (body (left refl) fin) , p|n)))
                                                            (λ x&isPrimeX&x|p -> let
                                                                                 x        = car x&isPrimeX&x|p
                                                                                 back     = cdr x&isPrimeX&x|p
                                                                                 isPrimeX = fst back
                                                                                 x|p      = snd back
                                                                                 in
                                                                                   right (x , (isPrimeX , (divTrans (suc (suc x)) p n x|p p|n))))))
                                 (λ notP|n -> cases (ftaHelper m q)
                                              (λ fin ->  left (body (right notP|n) fin))
                                              right))

fta : (n : Nat) -> (Σ (Nat) (λ p -> (isPrime p) × (p div (+2 n))))
fta n = cases (ftaHelper n n) (λ fin -> ((+2 n) , (only1Divides=>isPrime n fin , (1 , (sym $ *1= (+2 n)))))) (λ x -> ((+2 $ car x) , cdr x))

realFta : (n : Nat) -> (n ≡ 1 -> ⊥) -> (Σ (Nat) (λ p -> (isPrime p) × (p div n)))
realFta 0             neq1 = (2 , (2IsPrime , AllDivide0 2))
realFta 1             neq1 = absurd $ neq1 refl
realFta (suc (suc n)) neq1 = fta n

-- infinitePrimesHelper
-- go down same way as primeDec helper
-- issue is that we need to show that b!=1 a*b=e c*b=e+1 -> False
-- 1+a*b=c*b
-- b * (a - c) = 1
-- only le divides
-- b!=0 because b is prime
-- b=1
-- contradiction
-- c!=0

product : List Nat -> Nat
product [] = 1
product (l :: ls) = l * (product ls)

productLemma : (list be en : List Nat) -> (p :  Nat) -> (concat be (p :: en) ≡ list) -> ((product be) * (p * (product en)) ≡ product list)
productLemma list [] en p eq =  let
                                p*ed=list = cong product (trans (nilConcat (p :: en)) eq)
                                1*ped=ped = trans (comm* 1 (p * (product en))) (sym $ *1= (p * (product en)))
                                in
                                trans 1*ped=ped  p*ed=list
productLemma (l :: ls) (b :: be) en p refl =  trans (sym $ assoc* l (product be) (p * product en)) (cong (λ x -> b * x) $ productLemma ls be en p refl)

productPrimeList : (n : Nat) → product (car (primeList n)) ≡ 0 → ⊥
productPrimeList n = {!!}

infinitePrimes : (n : Nat) -> Σ Nat (λ x -> (n ≤ x) × isPrime x)
infinitePrimes  0             = (2 , ((z≤n 2) , 2IsPrime))
infinitePrimes  1             = (2 , ((s≤s 0 1 $ z≤n 1) , 2IsPrime))
infinitePrimes (suc (suc n)) = let
                       list+ev   = primeList (suc (suc n))
                       list      = car list+ev
                       listEv    = cdr list+ev
                       listProd  = product list
                       fta       = realFta (1 + listProd) (λ 1+prod=1 → (productPrimeList (suc (suc n)))
                                                             (trans (sym (a+c-c=a listProd 1))
                                                             (trans (cong (_- 1) (comm+ listProd 1))
                                                                    (cong (_- 1) 1+prod=1))))
                       prime     = car fta
                       evidence  = cdr fta
                       p|n       = snd $ evidence
                       in
                       cases (≤Dec prime (suc (suc n)))
                             (λ p≤n -> let
                                       pInList  = listEv prime (p≤n , fst evidence)
                                       pInEvd   = (cdr (cdr pInList))
                                       be       = product (car pInList)
                                       en       = product (car $ cdr pInList)
                                       c        = (be * en)
                                       b        = car p|n
                                       ac       = prime * c
                                       abc=list : be * (prime * en) ≡ listProd
                                       abc=list = productLemma list (car pInList) (car $ cdr pInList) prime (sym pInEvd) 
                                       abe=bea  : (prime * be ≡ be * prime)
                                       abe=bea  = comm* prime be
                                       bac=bac  : (be * prime) * en ≡ listProd
                                       bac=bac  = (trans (sym $ assoc* be prime en) abc=list) 
                                       abc=list : (prime * (be * en) ≡ listProd)
                                       abc=list = trans (assoc* prime be en) $ trans (cong (λ x -> x * en) $ abe=bea) bac=bac
                                       1+ac=1+l : (1 + (prime * c) ≡ 1 + listProd)
                                       1+ac=1+l = cong
                                                  (λ x -> 1 + x) abc=list
                                       1+ac=ab  : (1 + (prime * c) ≡ (prime * b))
                                       1+ac=ab  = trans
                                                  1+ac=1+l
                                                  (sym $ cdr p|n)
                                       1=ab-ac  : (1 ≡ (prime * b) - ac)
                                       1=ab-ac  = trans
                                                 (sym $ a+c-c=a 1 ac)
                                                 (cong (λ x -> x - ac) 1+ac=ab)
                                       in
                                       absurd (1isNotPrime $ replace
                                                             (aDiv1=>a=1 prime ((b - c) , (sym $ trans 1=ab-ac (a*c-a*b=a*c-b prime c b))))
                                                             (λ x -> isPrime x)
                                                             (fst evidence)))
                             (λ n≤p -> (prime , (n≤p , fst evidence)))
