id : {E : Set} ->  E -> E
id x = x

const : {A B : Set} -> A -> B -> A  
const x _ = x

_$_ : {A B : Set} -> (A -> B) -> A -> B
a $ b = a b

_∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
f ∘ g = (λ x -> f (g x))

data Σ (A : Set) (B : A -> Set) : Set where
  _,_ : (x : A) -> B x -> Σ A B

car : {A : Set} {B : A -> Set}  -> Σ A B -> A
car (a , b) = a

cdr : {A : Set} {B : A -> Set} -> (a : Σ A B) -> (B (car a))
cdr (a , b) = b

data _≡_ {A : Set} : A -> A -> Set where
  refl : {x : A} -> x ≡ x

cong : {A B : Set} {x y : A} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

data ⊥ : Set where

absurd : {A : Set} -> ⊥ -> A
absurd ()

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat ->  Nat ->  Nat
zero + y = y
(suc x) + y = suc (x + y)

_*_ : Nat -> Nat -> Nat
zero * y = 0
(suc x) * y = y + (x * y)


--FIX THIS
data _≤_ : Nat -> Nat -> Set where
  less : (n : Nat) -> (m : Nat) -> (Σ (Nat) (λ i -> ((i + n) ≡ m))) -> n ≤ m


data BinaryTree (A : Set) : Set where
  leaf : A -> BinaryTree A
  node : BinaryTree A -> BinaryTree A -> A -> BinaryTree A

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B 

data Maybe (A : Set) : Set where
  maybe : A -> Maybe A
  just : Maybe A

maybeMap : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B
maybeMap f (maybe a) = maybe (f a)
maybeMap _ just = just

data List (A : Set) : Set where
  nil : List A 
  ::  : A -> List A -> List A

concat : {E : Set} -> List E -> List E -> List E
concat (:: el l) l2 = :: el (concat l l2) 
concat nil = id

range : Nat -> List Nat
range (suc n) = (:: (suc n) (range n))
range 0 = nil


listMap : {A B : Set} -> (A -> B) -> List A -> List B
listMap f (:: l ls) = (:: (f l) (listMap f ls))
listMap _ _ = nil

isIn : (E : Set) -> (e : E) -> (l : List E) -> Set
isIn E e l = Σ (List E) (λ fr -> Σ (List E) (λ bk -> (l ≡ (concat fr (:: e bk)))))

divides : Nat -> Nat -> Set
divides a b = Σ Nat (λ n -> (n * a) ≡ b)



only≤Divides : (a b : Nat) -> (((a ≡ b -> ⊥) -> (b ≤ a -> ⊥)) -> ⊥) -> (divides a b) -> ⊥
only≤Divides a b f a|b = f (λ nota=b -> {!!})

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

