module BuiltIn where

-- Falsity
data ⊥ : Set where

absurd : {A : Set} → ⊥ → A
absurd ()

-- Products
data _×_ (A B : Set) : Set where
 _,_ : A → B → A × B
 
infixr 4 _,_

fst : {A B : Set} → A × B → A
fst  (a , b) = a

snd : {A B : Set} → A × B → B
snd (a , b) = b

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

car : {A : Set} {B : A → Set} → Σ A B → A
car (a , b) = a

cdr : {A : Set} {B : A → Set} → (a : Σ A B) → B (car a)
cdr (a , b) = b

-- Equivalence
data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x
infixr 4 _≡_

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

replace : {A : Set} {a b : A} → a ≡ b → (f : A -> Set) → f a → f b
replace refl f fa = fa

begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
begin p = p

_end : {A : Set} → (x : A) → x ≡ x
x end = refl

_=⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
x =⟨ p ⟩ q = trans p q

_=⟨⟩_ : {A : Set} → (x : A) → {y : A} → x ≡ y → x ≡ y
x =⟨⟩ q = x =⟨ refl ⟩ q

infix 1 begin_
infix 3 _end
infixr 2 _=⟨_⟩_
infixr 2 _=⟨⟩_

-- Naturals
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
zero    + y = y
(suc x) + y = suc (x + y)

_-_ : Nat → Nat → Nat
0 - y = y
x - 0 = x
(suc x) - (suc y) = x - y

_*_ : Nat → Nat → Nat
zero    * y = 0
(suc x) * y = y + (x * y)
infixr 5 _*_

data _≤_ : Nat → Nat → Set where
  z≤n : (n : Nat) → zero ≤ n 
  s≤s : (m n : Nat) → m ≤ n → (suc m) ≤ (suc n)
  
+Id : (x y : Nat) → suc (x + y) ≡ (suc x) + y
+Id x y = sym (
  begin
    (suc x) + y
  =⟨⟩
    suc (x + y)
  end)

difference : {a b : Nat} → a ≤ b → Σ Nat (λ k → a + k ≡ b)
difference (z≤n n) = n , refl
difference (s≤s m n pred≤) = k , eqProof
 where
   predDiff = difference pred≤
   k = car predDiff
   eqProof =
     begin
       (suc m + k)
     =⟨ +Id m k ⟩
       (suc m) + k
     =⟨ cong suc (cdr predDiff) ⟩
       suc n
     end

_div_ : Nat → Nat → Set
a div b = (Σ Nat (λ n → (a * n) ≡ b))

0!=Sn : (n : Nat) → 0 ≡ suc n → ⊥
0!=Sn n ()

Sn!=0 : (n : Nat) → suc n ≡ 0 → ⊥
Sn!=0 n ()

-- Either
data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

cases : {A B C : Set} → Either A B → (A → C) → (B → C) → C
cases (left a)  f _ = f a
cases (right b) _ g = g b

-- Maybe
data Maybe (A : Set) : Set where
  just     : A → Maybe A
  nothing  : Maybe A

indMaybe : {A B : Set} → (A → B) → Maybe A → Maybe B
indMaybe f (just a) = just (f a)
indMaybe _ nothing  = nothing

-- Fin
data Fin (A : Nat → Set): Nat → Set where
  end  : Fin A 0
  body : {n : Nat} → A n → Fin A n → Fin A (suc n)

finMap : {A B : Nat → Set} {n : Nat} → ({m : Nat} → A m → B m) → Fin A n → Fin B n
finMap f (body An finN-1) = body (f An) (finMap f finN-1)
finMap f end = end

-- Decideablity

dec= : (A : Set) -> Set
dec= A = (a b : A) -> Either (a ≡  b) (a ≡ b -> ⊥)

-- Miscellaneous
id : {A : Set} → A → A
id x = x

const : {A B : Set} → A → B → A
const x _ = x

_$_ : {A B : Set} → (A → B) → A → B
a $ b = a b

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)
infixr 8 _∘_
