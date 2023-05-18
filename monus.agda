

-- Falsity
data ⊥ : Set where

absurd : {A : Set} → ⊥ → A
absurd ()

-- Products
data _×_ (A B : Set) : Set where
 _,_ : A → B → A × B

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
x - 0 = x
0 - (suc y) = 0
(suc x) - (suc y) = x - y

_*_ : Nat → Nat → Nat
zero  * m = zero
suc n * m = (n * m) + m
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





+0= : (b : Nat) → b ≡ (b + 0)
+0= 0       = refl 
+0= (suc b) = cong suc (+0= b)



+1= : (b : Nat) → suc b ≡ (b + 1)
+1= 0       = refl 
+1= (suc b) = sym (
  begin
    suc b + 1
  =⟨⟩
    suc (b + 1)
  =⟨ cong suc (sym (+1= b))⟩
    suc (suc b)
  end )


suc+=+suc : (a b : Nat)  → suc (a + b) ≡ a + suc b
suc+=+suc 0 b       = refl 
suc+=+suc (suc a) b = cong suc (suc+=+suc a b)

comm+ : (a b : Nat) → (a + b) ≡ (b + a)
comm+ 0 b =  -- ????
  begin
    0 + b
  =⟨⟩
    b
  =⟨ +0= b ⟩
    b + 0
  end
comm+ (suc a) b =
  begin
    (suc a) + b
  =⟨⟩
    suc (a + b)
  =⟨ cong suc (comm+ a b) ⟩
    suc (b + a)
  =⟨ suc+=+suc b a ⟩
    b + (suc a)
  end


assoc+ : (a b c : Nat) -> (a + (b + c)) ≡ ((a + b) + c)
assoc+ a 0 c =
  begin
    a + (0 + c)
  =⟨⟩
    a + c
  =⟨ cong (λ x → (x + c)) (+0= a)⟩
    (a + 0) + c
  end
assoc+ a (suc b) c =
  begin
    a + (suc b + c)
  =⟨⟩
    a + suc (b + c)
  =⟨ sym ( suc+=+suc a (b + c)) ⟩
    suc (a + (b + c))
  =⟨ cong suc  (assoc+ a b c) ⟩
    suc ((a + b) + c)
  =⟨⟩
    suc (a + b) + c
  =⟨ cong (λ x → (x + c)) (suc+=+suc a b) ⟩
    (a + suc b) + c
  end
    
assoc-flip : (a b c : Nat) -> (a + (b + c)) ≡ (b + (a + c))
assoc-flip a b c =
  (trans (assoc+ a b c)
    (trans (cong (λ x → (x + c)) (comm+ a b))
      (sym (assoc+ b a c))))
      
*0=0 : (a : Nat) → 0 ≡ (a * 0)
*0=0 0 = refl
*0=0 (suc a) = sym
  (begin
    (suc a) * 0
  =⟨⟩ 
    (a * 0) + 0
  =⟨ sym (+0= (a * 0)) ⟩
    a * 0
  =⟨ sym (*0=0 a) ⟩
    0
  end)

*1=1 : (a : Nat) → a ≡ (a * 1)
*1=1 0 = refl
*1=1 (suc a) = sym
  (begin
    (suc a) * 1
  =⟨⟩
    (a * 1) + 1
  =⟨ sym (+1= (a * 1)) ⟩
   suc (a * 1) 
  =⟨ cong suc (sym (*1=1 a)) ⟩
    suc a
  end)

suc-help : (a b : Nat) → b + (a * b) ≡ (suc a) * b
suc-help a b = sym
  (begin
    (suc a) * b
  =⟨⟩
    (a * b) + b
  =⟨ comm+ (a * b) b ⟩ 
    b + (a * b)
  end)

suc-rev : (a b : Nat) → suc ( a + b) ≡ (suc a) + b
suc-rev a b = sym (
  begin
    (suc a) + b
  =⟨⟩
    suc ( a + b)
  end )
 

*suc=+* : ( a b : Nat) → a + (a * b) ≡ a * (suc b)
*suc=+* 0  b      = refl
*suc=+* (suc a) b = sym (
  begin
    suc a * suc b
  =⟨⟩
    (a * suc b) + (suc b)
  =⟨ comm+ (a * suc b) (suc b) ⟩
    suc b + (a * suc b)
  =⟨⟩
    suc (b + (a * suc b))
  =⟨ cong (λ x → suc (b + x)) (sym (*suc=+* a b)) ⟩
    suc (b + (a + (a * b)))
  =⟨ cong suc (assoc-flip b a (a * b)) ⟩
    suc (a + (b + (a * b)))
  =⟨ suc-rev a (b + (a * b)) ⟩
    suc a + (b + (a * b))
  =⟨ cong (λ x → (suc a + x)) (suc-help a b) ⟩
    suc a + (suc a * b)
  end ) 


comm* : ( a b : Nat) → a * b ≡ b * a
comm* 0 b = 
  begin
    0 * b
  =⟨⟩
    0
  =⟨ *0=0 b ⟩
    b * 0
  end
comm* (suc a) b =
  begin
    (suc a) * b
  =⟨⟩
    (a * b) + b
  =⟨ cong (λ (x) → (x + b)) (comm* a b) ⟩
    (b * a) + b
  =⟨ comm+ (b * a) b ⟩
    b + (b * a)
  =⟨ *suc=+* b a ⟩
    b * (suc a)
  end

c-c=0 : (c : Nat) -> (c - c) ≡ 0
c-c=0 0 = refl
c-c=0 (suc c) = 
  begin
    (suc c - (suc c))
  =⟨⟩
    (c - c)
  =⟨ (c-c=0 c) ⟩
    0
  end

-- wtf.. 
a+c-c=a : (a c :  Nat) -> ((a + c) - c) ≡ a
a+c-c=a a 0 = 
  begin
    (a + 0) - 0
  =⟨ cong (λ x -> x - 0) (sym (+0= a)) ⟩
    a - 0
  =⟨⟩
    a 
  end
a+c-c=a a (suc c) =
  begin
    (a + suc c) - (suc c)
  =⟨ cong (λ x → x - (suc c)) (comm+ a (suc c)) ⟩
    (suc c + a) - (suc c)
  =⟨⟩
    suc (c + a) - (suc c)
  =⟨ cong (λ x → suc x - (suc c)) (comm+ c a)  ⟩
    suc (a + c) - (suc c)
  =⟨⟩
    (a + c) - c
  =⟨ a+c-c=a a c ⟩
    a
  end
    
-- WTF
-0=0 : (a : Nat) -> 0 ≡ (0 - a)
-0=0 0 = refl
-0=0 (suc a) = refl 

neg-distr : (a b c : Nat) -> a - (b + c) ≡  ((a - b) - c)
neg-distr 0 0 c = refl
neg-distr (suc a) 0 c = refl
neg-distr 0 (suc b) c =
  begin
    zero - (suc b + c)
  =⟨⟩
    zero - suc (b + c)
  =⟨⟩
    zero
  =⟨ -0=0 c ⟩
    0 - c
  =⟨ cong (λ x -> x - c) (-0=0 (suc b)) ⟩
    (0 - suc b) - c
  end
neg-distr (suc a) (suc b) c =
  begin
    suc a - (suc b + c)
  =⟨⟩
    (suc a) - (suc (b + c))
  =⟨⟩
    a - (b + c)
  =⟨ neg-distr a b c ⟩
    (a - b) - c 
  end



sca-sba : (a b c : Nat) -> (b + a) - (c + a) ≡ b - c
sca-sba a 0 0 = 
  begin
    (zero + a) - (zero + a)
  =⟨⟩
    a - a
  =⟨ c-c=0 a ⟩
    0
  end
sca-sba a (suc b) 0 =
  begin
    (suc b + a) - (zero + a)
  =⟨⟩
    (suc b + a) - a
  =⟨ a+c-c=a (suc b) a ⟩
    suc b
  end
sca-sba a 0 (suc c) =
  begin
    (0 + a) - (suc c + a)
  =⟨ cong (λ x -> (0 + a) - x) (comm+ (suc c) a) ⟩
    (0 + a) - (a + suc c)
  =⟨⟩
    a - (a + suc c)
  =⟨ neg-distr a a (suc c) ⟩
    (a - a) - (suc c)
  =⟨ cong (λ x -> x - (suc c)) (c-c=0 a) ⟩
    0 - (suc c)
  =⟨⟩
    0
  end
sca-sba a (suc b) (suc c) =
  begin
    (suc b + a) - (suc c + a)
  =⟨⟩
    suc (b + a) - suc (c + a)
  =⟨⟩
    (b + a) - (c + a)
  =⟨ sca-sba a b c ⟩
    (b - c)
  end

a*c-a*b=a*c-b : (a b c : Nat) -> (a * c) - (a * b) ≡  (a * (c - b))
a*c-a*b=a*c-b a 0 0 =
  begin
    (a * zero) - (a * zero)
  =⟨ c-c=0 (a * 0) ⟩
    0
  =⟨ *0=0 a ⟩
    a * 0
  end
a*c-a*b=a*c-b a (suc b) 0 =
  begin
    (a * 0) - (a * (suc b))
  =⟨ cong (λ x -> (x - (a * (suc b)))) (sym (*0=0 a)) ⟩
    0 - (a * (suc b)) 
  =⟨ sym (-0=0 (a * (suc b))) ⟩
    0
  =⟨ *0=0 a ⟩
    a * 0
  =⟨ cong (λ x -> a * x) (-0=0 (suc b)) ⟩
    a * (zero - suc b)
  end
a*c-a*b=a*c-b a 0 (suc c) =
  begin
    (a * suc c) - (a * zero)
  =⟨ cong (λ x -> (a * (suc c)) - x)  (sym (*0=0 a)) ⟩
    (a * (suc c)) - 0 
  =⟨⟩
    a * (suc c)
  end
a*c-a*b=a*c-b a (suc b) (suc c) =
 begin
    (a * suc c) - (a * suc b)
  =⟨ cong (λ x -> (a * suc c) - x) (comm* a (suc b)) ⟩
    (a * suc c) -  (suc b * a)
  =⟨ cong (λ x -> x - (suc b * a)) (comm* a (suc c)) ⟩
    (suc c * a) - (suc b * a)
  =⟨⟩
    ((c * a) + a) - ((b * a) + a)
  =⟨ sca-sba a (c * a) (b * a) ⟩
    (c * a) - (b * a)
  =⟨ cong (λ x -> (c * a) - x ) (comm* b a) ⟩
    (c * a) - (a * b)
  =⟨ cong (λ x -> x - (a * b) ) (comm* c a) ⟩
    (a * c) - (a * b)
  =⟨ a*c-a*b=a*c-b a b c ⟩
    a * (c - b)
  end
  
