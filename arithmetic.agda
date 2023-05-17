{-# OPTIONS --allow-unsolved-metas #-}
module Arithmetic where

open import BuiltIn
open import List

+2 : Nat → Nat
+2 = suc ∘ suc

sub1 : Nat → Nat
sub1 0 = 0
sub1 (suc n) = n

+0= : (b : Nat) → b ≡ (b + 0)
+0= 0       = refl
+0= (suc b) = cong suc (+0= b)

*1= : (b : Nat) → b ≡ (b * 1)
*1= 0       = refl
*1= (suc b) = cong suc (*1= b)

n*0=0 : (n : Nat) → (n * 0) ≡ 0
n*0=0  0       = refl
n*0=0  (suc n) = cong (λ x → 0 + x) $ n*0=0 n

suc+=+suc : (a b : Nat) → suc (a + b) ≡ (a + (suc b))
suc+=+suc 0       b = refl 
suc+=+suc (suc a) b = cong suc (suc+=+suc a b)

comm+ : (a b : Nat) → (a + b) ≡ (b + a)
comm+ 0         = +0= 
comm+ (suc a) b = trans (cong suc $ comm+ a b) $ suc+=+suc b a

dist+ : (a b c : Nat) -> (a + (b + c)) ≡ ((a + b) + c)
dist+ 0 b c = refl
dist+ (suc a) b c = 
  begin
    (suc a + (b + c))
  =⟨⟩
    (suc (a + (b + c)))
  =⟨ cong suc (dist+ a b c) ⟩
    (suc ((a + b) + c))
  =⟨⟩
    refl

*+=*suc : (a b : Nat) -> (a + (a * b)) ≡ (a * (suc b))
*+=*suc 0 b = refl
*+=*suc (suc a) b = 
  begin
    suc a + (suc a * b)
  =⟨⟩
    suc a + (b + (a * b))
  =⟨ (dist+ (suc a)  b (a * b)) ⟩
    ((suc a + b) + (a * b))
  =⟨ (cong (λ x -> x + (a * b)) (comm+ (suc a) b)) ⟩
    ((b + suc a) + (a * b))
  =⟨ (cong (λ x -> x + (a * b)) (sym (suc+=+suc b a))) ⟩
    (suc (b + a) + (a * b))
  =⟨ (cong (λ x -> (suc x) + (a * b)) (comm+ b a)) ⟩
    (suc (a + b) + (a * b))
  =⟨ (cong (λ x -> x + (a * b)) (suc+=+suc a b)) ⟩
    ((a + suc b) + (a * b))
  =⟨ (cong (λ x -> x + (a * b)) (comm+ a (suc b))) ⟩
    (((suc b) + a) + (a * b))
  =⟨ (sym (dist+ (suc b) a (a * b))) ⟩
    (suc b + (a + (a * b)))
  =⟨ (cong (λ x -> (suc b) + x) (*+=*suc a b)) ⟩
    (suc b + (a * suc b))
  =⟨⟩
    ((suc a) * (suc b))
  =⟨⟩
    refl

comm* : (a b : Nat) → (a * b) ≡ (b * a)
comm* 0 b = 
  begin
    0 * b
  =⟨⟩
    0
  =⟨ sym (n*0=0 b) ⟩
    (b * 0)
  =⟨⟩
    refl
comm* (suc a) b = 
  begin
    suc a * b
  =⟨⟩
    (b + (a * b))
  =⟨ cong (λ x -> b + x) (comm* a b) ⟩
    (b + (b * a))
  =⟨ *+=*suc b a ⟩
    b * suc a
  =⟨⟩
    refl

AllDivide0 : (a : Nat) → a div 0
AllDivide0 a = 0 , n*0=0 a

only0Divides0 : (a : Nat) → 0 div a → a ≡ 0
only0Divides0 a 0|a = sym (cdr 0|a)

eqAlso≤ : (a b c : Nat) → (a ≤ b) × (b ≡ c) → a ≤ c
eqAlso≤ a b c (a≤b , b=c) = replace b=c (λ x → a ≤ x) a≤b

times0is0 : (a c : Nat) → c ≡ 0 → a * c ≡ 0
times0is0 a c c=0 = trans (cong (λ x -> a * x) c=0) $ n*0=0 a


≤and≥then= : (a b : Nat) → (a ≤ b) × (b ≤ a) → a ≡ b
≤and≥then= 0 0 _ = refl
≤and≥then= 0 (suc b) (0≤Sb , Sb≤0) = absurd $ 0!=Sn (b + k) (sym Sb+k=0)
  where
    diff = difference Sb≤0
    k = car diff
    Sb+k=0 = cdr diff
≤and≥then= (suc a) 0 (Sa≤0 , 0≤Sa) = sym $ ≤and≥then= 0 (suc a) (0≤Sa , Sa≤0)
≤and≥then= (suc a) (suc b) (s≤s a b a≤b , s≤s b a b≤a) = cong suc $ ≤and≥then= a b (a≤b , b≤a)

sa=sb->a=b : (a b : Nat) -> (suc a) ≡ (suc b) -> a ≡ b
sa=sb->a=b a b sa=sb = cong sub1 sa=sb

a≤b->sa≤sb : (a b : Nat) -> a ≤ b -> (suc a) ≤ (suc b)
a≤b->sa≤sb zero b (z≤n b) = s≤s 0 b (z≤n b)
a≤b->sa≤sb (suc m) (suc n) (s≤s m n a≤b) = s≤s (suc m) (suc n) (s≤s m n a≤b)

≤Trans : (a b c : Nat) -> a ≤ b -> b ≤ c -> a ≤ c
≤Trans zero b c (z≤n b) b≤c = z≤n c
≤Trans (suc m) (suc n) (suc c) (s≤s m n m≤n) (s≤s n c n≤c) = s≤s m c (≤Trans m n c m≤n n≤c)

≤Switch : (a b c d : Nat) -> a ≡ b -> c ≡ d -> a ≤ c -> b ≤ d
≤Switch a b c d a=b c=d a≤c = 
  replace c=d
    (λ x -> b ≤ x)
    (replace a=b
      (λ x -> x ≤ c)
      a≤c)

≤+ : (a b c : Nat) -> a ≤ b -> (a + c) ≤ (b + c)
≤+ a b 0 a≤b = 
  ≤Switch
    a (a + 0) b (b + 0)
    (+0= a)
    (+0= b)
    a≤b
≤+ a b (suc c) a≤b = 
  ≤Switch
    (suc (a + c)) (a + (suc c)) (suc (b + c)) (b + (suc c))
    (suc+=+suc a c)
    (suc+=+suc b c)
    (s≤s (a + c) (b + c) (≤+ a b c a≤b))

≤Product-help : (a b : Nat) -> (b ≡ 0 -> ⊥) -> suc (a * b) ≤ (suc a * b)
≤Product-help a 0 b!=0 = (absurd (b!=0 refl))
≤Product-help 0 (suc b) b!=0 =
  ≤Trans
    (suc (zero * (suc b))) 1 (1 * (suc b)) -- a, b, c
    (s≤s 0 0 (z≤n 0)) -- a ≤ b
    (s≤s 0 (1 * b) (z≤n (1 * b))) -- b ≤ c
≤Product-help (suc a) (suc b) b!=0 = ≤+ 1 (suc b) ((suc a) * (suc b))  (s≤s 0 b (z≤n b))

≤Product : (a b c : Nat) → (c ≡ 0 → ⊥) × (a ≡ b) → a ≤ (b * c)
≤Product a b 0 (c!=0 , a=b) = (absurd (c!=0 refl))
≤Product 0 0 c (c!=0 , a=b) = z≤n (0 * c)
≤Product (suc a) (suc b) c (c!=0 , sa=sb) =
  (≤Trans
    (suc a) (suc (b * c)) ((suc b) * c) -- a, b, c
    (a≤b->sa≤sb a (b * c) (≤Product a b c (c!=0 , (sa=sb->a=b a b sa=sb)))) -- a ≤ b
    (≤Product-help b c c!=0)) -- b ≤ c


aInRangeB : (a b : Nat) → a ≤ b → isIn Nat a (range b)
aInRangeB a b a≤b = {!!}

only≤Divides : (a b : Nat) → (b ≡ 0 → ⊥) → (a ≡ b → ⊥) × (b ≤ a) → a div b → ⊥
only≤Divides a b b!=0 (a!=b , b≤a) a|b = a!=b $ ≤and≥then= a b (a≤b , b≤a)
  where
    k = car a|b
    ak=b = cdr a|b
    k!=0 = λ k=0 → b!=0 $ trans (sym ak=b) (trans (cong (a *_) k=0) (n*0=0 a))
    a≤ak = ≤Product a a k (k!=0 , refl)
    a≤b = eqAlso≤ a (a * k) b (a≤ak , ak=b)

≤Dec : (a b : Nat) → Either (a ≤ b) (b ≤ a)
≤Dec 0       b       = left (z≤n b)
≤Dec a       0       = right (z≤n a)
≤Dec (suc a) (suc b) = cases (≤Dec a b) (left ∘ s≤s a b) (right ∘ s≤s b a)

divTrans : (a b c : Nat) -> (a div b) -> (b div c) -> (a div c)
divTrans = {!!}

aDiv1=>a=1 :(a : Nat) -> (a div 1) -> (a ≡ 1)
aDiv1=>a=1 a = {!!}

a+c-c=a : (a c : Nat) -> ((a + c) - c) ≡ a
a+c-c=a a c = {!!}

a*c-a*b=a*c-b : (a b c : Nat) -> (a * c) - (a * b) ≡  (a * (c - b))
a*c-a*b=a*c-b a b c = {!!}
