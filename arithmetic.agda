{-# OPTIONS --allow-unsolved-metas #-}
module Arithmetic where

open import BuiltIn
open import List

+2 : Nat → Nat
+2 = suc ∘ suc

sub1 : Nat → Nat
sub1 0 = 0
sub1 (suc n) = n

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


+0= : (b : Nat) → b ≡ (b + 0)
+0= 0       = refl
+0= (suc b) = cong suc (+0= b)

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

*1= : (b : Nat) → b ≡ (b * 1)
*1= = *1=1

n*0=0 : (n : Nat) → (n * 0) ≡ 0
n*0=0  0       = refl
n*0=0  (suc n) = cong (λ x → x + 0) $ n*0=0 n

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
  =⟨ sym $ n*0=0 b ⟩
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
≤Product-help (suc a) (suc b) b!=0 = ≤Switch (1 + ((suc a) * (suc b)))
                                             (1 + ((suc a) * (suc b)))
                                             ((suc b) +  ((suc a) * (suc b)))
                                             (((suc a) * (suc b)) + (suc b))
                                             refl
                                             (comm+ (suc b)  ((suc a) * (suc b)))
                                             (≤+ 1 (suc b) ((suc a) * (suc b)) (s≤s 0 b (z≤n b)))

≤Product : (a b c : Nat) → (c ≡ 0 → ⊥) × (a ≡ b) → a ≤ (b * c)
≤Product a b 0 (c!=0 , a=b) = (absurd (c!=0 refl))
≤Product 0 0 c (c!=0 , a=b) = z≤n (0 * c)
≤Product (suc a) (suc b) c (c!=0 , sa=sb) =
  (≤Trans
    (suc a) (suc (b * c)) ((suc b) * c) -- a, b, c
    (a≤b->sa≤sb a (b * c) (≤Product a b c (c!=0 , (sa=sb->a=b a b sa=sb)))) -- a ≤ b
    (≤Product-help b c c!=0)) -- b ≤ c


rangeUpTo : Nat -> Nat -> List Nat
rangeUpTo m zero = []
rangeUpTo m (suc num) = (m + (suc num)) :: rangeUpTo m num

x-0=x : (x : Nat) -> x - 0 ≡ x
x-0=x  zero = refl
x-0=x (suc x) = refl

aInRangeBHelp4 : (n : Nat) ->  suc (suc n) :: concat (rangeUpTo 1 n) (1 :: 0 :: []) ≡  concat (rangeUpTo 2 (n - zero)) (2 :: 1 :: 0 :: [])
aInRangeBHelp4 zero = refl
aInRangeBHelp4 (suc n) =
  begin
     suc (suc (suc n)) :: concat (rangeUpTo 1 (suc n)) (1 :: 0 :: [])
  =⟨⟩
     suc (suc (suc n)) :: concat ((1 + (suc n)) :: (rangeUpTo 1 n)) (1 :: 0 :: [])
  =⟨⟩
     suc (suc (suc n)) :: concat ((suc (suc n)) :: (rangeUpTo 1 n)) (1 :: 0 :: [])
  =⟨⟩
     suc (suc (suc n)) :: (suc (suc n)) :: concat ((rangeUpTo 1 n)) (1 :: 0 :: [])
  =⟨ cong (suc (suc (suc n)) ::_) (aInRangeBHelp4 n)⟩
     suc (suc (suc n)) :: concat (rangeUpTo 2 (n - zero)) (2 :: 1 :: 0 :: [])
  =⟨ cong (λ x ->  suc (suc (suc n)) :: concat (rangeUpTo 2 x) (2 :: 1 :: 0 :: [])) (x-0=x n) ⟩
     suc (suc (suc n)) :: concat (rangeUpTo 2 n) (2 :: 1 :: 0 :: [])
  =⟨⟩
    refl 

aInRangeBHelp3 : (m n : Nat) -> m ≤ n -> suc (suc n) :: concat (rangeUpTo (suc m) (n - m)) (suc m :: range m)  ≡ concat (rangeUpTo (suc (suc m)) (n - m)) (suc (suc m) :: suc m :: range m)
aInRangeBHelp3 .zero n (z≤n .n) =
 begin
    suc (suc n) :: concat (rangeUpTo (suc zero) (n - zero)) (suc zero :: range zero)
  =⟨⟩
    suc (suc n) :: concat (rangeUpTo 1 (n - zero)) (1 :: 0 :: [])
  =⟨ cong (λ x -> suc (suc n) :: concat (rangeUpTo 1 x) (1 :: 0 :: [])) (x-0=x n) ⟩
    suc (suc n) :: concat (rangeUpTo 1 n) (1 :: 0 :: [])
  =⟨ aInRangeBHelp4 n ⟩
    concat (rangeUpTo 2 (n - zero)) (2 :: 1 :: 0 :: [])
  end
aInRangeBHelp3 .(suc m) .(suc n) (s≤s m n m≤n) = 
  begin
     suc (suc (suc n)) :: concat (rangeUpTo (suc (suc m)) (n -  m)) (suc (suc m) :: range (suc m))
  =⟨⟩
    {!!}

aInRangeBHelp2 : (m n : Nat) -> m ≤ n ->  suc n :: range n ≡  concat (rangeUpTo (suc m) (n - m)) (suc m :: range m)
aInRangeBHelp2 .zero zero (z≤n .zero) = refl
aInRangeBHelp2 .zero (suc n) (z≤n .(suc n)) =
 begin
    suc (suc n) :: range (suc n)
  =⟨⟩
    suc (suc n) :: suc n :: range n
  =⟨ cong (suc (suc n) ::_) (aInRangeBHelp2 zero n (z≤n n)) ⟩
    suc (suc n) :: concat (rangeUpTo (suc zero) (n - zero)) (suc zero :: range zero)
  =⟨⟩
    suc (suc n) :: concat (rangeUpTo 1 (n - zero)) (1 :: range zero)
  =⟨⟩
    suc (suc n) :: concat (rangeUpTo 1 (n - 0)) (1 :: 0 :: [])
  =⟨ cong (λ x -> suc (suc n) :: concat (rangeUpTo 1 x) (1 :: 0 :: [])) (x-0=x n) ⟩
    suc (suc n) :: concat (rangeUpTo 1 n) (1 :: 0 :: [])
  end
aInRangeBHelp2 .(suc m) .(suc n) (s≤s m n m≤n) =
  begin
     suc (suc n) :: range (suc n)
  =⟨⟩
    suc (suc n) :: suc n :: range n
  =⟨ cong (suc (suc n) ::_) (aInRangeBHelp2 m n m≤n) ⟩
   suc (suc n) :: concat (rangeUpTo (suc m) (n - m)) (suc m :: range m)
  =⟨ aInRangeBHelp3 m n m≤n ⟩
    concat (rangeUpTo (suc (suc m)) (n - m)) (suc (suc m) :: suc m :: range m)
  =⟨⟩
    refl

aInRangeBHelp1 : (b : Nat) -> range b ≡ concat (rangeUpTo 0 b) (zero :: [])
aInRangeBHelp1 zero = refl
aInRangeBHelp1 (suc b) =
  begin
    range (suc b)
  =⟨⟩
    suc b :: range b
  =⟨ cong (suc b ::_) (aInRangeBHelp1 b) ⟩
    suc b :: concat (rangeUpTo 0 b) (zero :: [])
  =⟨⟩
    0 + (suc b)  :: concat (rangeUpTo 0 b) (zero :: [])
  =⟨⟩
    refl

aInRangeB : (a b : Nat) → a ≤ b → isIn Nat a (range b)
aInRangeB .zero b (z≤n .b) = (rangeUpTo 0 b , ([] , aInRangeBHelp1 b))
aInRangeB .(suc m) .(suc n) (s≤s m n m≤n) = (rangeUpTo (suc m) ((suc n) - (suc m)), (range m , aInRangeBHelp2 m n m≤n))

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
  =⟨ sym $ n*0=0 a ⟩
    a * 0
  end
a*c-a*b=a*c-b a (suc b) 0 =
  begin
    (a * 0) - (a * (suc b))
  =⟨ cong (λ x -> (x - (a * (suc b)))) (n*0=0 a) ⟩
    0 - (a * (suc b))
  =⟨ sym (-0=0 (a * (suc b))) ⟩
    0
  =⟨ sym $ n*0=0 a ⟩
    a * 0
  =⟨ cong (λ x -> a * x) (-0=0 (suc b)) ⟩
    a * (zero - suc b)
  end
a*c-a*b=a*c-b a 0 (suc c) =
  begin
    (a * suc c) - (a * zero)
  =⟨ cong (λ x -> (a * (suc c)) - x)  (n*0=0 a) ⟩
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

distr+* : (a b c : Nat) → (a + b) * c ≡ (a * c) + (b * c)
distr+* 0 b c = refl
distr+* (suc a) b c = -- {! !}
  begin
    (suc a + b) * c
  =⟨⟩
    suc ( a + b) * c
  =⟨⟩
    (( a + b) * c) + c
  =⟨ cong (λ x → (x + c)) (distr+* a b c) ⟩
    ((a * c) + (b * c)) + c
  =⟨ comm+ ((a * c) + (b * c)) c ⟩
    c + ((a * c) + (b * c))
  =⟨ assoc+ c (a * c) (b * c)  ⟩
    (c + (a * c)) + (b * c)
  =⟨ cong (λ x → (x + (b * c))) (suc-help a c) ⟩
    ( suc a * c ) + (b * c)
  end

distr*+ : (a b c : Nat) → a * (b + c) ≡ (a * b) + (a * c)
distr*+ a b c =
  trans
    (comm* a (b + c))
    (trans
      (distr+* b c a)
      (trans
        (cong (λ x → (x + (c * a))) (comm* b a) )
        (cong (λ x → ((a * b) + x)) (comm* c a))))


assoc* : (a b c : Nat) → a * (b * c) ≡ (a * b) * c
assoc* 0 b c = refl
assoc* (suc a) b c = 
  begin
    suc a * (b * c)
  =⟨⟩
    (a * (b * c)) + (b * c)
  =⟨ cong (λ x → x + (b * c)) (assoc* a b c) ⟩
    ((a * b) * c) + (b * c)
  =⟨ sym ( distr+*  (a * b) b c ) ⟩
    ((a * b) + b) * c
  =⟨ cong (λ x → x * c) (comm+ (a * b) b) ⟩
    (b + (a * b)) * c
  =⟨ cong (λ x → x * c) (suc-help a b) ⟩
    (suc a * b) * c
  end


a≤Sb&a!=Sb=>a≤b : (a b : Nat) -> a ≤ (suc b) -> (a ≡ (suc b) -> ⊥) -> a ≤ b
a≤Sb&a!=Sb=>a≤b a b a≤Sb a!=Sb = {!!}
