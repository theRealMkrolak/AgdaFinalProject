{-# OPTIONS --allow-unsolved-metas #-}
module Arithmetic where


open import BuiltIn
open import List

+2 : Nat -> Nat
+2 = suc ∘ suc 

sub1 : Nat -> Nat
sub1 0 = 0
sub1 (suc n) = n

+0= : (b : Nat) → b ≡ (b + 0)
+0= 0       = refl 
+0= (suc b) = cong suc (+0= b)

*1= : (b : Nat) -> b ≡ (b * 1)
*1= 0 = refl
*1= (suc b) = cong suc (*1= b)

n*0=0 : (n  : Nat) -> ((n * 0) ≡ 0)
n*0=0  0 = refl
n*0=0  (suc n) = cong (λ x -> 0 + x) $ n*0=0 n

suc+=+suc : (a b : Nat) → (suc (a + b)) ≡ (a + (suc b))
suc+=+suc 0 b       = refl 
suc+=+suc (suc a) b = cong suc (suc+=+suc a b)

comm+ : (a b : Nat) → (a + b) ≡ (b + a)
comm+ 0  = +0= 
comm+ (suc a) b = trans (cong suc $ comm+ a b) $ suc+=+suc b a

0!=Sn : (n : Nat) -> (0 ≡ (suc n) -> ⊥)
0!=Sn n ()

comm* : (a b : Nat) → (a * b) ≡ (b * a)
comm* = {!!}

0DividesAll : (a : Nat) -> (divides a 0)
0DividesAll a = (0 , n*0=0 a)

only0Divides0 : (a : Nat) -> (divides 0 a) -> (a ≡ 0)
only0Divides0 0|a = {!!}

a≤b&b=c=>a≤c : (a b c : Nat) -> ((a ≤ b) × (b ≡ c)) -> a ≤ c
a≤b&b=c=>a≤c a b c (a≤b ^ b=c) = {!!}

c=0=>a*c=0 : (a c : Nat) -> (c ≡ 0) -> ((a * c) ≡ 0)
c=0=>a*c=0 a c c=0 = {!!}

a≤b&b≤a=>a=b : (a b : Nat) -> ((a ≤ b) × (b ≤ a)) -> (a ≡ b)
a≤b&b≤a=>a=b a b (a≤b ^ b≤a) = {!!}

c!=0&a=b=>a≤bc : (a b c : Nat) -> ((c ≡ 0 -> ⊥) × (a ≡ b)) -> (a ≤ (b * c))
c!=0&a=b=>a≤bc a b c (c!=0 ^ a=b) = {!!}

aInRangeB : (a b : Nat) -> a ≤ b -> (isIn Nat a (range b))
aInRangeB a b a≤b = {!!}

only≤Divides : (a b : Nat) -> (b ≡ 0 -> ⊥) -> ((a ≡ b -> ⊥) × (b ≤ a)) -> (divides a b) -> ⊥
only≤Divides a b b!=0 (aNeqb ^ b≤a) a|b = let
                                         c    = (car a|b)
                                         ac=b = (cdr a|b)
                                     in  aNeqb $ a≤b&b≤a=>a=b
                                                 a
                                                 b
                                                   (a≤b&b=c=>a≤c
                                                     a
                                                     (a * c)
                                                     b
                                                     (c!=0&a=b=>a≤bc
                                                       a
                                                       a
                                                       c
                                                       ((λ c=0 -> b!=0 $ trans (sym ac=b) (trans (cong (λ x -> a * x) c=0) (n*0=0 a))) ^ refl) ^ ac=b) ^ b≤a)

--works by showing that a=a => a≤ac because c!=0 then using that we show that because ac=b that a≤ac => a≤b thus because a≤b and b≤a we get a=b which gives us a contradictiona
--c!=0 is shown by assuming c and showing that b=0 which is false by def of division


≤EitherRefl : (a b : Nat) -> Either (a ≤ b) (b ≤ a)
≤EitherRefl = {!!}

